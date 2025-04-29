use spongefish::{codecs::arkworks_algebra::{FieldToUnitDeserialize, FieldToUnitSerialize, UnitToField}, ProverState};
use whir::poly_utils::evals::EvaluationsList;

use crate::{skyscraper::SkyscraperSponge, utils::{sumcheck::{calculate_eq, calculate_evaluations_over_boolean_hypercube_for_eq, eval_linear_poly, eval_qubic_poly, sumcheck_fold_map_reduce, SumcheckIOPattern}, HALF}, whir_r1cs::IOPattern, FieldElement};

pub struct GrandProductArgument {}

pub struct GrandProductArgumentProof {
    transcript: Vec<u8>,
}

impl GrandProductArgument {
    pub fn new() -> Self {
        GrandProductArgument {}
    }

    pub fn prove(&self)  {
        let io: IOPattern = IOPattern::new("🌪️")
        .add_sumcheck_polynomials(2, 1)
        .add_sumcheck_polynomials(4, 1)
        .add_sumcheck_polynomials(2, 1);

        let mut merlin = io.to_prover_state();

        let l_evaluations = EvaluationsList::new(vec![FieldElement::from(362880), FieldElement::from(980179200 as u64)]);
        let l_temp = l_evaluations.to_coeffs();
        let mut l: &[ark_ff::Fp<ark_ff::MontBackend<whir::crypto::fields::BN254Config, 4>, 4>] = l_temp.coeffs();
        
        merlin
        .add_scalars(&mut l)
        .expect("Failed to add l");

        let mut r = [FieldElement::from(0); 1];
        merlin.fill_challenge_scalars(&mut r)
        .expect("Failed to add a challenge scalar");

        let saved_val_for_sumcheck_equality_assertion = eval_linear_poly(&l, &r[0]);
        
        let mut eq_r = calculate_evaluations_over_boolean_hypercube_for_eq(&r);
        let mut v0 = vec![FieldElement::from(120), FieldElement::from(17160)];
        let mut v1 = vec![FieldElement::from(3024), FieldElement::from(57120)];
        
        let merlin = run_sumcheck(merlin, &mut v0, &mut v1, &mut eq_r, saved_val_for_sumcheck_equality_assertion);

        let transcript = merlin.narg_string().to_vec();
        let proof = GrandProductArgumentProof { transcript};
        self.verify(proof);
    }

    pub fn verify(&self, proof: GrandProductArgumentProof) {
        let io: IOPattern = IOPattern::new("🌪️")
        .add_sumcheck_polynomials(2, 1)
        .add_sumcheck_polynomials(4, 1)
        .add_sumcheck_polynomials(2, 1);

        let mut arthur = io.to_verifier_state(&proof.transcript);

        let mut l = [FieldElement::from(0); 2];
        arthur.fill_next_scalars(&mut l)
            .expect("Failed to fill next scalars");

        let mut r = [FieldElement::from(0); 1];
        arthur.fill_challenge_scalars(&mut r)
            .expect("Failed to fill next scalars");

        assert_eq!(eval_linear_poly(&l, &FieldElement::from(0)) * eval_linear_poly(&l, &FieldElement::from(1)), FieldElement::from(355687428096000 as u64));

        let mut h = [FieldElement::from(0); 4];
        arthur.fill_next_scalars(&mut h)
            .expect("Failed to fill next scalars");
        let mut alpha_verifier = [FieldElement::from(0); 1];
        arthur.fill_challenge_scalars(&mut alpha_verifier)
            .expect("Failed to fill next scalars");

        assert_eq!(eval_qubic_poly(&h, &FieldElement::from(0)) + eval_qubic_poly(&h, &FieldElement::from(1)), eval_linear_poly(&l, &r[0]));
        
        let mut left_side = calculate_eq(&r, &alpha_verifier);

        arthur.fill_next_scalars(&mut l)
            .expect("Failed to fill next scalars");
        arthur.fill_challenge_scalars(&mut r)
            .expect("Failed to fill next scalars");

        left_side = left_side * eval_linear_poly(&l, &FieldElement::from(0)) * eval_linear_poly(&l, &FieldElement::from(1));
        
        assert_eq!(left_side, eval_qubic_poly(&h, &alpha_verifier[0]));
    }
}

fn run_sumcheck(
    mut merlin: ProverState<SkyscraperSponge, FieldElement>,
    mut v0: &mut Vec<FieldElement>,
    mut v1: &mut Vec<FieldElement>,
    mut eq_r: &mut Vec<FieldElement>,
    mut saved_val_for_sumcheck_equality_assertion: FieldElement,
) -> ProverState<SkyscraperSponge, FieldElement> {
    let mut alpha_i_wrapped_in_vector = [FieldElement::from(0)];
    let mut fold = None;

    for _ in 0..1 {
        let [hhat_i_at_0, hhat_i_at_em1, hhat_i_at_inf_over_x_cube] =
            sumcheck_fold_map_reduce([&mut eq_r, &mut v0, &mut v1], fold, |[eq_r, v0, v1]| {
                [
                    // Evaluation at 0
                    eq_r.0 * v0.0 * v1.0,
                    // Evaluation at -1
                    (eq_r.0 + eq_r.0 - eq_r.1) * (v0.0 + v0.0 - v0.1) * (v1.0 + v1.0 - v1.1),
                    // Evaluation at infinity
                    (eq_r.1 - eq_r.0) * (v0.1 - v0.0) * (v1.1 - v1.0),
                ]
            });

        if fold.is_some() {
            eq_r.truncate(eq_r.len() / 2);
            v0.truncate(v0.len() / 2);
            v1.truncate(v1.len() / 2);
        }

        let mut hhat_i_coeffs = [FieldElement::from(0); 4];
        
        hhat_i_coeffs[0] = hhat_i_at_0;
        hhat_i_coeffs[2] = HALF
            * (saved_val_for_sumcheck_equality_assertion + hhat_i_at_em1
                - hhat_i_at_0
                - hhat_i_at_0
                - hhat_i_at_0);
        hhat_i_coeffs[3] = hhat_i_at_inf_over_x_cube;
        hhat_i_coeffs[1] = saved_val_for_sumcheck_equality_assertion
            - hhat_i_coeffs[0]
            - hhat_i_coeffs[0]
            - hhat_i_coeffs[3]
            - hhat_i_coeffs[2];

        assert_eq!(
            saved_val_for_sumcheck_equality_assertion,
            hhat_i_coeffs[0]
                + hhat_i_coeffs[0]
                + hhat_i_coeffs[1]
                + hhat_i_coeffs[2]
                + hhat_i_coeffs[3]
        );
        
        let _ = merlin.add_scalars(&hhat_i_coeffs[..]);
        let _ = merlin.fill_challenge_scalars(&mut alpha_i_wrapped_in_vector);
        fold = Some(alpha_i_wrapped_in_vector[0]);
        saved_val_for_sumcheck_equality_assertion = eval_qubic_poly(&hhat_i_coeffs, &alpha_i_wrapped_in_vector[0]);
    }

    let folded_v0 = v0[0] + (v0[1] - v0[0]) * alpha_i_wrapped_in_vector[0];
    let folded_v1 = v1[0] + (v1[1] - v1[0]) * alpha_i_wrapped_in_vector[0];

    let l_evaluations = EvaluationsList::new(vec![folded_v0, folded_v1]);
    let l_temp = l_evaluations.to_coeffs();
    let mut l = l_temp.coeffs();
    
    merlin
    .add_scalars(&mut l)
    .expect("Failed to add h");

    let mut r = [FieldElement::from(0); 1];
    merlin.fill_challenge_scalars(&mut r)
    .expect("Failed to add challenge scalar 1");

    merlin
}
