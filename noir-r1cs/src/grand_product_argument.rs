use spongefish::codecs::arkworks_algebra::{FieldToUnitDeserialize, FieldToUnitSerialize, UnitToField};
use whir::poly_utils::evals::EvaluationsList;

use crate::{utils::{sumcheck::{calculate_evaluations_over_boolean_hypercube_for_eq, eval_linear_poly, eval_qubic_poly, sumcheck_fold_map_reduce, SumcheckIOPattern}, HALF}, whir_r1cs::IOPattern, FieldElement};

pub struct GrandProductArgument {}

impl GrandProductArgument {
    pub fn new() -> Self {
        GrandProductArgument {}
    }

    pub fn prove(&self) {
        let io: IOPattern = IOPattern::new("🌪️")
        .add_sumcheck_polynomials(2, 1)
        .add_sumcheck_polynomials(4, 1);

        let mut merlin = io.to_prover_state();

        let h_evaluations = EvaluationsList::new(vec![FieldElement::from(362880), FieldElement::from(980179200 as u64)]);
        let h_temp = h_evaluations.to_coeffs();
        let mut h = h_temp.coeffs();
        
        merlin
        .add_scalars(&mut h)
        .expect("Failed to add q_1");

        let mut r = [FieldElement::from(0); 1];
        merlin.fill_challenge_scalars(&mut r)
        .expect("Failed to add challenge scalar 1");
        
        let mut saved_val_for_sumcheck_equality_assertion = eval_linear_poly(&h, &r[0]);

        let mut eq_r = calculate_evaluations_over_boolean_hypercube_for_eq(&r);
        let mut g0 = [FieldElement::from(120), FieldElement::from(1760)];
        let mut g1 = [FieldElement::from(3024), FieldElement::from(57120)];
        
        let mut alpha = Vec::<FieldElement>::with_capacity(1);
        let mut fold = None;


        for _ in 0..1 {
            let [hhat_i_at_0, hhat_i_at_em1, hhat_i_at_inf_over_x_cube] =
            sumcheck_fold_map_reduce([&mut eq_r, &mut g0, &mut g1], fold, |[eq_r, g0, g1]| {
                [
                    // Evaluation at 0
                    eq_r.0 * g0.0 * g1.0,
                    // Evaluation at -1
                    (eq_r.0 + eq_r.0 - eq_r.1) * (g0.0 + g0.0 - g0.1) * (g1.0 + g1.0 - g1.1),
                    // Evaluation at infinity
                    (eq_r.1 - eq_r.0) * (g0.1 - g0.0) * (g1.1 - g1.0),
                ]
            });

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
            let mut alpha_i_wrapped_in_vector = [FieldElement::from(0)];
            let _ = merlin.fill_challenge_scalars(&mut alpha_i_wrapped_in_vector);
            let alpha_i = alpha_i_wrapped_in_vector[0];
            alpha.push(alpha_i);
    
            fold = Some(alpha_i);
    
            saved_val_for_sumcheck_equality_assertion = eval_qubic_poly(&hhat_i_coeffs, &alpha_i);
        }




        let transcript = merlin.narg_string().to_vec();
        let mut arthur = io.to_verifier_state(&transcript);

        let mut h_verifier = [FieldElement::from(0); 2];
        arthur.fill_next_scalars(&mut h_verifier)
            .expect("Failed to fill next scalars");

        let mut r_verifier = [FieldElement::from(0); 1];
        arthur.fill_challenge_scalars(&mut r_verifier)
            .expect("Failed to fill next scalars");

        assert_eq!(eval_linear_poly(&h_verifier, &FieldElement::from(0)) * eval_linear_poly(&h_verifier, &FieldElement::from(1)), FieldElement::from(355687428096000 as u64));

        let mut sch_verifier = [FieldElement::from(0); 4];
        arthur.fill_next_scalars(&mut sch_verifier)
            .expect("Failed to fill next scalars");
        let mut alpha_verifier = [FieldElement::from(0); 1];
        arthur.fill_challenge_scalars(&mut alpha_verifier)
            .expect("Failed to fill next scalars");

        assert_eq!(eval_linear_poly(&h_verifier, &r_verifier[0]), eval_qubic_poly(&sch_verifier, &FieldElement::from(0)) + eval_qubic_poly(&sch_verifier, &FieldElement::from(1)));

    }
}
