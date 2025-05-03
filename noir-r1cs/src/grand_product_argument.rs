use core::num;
use std::{fmt::Debug, os::macos::raw::stat};

use ark_poly::EvaluationDomain;
use spongefish::{codecs::arkworks_algebra::{FieldToUnitDeserialize, FieldToUnitSerialize, UnitToField}, ProverState};
use whir::{parameters::{default_max_pow, FoldType, FoldingFactor, SoundnessType}, poly_utils::{evals::EvaluationsList, multilinear::MultilinearPoint}, whir::{committer::{CommitmentReader, CommitmentWriter}, domainsep::WhirDomainSeparator, prover::Prover, statement::{Statement, StatementVerifier, VerifierWeights, Weights}, verifier::Verifier}};

use crate::{skyscraper::SkyscraperSponge, utils::{next_power_of_two, sumcheck::{calculate_eq, calculate_evaluations_over_boolean_hypercube_for_eq, eval_linear_poly, eval_qubic_poly, sumcheck_fold_map_reduce, SumcheckIOPattern}, HALF}, whir_r1cs::{IOPattern, MultivariateParameters, WhirConfig, WhirParameters, WhirProof}, FieldElement};

pub struct GrandProductArgument {
    pub arr: Vec<FieldElement>,
    pub whir_config: WhirConfig,
}

pub struct GrandProductArgumentProof {
    transcript: Vec<u8>,
    claimed_product: FieldElement,
    num_of_layers: usize,
    whir_proof: WhirProof,
}

impl GrandProductArgument {
    pub fn new(mut arr: Vec<FieldElement>) -> Self {
        arr.resize(arr.len().next_power_of_two(), FieldElement::from(1));
        let num_variables = next_power_of_two(arr.len());
        let mv_params = MultivariateParameters::new(num_variables);
        let whir_params = WhirParameters {
            initial_statement:     true,
            security_level:        128,
            pow_bits:              default_max_pow(num_variables, 1),
            folding_factor:        FoldingFactor::Constant(4),
            leaf_hash_params:      (),
            two_to_one_params:     (),
            soundness_type:        SoundnessType::ConjectureList,
            fold_optimisation:     FoldType::ProverHelps,
            _pow_parameters:       Default::default(),
            starting_log_inv_rate: 1,
        };
        let whir_config = WhirConfig::new(mv_params, whir_params);
        
        GrandProductArgument {
            whir_config, arr,
        }
    }

    pub fn prove(&self)  {
        let layers = calculate_binary_multiplication_tree(self.arr.clone());
        let io = create_io_pattern(layers.len(), &self.whir_config);
        let mut merlin = io.to_prover_state();

        let committer = CommitmentWriter::new(self.whir_config.clone());

        let poly = EvaluationsList::new(self.arr.clone());
        let polynomial = poly.to_coeffs();

        let witness = committer
            .commit(&mut merlin, polynomial)
            .expect("WHIR prover failed to commit");

        let mut saved_val_for_sumcheck_equality_assertion;
        let mut r;
        let mut line_evaluations;
        let mut alpha = Vec::<FieldElement>::new();

        (merlin, r, saved_val_for_sumcheck_equality_assertion) = add_line_to_merlin(merlin, layers[1].clone());

        for i in 2..layers.len() {
            alpha.push(r[0]);
            let mut eq_r = calculate_evaluations_over_boolean_hypercube_for_eq(&alpha);
            let (mut v0, mut v1) = split_by_index(layers[i].clone());
            let sumcheck_polynomial_mles = [eq_r, v0, v1];
            (merlin, line_evaluations, alpha) = run_sumcheck(merlin, sumcheck_polynomial_mles, saved_val_for_sumcheck_equality_assertion);
            (merlin, r, saved_val_for_sumcheck_equality_assertion) = add_line_to_merlin(merlin, line_evaluations.to_vec());
        }
        alpha.push(r[0]);

        let mut statement = Statement::<FieldElement>::new(next_power_of_two(self.arr.len()));
        let weight = Weights::evaluation(MultilinearPoint(alpha));
        statement.add_constraint(weight, saved_val_for_sumcheck_equality_assertion);

        let prover = Prover(self.whir_config.clone());
        let whir_proof = prover
            .prove(&mut merlin, statement, witness)
            .expect("WHIR prover failed to generate a proof");

        let transcript = merlin.narg_string().to_vec();
        let proof = GrandProductArgumentProof { 
            whir_proof,
            transcript,
            claimed_product: layers[0][0],
            num_of_layers: layers.len(),
        };
        self.verify(proof);
    }

    pub fn verify(&self, proof: GrandProductArgumentProof) {
        let io = create_io_pattern(proof.num_of_layers, &self.whir_config);
        let mut arthur = io.to_verifier_state(&proof.transcript);

        let mut l = [FieldElement::from(0); 2];
        let mut r = [FieldElement::from(0); 1];
        let mut h = [FieldElement::from(0); 4];
        let mut alpha = [FieldElement::from(0); 1];
        let mut last_sumcheck_value= proof.claimed_product;

        let mut prev_rand = Vec::<FieldElement>::new();
        let mut rand = Vec::<FieldElement>::new();

        let commitment_reader = CommitmentReader::new(&self.whir_config);
        let parsed_commitment = commitment_reader.parse_commitment(&mut arthur).unwrap();
        
        for i in 0..proof.num_of_layers-1 {
            for _ in 0..i {
                arthur.fill_next_scalars(&mut h)
                    .expect("Failed to fill next scalars");
                arthur.fill_challenge_scalars(&mut alpha)
                    .expect("Failed to fill next scalars");
                assert_eq!(eval_qubic_poly(&h, &FieldElement::from(0)) + eval_qubic_poly(&h, &FieldElement::from(1)), last_sumcheck_value);
                rand.push(alpha[0]);
                last_sumcheck_value = eval_qubic_poly(&h, &alpha[0]);
            }
            arthur.fill_next_scalars(&mut l)
                .expect("Failed to fill next scalars");
            arthur.fill_challenge_scalars(&mut r)
                .expect("Failed to fill next scalars");
            let claimed_last_sch = calculate_eq(&prev_rand, &rand) * eval_linear_poly(&l, &FieldElement::from(0)) * eval_linear_poly(&l, &FieldElement::from(1));
            assert_eq!(claimed_last_sch, last_sumcheck_value);
            rand.push(r[0]);
            prev_rand = rand;
            rand = Vec::<FieldElement>::new();
            last_sumcheck_value = eval_linear_poly(&l, &r[0]);
        }

        let weights = VerifierWeights::evaluation(MultilinearPoint(prev_rand));
        let mut statement_verifier = StatementVerifier::from_statement(&Statement::<FieldElement>::new(next_power_of_two(self.arr.len())));
        statement_verifier.add_constraint(weights, last_sumcheck_value);
            
        let verifier = Verifier::new(&self.whir_config);
        verifier.verify(&mut arthur, &parsed_commitment, &statement_verifier, &proof.whir_proof)
            .expect("WHIR verifier failed to verify the proof");
    }


}

pub fn run_sumcheck(
    mut merlin: ProverState<SkyscraperSponge, FieldElement>,
    mut mles: [Vec<FieldElement>; 3],
    mut saved_val_for_sumcheck_equality_assertion: FieldElement,
) -> (ProverState<SkyscraperSponge, FieldElement>, [FieldElement; 2], Vec<FieldElement>) {
    let mut alpha_i_wrapped_in_vector = [FieldElement::from(0)];
    let mut alpha = Vec::<FieldElement>::new();
    let mut fold = None;

    let mut m0 = mles[0].clone();
    let mut m1 = mles[1].clone();
    let mut m2 = mles[2].clone();
    

    loop {
        let [hhat_i_at_0, hhat_i_at_em1, hhat_i_at_inf_over_x_cube] =
            sumcheck_fold_map_reduce([&mut m0, &mut m1, &mut m2], fold, |[m0, m1, m2]| {
                [
                    // Evaluation at 0
                    m0.0 * m1.0 * m2.0,
                    // Evaluation at -1
                    (m0.0 + m0.0 - m0.1) * (m1.0 + m1.0 - m1.1) * (m2.0 + m2.0 - m2.1),
                    // Evaluation at infinity
                    (m0.1 - m0.0) * (m1.1 - m1.0) * (m2.1 - m2.0),
                ]
            });

        if fold.is_some() {
            m0.truncate(m0.len() / 2);
            m1.truncate(m1.len() / 2);
            m2.truncate(m2.len() / 2);
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
        alpha.push(alpha_i_wrapped_in_vector[0]);
        if m0.len() <= 2 {
            break;
        }
    }

    let folded_v0 = m1[0] + (m1[1] - m1[0]) * alpha_i_wrapped_in_vector[0];
    let folded_v1 = m2[0] + (m2[1] - m2[0]) * alpha_i_wrapped_in_vector[0];

    (merlin, [folded_v0, folded_v1], alpha) 
}

fn calculate_binary_multiplication_tree(array_to_prove: Vec<FieldElement>) -> Vec<Vec<FieldElement>> {
    let mut layers = vec![];
    let mut current_layer = array_to_prove;

    while current_layer.len() > 1 {
        let mut next_layer = vec![];

        for i in (0..current_layer.len()).step_by(2) {
            let product = current_layer[i] * current_layer[i + 1];
            next_layer.push(product);
        }

        layers.push(current_layer);
        current_layer = next_layer;
    }

    layers.push(current_layer);
    layers.reverse();
    layers
}

fn split_by_index(input: Vec<FieldElement>) -> (Vec<FieldElement>, Vec<FieldElement>) {
    let mut even_indexed = Vec::new();
    let mut odd_indexed = Vec::new();

    for (i, item) in input.into_iter().enumerate() {
        if i % 2 == 0 {
            even_indexed.push(item);
        } else {
            odd_indexed.push(item);
        }
    }

    (even_indexed, odd_indexed)
}

fn create_io_pattern(layer_count: usize, whir_config: &WhirConfig) -> IOPattern {
    let mut io: IOPattern = IOPattern::new("🌪️");

    io = io.commit_statement(whir_config);

    io = io
        .add_sumcheck_polynomials(2, 1);

    for i in 1..(layer_count-1) {
        io = io.add_sumcheck_polynomials(4, i);
        io = io.add_sumcheck_polynomials(2, 1);
    }
    
    io = io.add_whir_proof(whir_config);

    io
}

fn add_line_to_merlin(mut merlin: ProverState<SkyscraperSponge, FieldElement>, arr: Vec<FieldElement>) -> (ProverState<SkyscraperSponge, FieldElement>, [FieldElement; 1], FieldElement) {
    let l_evaluations = EvaluationsList::new(arr);
    let l_temp = l_evaluations.to_coeffs();
    let l: &[FieldElement] = l_temp.coeffs();
    merlin
        .add_scalars(&l)
        .expect("Failed to add l");

    let mut r = [FieldElement::from(0); 1];
    merlin.fill_challenge_scalars(&mut r)
        .expect("Failed to add a challenge scalar");

    let saved_val_for_sumcheck_equality_assertion = eval_linear_poly(&l, &r[0]);

    (merlin, r, saved_val_for_sumcheck_equality_assertion)
}