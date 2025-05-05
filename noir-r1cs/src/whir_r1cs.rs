use {
    crate::{
        grand_product_argument::run_sumcheck, skyscraper::{SkyscraperMerkleConfig, SkyscraperPoW, SkyscraperSponge}, utils::{
            next_power_of_two, pad_to_power_of_two, serde_ark, serde_hex,
            sumcheck::{
                calculate_eq, calculate_evaluations_over_boolean_hypercube_for_eq,
                calculate_external_row_of_r1cs_matrices, calculate_witness_bounds, eval_qubic_poly,
                sumcheck_fold_map_reduce, SumcheckIOPattern,
            },
            HALF,
        }, FieldElement, R1CS
    }, anyhow::{ensure, Context, Result}, ark_std::{One, Zero}, core::num, serde::{Deserialize, Serialize}, spongefish::{
        codecs::arkworks_algebra::{FieldToUnitDeserialize, FieldToUnitSerialize, UnitToField},
        DomainSeparator, ProverState, VerifierState,
    }, std::fmt::{Debug, Formatter}, tracing::{info, instrument, warn}, whir::{
        parameters::{
            default_max_pow, FoldType, FoldingFactor,
            MultivariateParameters as GenericMultivariateParameters, SoundnessType,
            WhirParameters as GenericWhirParameters,
        },
        poly_utils::{evals::EvaluationsList, multilinear::MultilinearPoint},
        whir::{
            committer::{CommitmentReader, CommitmentWriter},
            domainsep::WhirDomainSeparator,
            parameters::WhirConfig as GenericWhirConfig,
            prover::Prover,
            statement::{
                Statement, StatementVerifier as GenericStatementVerifier, VerifierWeights, Weights,
            },
            verifier::Verifier,
            WhirProof as GenericWhirProof,
        },
    }
};

pub type MultivariateParameters = GenericMultivariateParameters<FieldElement>;
pub type WhirParameters = GenericWhirParameters<SkyscraperMerkleConfig, SkyscraperPoW>;
pub type WhirConfig = GenericWhirConfig<FieldElement, SkyscraperMerkleConfig, SkyscraperPoW>;
pub type WhirProof = GenericWhirProof<SkyscraperMerkleConfig, FieldElement>;
pub type IOPattern = DomainSeparator<SkyscraperSponge, FieldElement>;
pub type StatementVerifier = GenericStatementVerifier<FieldElement>;

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct WhirR1CSScheme {
    pub m:           usize,
    pub m_0:         usize,
    pub whir_config: WhirConfig,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct WhirR1CSProof {
    #[serde(with = "serde_hex")]
    pub transcript: Vec<u8>,

    pub whir_proof: WhirProof,

    pub proof_val:  WhirProof,

    pub proof_e_rx: WhirProof,

    pub proof_e_ry: WhirProof,

    pub num_terms: usize,

    // TODO: Derive from transcript
    #[serde(with = "serde_ark")]
    pub whir_query_answer_sums: [FieldElement; 3],

    #[serde(with = "serde_ark")]
    pub val: FieldElement,

    #[serde(with = "serde_ark")]
    pub e_rx: FieldElement,

    #[serde(with = "serde_ark")]
    pub e_ry: FieldElement,
}

struct DataFromSumcheckVerifier {
    r:                 Vec<FieldElement>,
    alpha:             Vec<FieldElement>,
    last_sumcheck_val: FieldElement,
}

impl WhirR1CSScheme {
    pub fn new_for_r1cs(r1cs: &R1CS) -> Self {
        Self::new_for_size(r1cs.witnesses, r1cs.constraints)
    }

    pub fn new_for_size(witnesses: usize, constraints: usize) -> Self {
        // m is equal to ceiling(log(number of variables in constraint system)). It is
        // equal to the log of the width of the matrices.
        let m = next_power_of_two(witnesses);

        // m_0 is equal to ceiling(log(number_of_constraints)). It is equal to the
        // number of variables in the multilinear polynomial we are running our sumcheck
        // on.
        let m_0 = next_power_of_two(constraints);

        // Whir parameters
        let mv_params = MultivariateParameters::new(m);
        let whir_params = WhirParameters {
            initial_statement:     true,
            security_level:        128,
            pow_bits:              default_max_pow(m, 1),
            folding_factor:        FoldingFactor::Constant(4),
            leaf_hash_params:      (),
            two_to_one_params:     (),
            soundness_type:        SoundnessType::ConjectureList,
            fold_optimisation:     FoldType::ProverHelps,
            _pow_parameters:       Default::default(),
            starting_log_inv_rate: 1,
        };
        let whir_config = WhirConfig::new(mv_params, whir_params);

        Self {
            m,
            m_0,
            whir_config,
        }
    }

    #[instrument(skip_all)]
    pub fn prove(&self, r1cs: &R1CS, witness: Vec<FieldElement>) -> Result<WhirR1CSProof> {
        ensure!(
            witness.len() == r1cs.witnesses,
            "Unexpected witness length for R1CS instance"
        );
        ensure!(
            r1cs.witnesses <= 1 << self.m,
            "R1CS witness length exceeds scheme capacity"
        );
        ensure!(
            r1cs.constraints <= 1 << self.m_0,
            "R1CS constraints exceed scheme capacity"
        );

        
        let num_terms = r1cs.a().iter().count();

        let whir_config_terms = generate_whir_config(num_terms);
        
        // Set up transcript
        let io: IOPattern = create_io_pattern(self.m_0, &self.whir_config, &whir_config_terms, num_terms);
        let merlin = io.to_prover_state();

        // First round of sumcheck to reduce R1CS to a batch weighted evaluation of the
        // witness
        let (merlin, alpha) = run_sumcheck_prover(r1cs, &witness, merlin, self.m_0);

        // Compute weights from R1CS instance
        let alphas = calculate_external_row_of_r1cs_matrices(&alpha, r1cs);

        // Compute WHIR weighted batch opening proof
        let (whir_proof, mut merlin, whir_query_answer_sums) =
            run_whir_pcs_prover(witness, &self.whir_config, merlin, self.m, alphas);

        let eq_rx = calculate_evaluations_over_boolean_hypercube_for_eq(&alpha);
        let eq_ry = calculate_evaluations_over_boolean_hypercube_for_eq(&whir_proof.randomness);
        let mut e_rx = Vec::<FieldElement>::new();
        let mut e_ry = Vec::<FieldElement>::new();

        // These can be computed once when the matrix is generated.
        let mut row_counters = vec![0;r1cs.constraints];
        let mut col_counters = vec![0;r1cs.witnesses];
        let mut read_ts_row = Vec::<FieldElement>::new();
        let mut read_ts_col = Vec::<FieldElement>::new();
        let mut matrix_row = Vec::<FieldElement>::new();
        let mut matrix_val = Vec::<FieldElement>::new();
        let mut matrix_col = Vec::<FieldElement>::new();

        r1cs.a().iter().for_each(|((i,j), val)|{
            read_ts_row.push(FieldElement::from(row_counters[i] as u64));
            read_ts_col.push(FieldElement::from(col_counters[j] as u64));
            row_counters[i] += 1;
            col_counters[j] += 1;
            e_rx.push(eq_rx[i]);
            e_ry.push(eq_ry[j]);
            matrix_row.push(FieldElement::from(i as u64));
            matrix_col.push(FieldElement::from(j as u64));
            matrix_val.push(val);
        });

        matrix_val = pad_to_power_of_two(matrix_val);
        e_rx = pad_to_power_of_two(e_rx);
        e_ry = pad_to_power_of_two(e_ry);

        let num_variables = next_power_of_two(matrix_val.len());
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

        let committer = CommitmentWriter::new(whir_config_terms.clone());

        let matrix_val_evals = EvaluationsList::new(matrix_val.clone());
        let matrix_val_coeffs = matrix_val_evals.to_coeffs();
        let witness_val = committer
            .commit(&mut merlin, matrix_val_coeffs)
            .expect("WHIR prover failed to commit");

        let matrix_e_rx_evals = EvaluationsList::new(e_rx.clone());
        let matrix_e_rx_coeffs = matrix_e_rx_evals.to_coeffs();
        let witness_e_rx = committer
            .commit(&mut merlin, matrix_e_rx_coeffs)
            .expect("WHIR prover failed to commit");

        let matrix_e_ry_evals = EvaluationsList::new(e_ry.clone());
        let matrix_e_ry_coeffs = matrix_e_ry_evals.to_coeffs();
        let witness_e_ry = committer
            .commit(&mut merlin, matrix_e_ry_coeffs)
            .expect("WHIR prover failed to commit");

        let sumcheck_polynomial_mles = [matrix_val.clone(), e_rx, e_ry];
        let (mut merlin, line_evaluations, alpha) = run_sumcheck(merlin, sumcheck_polynomial_mles, whir_proof.statement_values_at_random_point[0].clone());

        let mut statement_val = Statement::<FieldElement>::new(num_variables);
        let weight_val = Weights::evaluation(MultilinearPoint(alpha.clone()));
        statement_val.add_constraint(weight_val, line_evaluations[0].clone());

        let prover_val = Prover(whir_config_terms.clone());
        let proof_val = prover_val
            .prove(&mut merlin, statement_val, witness_val)
            .expect("WHIR prover failed to generate a proof");

        let mut statement_e_rx = Statement::<FieldElement>::new(num_variables);
        let weight_e_rx = Weights::evaluation(MultilinearPoint(alpha.clone()));
        statement_e_rx.add_constraint(weight_e_rx, line_evaluations[1].clone());

        let prover_e_rx = Prover(whir_config_terms.clone());
        let proof_e_rx = prover_e_rx
            .prove(&mut merlin, statement_e_rx, witness_e_rx)
            .expect("WHIR prover failed to generate a proof");

        let mut statement_e_ry = Statement::<FieldElement>::new(num_variables);
        let weight_e_ry = Weights::evaluation(MultilinearPoint(alpha.clone()));
        statement_e_ry.add_constraint(weight_e_ry, line_evaluations[2].clone());

        let prover_e_ry = Prover(whir_config_terms.clone());
        let proof_e_ry = prover_e_ry
            .prove(&mut merlin, statement_e_ry, witness_e_ry)
            .expect("WHIR prover failed to generate a proof");

        let transcript = merlin.narg_string().to_vec();

        Ok(WhirR1CSProof {
            transcript,
            whir_proof,
            proof_val,
            proof_e_rx,
            proof_e_ry,
            whir_query_answer_sums,
            num_terms: matrix_val.len(),
            val: line_evaluations[0].clone(),
            e_rx: line_evaluations[1].clone(),
            e_ry: line_evaluations[2].clone(),
        })
    }

    #[instrument(skip_all)]
    #[allow(unused)] // TODO: Fix implementation
    pub fn verify(&self, proof: &WhirR1CSProof) -> Result<()> {
        // Set up transcript
        let whir_config_terms = generate_whir_config(proof.num_terms);

        let io = create_io_pattern(self.m_0, &self.whir_config, &whir_config_terms, proof.num_terms);
        let mut arthur = io.to_verifier_state(&proof.transcript);

        // Compute statement verifier
        let mut statement_verifier =
            StatementVerifier::from_statement(&Statement::<FieldElement>::new(self.m));
        for claimed_sum in &proof.whir_query_answer_sums {
            statement_verifier
                .add_constraint(VerifierWeights::linear(self.m, None), claimed_sum.clone());
        }

        let data_from_sumcheck_verifier =
            run_sumcheck_verifier(&mut arthur, self.m_0).context("while verifying sumcheck")?;
        run_whir_pcs_verifier(
            &mut arthur,
            &self.whir_config,
            &proof.whir_proof,
            &statement_verifier,
        )
        .context("while verifying WHIR proof")?;

        let commitment_reader = CommitmentReader::new(&whir_config_terms);
        let verifier = Verifier::new(&whir_config_terms);
        let parsed_commitment1 = commitment_reader.parse_commitment(&mut arthur).unwrap();
        let parsed_commitment2 = commitment_reader.parse_commitment(&mut arthur).unwrap();
        let parsed_commitment3 = commitment_reader.parse_commitment(&mut arthur).unwrap();

        let mut alpha_collector = Vec::<FieldElement>::new();
        let mut h = [FieldElement::zero(); 4];
        let mut alpha = [FieldElement::zero(); 1];
        
        let mut last_sumcheck_value = proof.whir_proof.statement_values_at_random_point[0].clone();

        for _ in 0..next_power_of_two(proof.num_terms) {
            arthur.fill_next_scalars(&mut h)
                .expect("Failed to fill next scalars");
            arthur.fill_challenge_scalars(&mut alpha)
                .expect("Failed to fill next scalars");
            assert_eq!(eval_qubic_poly(&h, &FieldElement::from(0)) + eval_qubic_poly(&h, &FieldElement::from(1)), last_sumcheck_value);
            last_sumcheck_value = eval_qubic_poly(&h, &alpha[0]);
            alpha_collector.push(alpha[0]);
        }

        let weights = VerifierWeights::evaluation(MultilinearPoint(alpha_collector));
        
        let mut statement_verifier_val = StatementVerifier::from_statement(&Statement::<FieldElement>::new(next_power_of_two(proof.num_terms)));
        statement_verifier_val.add_constraint(weights.clone(), proof.val.clone());
        let verifier = Verifier::new(&whir_config_terms);
        verifier.verify(&mut arthur, &parsed_commitment1, &statement_verifier_val, &proof.proof_val)
            .expect("WHIR verifier failed to verify the proof");

        let mut statement_verifier_e_rx = StatementVerifier::from_statement(&Statement::<FieldElement>::new(next_power_of_two(proof.num_terms)));
        statement_verifier_e_rx.add_constraint(weights.clone(), proof.e_rx.clone());
        let verifier = Verifier::new(&whir_config_terms);
        verifier.verify(&mut arthur, &parsed_commitment2, &statement_verifier_e_rx, &proof.proof_e_rx)
            .expect("WHIR verifier failed to verify the proof");

        let mut statement_verifier_e_ry = StatementVerifier::from_statement(&Statement::<FieldElement>::new(next_power_of_two(proof.num_terms)));
        statement_verifier_e_ry.add_constraint(weights, proof.e_ry.clone());
        let verifier = Verifier::new(&whir_config_terms);
        verifier.verify(&mut arthur, &parsed_commitment3, &statement_verifier_e_ry, &proof.proof_e_ry)
            .expect("WHIR verifier failed to verify the proof");
        
        ensure!(
            last_sumcheck_value == proof.val * proof.e_rx * proof.e_ry,
            "last sumcheck value does not match"
        );
        // Check the Spartan sumcheck relation.
        ensure!(
            data_from_sumcheck_verifier.last_sumcheck_val
                == (proof.whir_query_answer_sums[0] * proof.whir_query_answer_sums[1]
                    - proof.whir_query_answer_sums[2])
                    * calculate_eq(
                        &data_from_sumcheck_verifier.r,
                        &data_from_sumcheck_verifier.alpha
                    ),
            "last sumcheck value does not match"
        );

        // TODO: Verify evaluation of sparse matrices in random point.

        Ok(())
    }
}

// TODO: Implement Debug for WhirConfig and derive.
impl Debug for WhirR1CSScheme {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("WhirR1CSScheme")
            .field("m", &self.m)
            .field("m_0", &self.m_0)
            .finish()
    }
}

#[instrument(skip_all)]
pub fn run_sumcheck_prover(
    r1cs: &R1CS,
    z: &[FieldElement],
    mut merlin: ProverState<SkyscraperSponge, FieldElement>,
    m_0: usize,
) -> (
    ProverState<SkyscraperSponge, FieldElement>,
    Vec<FieldElement>,
) {
    let mut saved_val_for_sumcheck_equality_assertion = FieldElement::zero();
    // r is the combination randomness from the 2nd item of the interaction phase
    let mut r = vec![FieldElement::zero(); m_0];
    merlin
        .fill_challenge_scalars(&mut r)
        .expect("Failed to extract challenge scalars from Merlin");

    // let a = sum_fhat_1, b = sum_fhat_2, c = sum_fhat_3 for brevity
    let ((mut a, mut b, mut c), mut eq) = rayon::join(
        || calculate_witness_bounds(r1cs, z),
        || calculate_evaluations_over_boolean_hypercube_for_eq(&r),
    );

    let mut alpha = Vec::<FieldElement>::with_capacity(m_0);

    let mut fold = None;


    
    for _ in 0..m_0 {
        // Here hhat_i_at_x represents hhat_i(x). hhat_i(x) is the qubic sumcheck
        // polynomial sent by the prover.
        let [hhat_i_at_0, hhat_i_at_em1, hhat_i_at_inf_over_x_cube] =
            sumcheck_fold_map_reduce([&mut a, &mut b, &mut c, &mut eq], fold, |[a, b, c, eq]| {
                [
                    // Evaluation at 0
                    eq.0 * (a.0 * b.0 - c.0),
                    // Evaluation at -1
                    (eq.0 + eq.0 - eq.1)
                        * ((a.0 + a.0 - a.1) * (b.0 + b.0 - b.1) - (c.0 + c.0 - c.1)),
                    // Evaluation at infinity
                    (eq.1 - eq.0) * (a.1 - a.0) * (b.1 - b.0),
                ]
            });
        if fold.is_some() {
            a.truncate(a.len() / 2);
            b.truncate(b.len() / 2);
            c.truncate(c.len() / 2);
            eq.truncate(eq.len() / 2);
        }

        let mut hhat_i_coeffs = [FieldElement::zero(); 4];

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
        let mut alpha_i_wrapped_in_vector = [FieldElement::zero()];
        let _ = merlin.fill_challenge_scalars(&mut alpha_i_wrapped_in_vector);
        let alpha_i = alpha_i_wrapped_in_vector[0];
        alpha.push(alpha_i);

        fold = Some(alpha_i);

        saved_val_for_sumcheck_equality_assertion = eval_qubic_poly(&hhat_i_coeffs, &alpha_i);
    }
    (merlin, alpha)
}

#[instrument(skip_all)]
pub fn run_whir_pcs_prover(
    z: Vec<FieldElement>,
    params: &WhirConfig,
    mut merlin: ProverState<SkyscraperSponge, FieldElement>,
    m: usize,
    alphas: [Vec<FieldElement>; 3],
) -> (
    WhirProof,
    ProverState<SkyscraperSponge, FieldElement>,
    [FieldElement; 3],
) {
    info!("WHIR Parameters: {params}");

    if !params.check_pow_bits() {
        warn!("More PoW bits required than specified.");
    }

    let z = pad_to_power_of_two(z);
    let poly = EvaluationsList::new(z);
    let polynomial = poly.to_coeffs();

    let committer = CommitmentWriter::new(params.clone());
    let witness = committer
        .commit(&mut merlin, polynomial)
        .expect("WHIR prover failed to commit");

    let mut statement = Statement::<FieldElement>::new(m);

    let sums: [FieldElement; 3] = alphas.map(|alpha| {
        let weight = Weights::linear(EvaluationsList::new(pad_to_power_of_two(alpha)));
        let sum = weight.weighted_sum(&poly);
        statement.add_constraint(weight, sum);
        sum
    });

    let prover = Prover(params.clone());
    let proof = prover
        .prove(&mut merlin, statement, witness)
        .expect("WHIR prover failed to generate a proof");

    (proof, merlin, sums)
}

#[instrument(skip_all)]
pub fn run_sumcheck_verifier(
    arthur: &mut VerifierState<SkyscraperSponge, FieldElement>,
    m_0: usize,
) -> Result<DataFromSumcheckVerifier> {
    // r is the combination randomness from the 2nd item of the interaction phase
    let mut r = vec![FieldElement::zero(); m_0];
    let _ = arthur.fill_challenge_scalars(&mut r);

    let mut saved_val_for_sumcheck_equality_assertion = FieldElement::zero();

    let mut alpha = vec![FieldElement::zero(); m_0];

    for i in 0..m_0 {
        let mut hhat_i = [FieldElement::zero(); 4];
        let mut alpha_i = [FieldElement::zero(); 1];
        let _ = arthur.fill_next_scalars(&mut hhat_i);
        let _ = arthur.fill_challenge_scalars(&mut alpha_i);
        alpha[i] = alpha_i[0];
        let hhat_i_at_zero = eval_qubic_poly(&hhat_i, &FieldElement::zero());
        let hhat_i_at_one = eval_qubic_poly(&hhat_i, &FieldElement::one());
        ensure!(
            saved_val_for_sumcheck_equality_assertion == hhat_i_at_zero + hhat_i_at_one,
            "Sumcheck equality assertion failed"
        );
        saved_val_for_sumcheck_equality_assertion = eval_qubic_poly(&hhat_i, &alpha_i[0]);
    }

    Ok(DataFromSumcheckVerifier {
        r,
        alpha,
        last_sumcheck_val: saved_val_for_sumcheck_equality_assertion,
    })
}

#[instrument(skip_all)]
pub fn run_whir_pcs_verifier(
    arthur: &mut VerifierState<SkyscraperSponge, FieldElement>,
    params: &WhirConfig,
    proof: &WhirProof,
    statement_verifier: &StatementVerifier,
) -> Result<()> {
    let commitment_reader = CommitmentReader::new(&params);
    let verifier = Verifier::new(&params);
    // let verifier = Verifier::new(&params);
    let parsed_commitment = commitment_reader.parse_commitment(arthur).unwrap();

    verifier
        .verify(arthur, &parsed_commitment, &statement_verifier, &proof)
        .context("while verifying WHIR")?;

    Ok(())
}

#[instrument(skip_all)]
pub fn create_io_pattern(m_0: usize, whir_params: &WhirConfig, whir_params_terms: &WhirConfig, num_terms: usize) -> IOPattern {
    IOPattern::new("🌪️")
        .add_rand(m_0)
        .add_sumcheck_polynomials(4, m_0)
        .commit_statement(&whir_params)
        .add_whir_proof(&whir_params)
        .commit_statement(&whir_params_terms)
        .commit_statement(&whir_params_terms)
        .commit_statement(&whir_params_terms)
        .add_sumcheck_polynomials(4, next_power_of_two(num_terms))
        .add_whir_proof(&whir_params_terms)
        .add_whir_proof(&whir_params_terms)
        .add_whir_proof(&whir_params_terms)
}

pub fn generate_whir_config(num_coeffs: usize) -> WhirConfig {
    let num_variables = next_power_of_two(num_coeffs);
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

    return whir_config;
}