use circuit_verifier::statement::CircuitStatement;
use circuits::ops::Guess;

use crate::prover::prepare_circuit_proof_for_circuit_verifier;
use crate::prover::{BaseColumnPool, CircuitProof, SimdBackend, prove_circuit_assignment};
use circuit_common::finalize::finalize_context;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_verifier::circuit_claim::CircuitInteractionElements;
use circuit_verifier::circuit_claim::lookup_sum;
use circuit_verifier::statement::{INTERACTION_POW_BITS, all_circuit_components};
use circuit_verifier::verify::{CircuitConfig, verify_circuit};
use circuits::blake::{blake, m31_to_u32};
use circuits::context::Var;
use circuits::eval;
use circuits::ivalue::{IValue, qm31_from_u32s};
use circuits::ops::{output, permute};
use circuits::poseidon2_hasher::{
    Poseidon2M31Channel, Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher,
};
use circuits::{context::Context, ops::guess};
use circuits_stark_verifier::proof::{Proof as CircuitVerifierProof, ProofConfig};
use circuits_stark_verifier::verify::verify;
use expect_test::expect;
use num_traits::{One, Zero};
use stwo::core::air::Component;
use stwo::core::channel::Channel;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::{CommitmentSchemeVerifier, PcsConfig, TreeVec};
// Not a power of 2 so that we can test component padding.
const N: usize = 1030;

pub fn build_fibonacci_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    let (mut a, mut b) = (guess(&mut context, QM31::zero()), guess(&mut context, QM31::one()));
    for _ in 2..N {
        (a, b) = (b, eval!(&mut context, (a) + (b)));
    }

    expect![[r#"
        (809871181 + 0i) + (0 + 0i)u
    "#]]
    .assert_debug_eq(&context.get(b));
    output(&mut context, b);

    context
}

pub fn build_permutation_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    let a = guess(&mut context, qm31_from_u32s(0, 2, 0, 2));
    let b = guess(&mut context, qm31_from_u32s(1, 1, 1, 1));

    let outputs = permute(&mut context, &[a, b], IValue::sort_by_u_coordinate);
    let _outputs = permute(&mut context, &outputs, IValue::sort_by_u_coordinate);

    context
}

pub fn build_blake_gate_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();
    context.enable_assert_eq_on_eval();

    let mut inputs: Vec<Var> = vec![];
    let n_inputs = 9;
    let n_bytes = n_inputs * 16;
    let n_blake_gates = 15;
    for i in 0..n_inputs {
        inputs.push(guess(
            &mut context,
            qm31_from_u32s(4 * i + 82, 4 * i + 83, 4 * i + 84, 4 * i + 85),
        ));
    }
    for _ in 0..n_blake_gates {
        let output = blake(&mut context, &inputs, n_bytes as usize);
        eval!(&mut context, (output.0) + (output.1));
    }

    context
}

pub fn build_m31_to_u32_context() -> Context<QM31> {
    let mut context = Context::<QM31>::default();

    let a = guess(&mut context, QM31::from(42));
    let out_a = m31_to_u32(&mut context, a);
    expect![[r#"
        (42 + 0i) + (0 + 0i)u
    "#]]
    .assert_debug_eq(&context.get(out_a));

    let b = guess(&mut context, QM31::from(100_000));
    let out_b = m31_to_u32(&mut context, b);
    expect![[r#"
        (34464 + 1i) + (0 + 0i)u
    "#]]
    .assert_debug_eq(&context.get(out_b));

    let c = guess(&mut context, QM31::from(2_000_042));
    let out_c = m31_to_u32(&mut context, c);
    expect![[r#"
        (33962 + 30i) + (0 + 0i)u
    "#]]
    .assert_debug_eq(&context.get(out_c));

    context
}

/// Verifies a [`CircuitProof`] using the stwo verifier. Asserts that the proof is valid
/// and that the logup sum is zero.
fn stwo_verify(
    circuit_proof: CircuitProof<Poseidon2M31MerkleHasher>,
    preprocessed_circuit: &PreprocessedCircuit,
) {
    let CircuitProof {
        components,
        claim,
        interaction_claim,
        pcs_config,
        stark_proof,
        interaction_pow_nonce,
        channel_salt,
    } = circuit_proof;
    assert!(stark_proof.is_ok(), "Got error: {}", stark_proof.err().unwrap());
    let proof = stark_proof.unwrap();

    let verifier_channel = &mut Poseidon2M31Channel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(verifier_channel);
    let commitment_scheme =
        &mut CommitmentSchemeVerifier::<Poseidon2M31MerkleChannel>::new(pcs_config);

    // Retrieve the expected column sizes in each commitment interaction, from the AIR.
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_circuit.preprocessed_trace.log_sizes(),
        verifier_channel,
    );
    claim.mix_into(verifier_channel);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);

    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);

    verifier_channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(verifier_channel);

    interaction_claim.mix_into(verifier_channel);

    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);
    stwo::core::verifier::verify_ex(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
        true,
    )
    .unwrap();

    assert_eq!(
        lookup_sum(
            &claim,
            &interaction_claim,
            &interaction_elements,
            &preprocessed_circuit.params.output_addresses,
        ),
        QM31::zero()
    );
}

#[test]
#[ignore = "Blake gate AIR removed on feat/poseidon-instead-blake branch"]
fn test_prove_and_stark_verify_blake_gate_context() {
    let mut blake_gate_context = build_blake_gate_context();
    blake_gate_context.finalize_guessed_vars();
    blake_gate_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut blake_gate_context);
    let circuit_proof = prove_circuit_assignment(
        blake_gate_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );
    stwo_verify(circuit_proof, &preprocessed_circuit);
}

#[test]
fn test_prove_and_stark_verify_permutation_context() {
    let mut permutation_context = build_permutation_context();
    permutation_context.finalize_guessed_vars();
    permutation_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut permutation_context);
    let circuit_proof = prove_circuit_assignment(
        permutation_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );
    stwo_verify(circuit_proof, &preprocessed_circuit);
}

#[test]
fn test_prove_and_stark_verify_fibonacci_context() {
    let mut fibonacci_context = build_fibonacci_context();
    fibonacci_context.finalize_guessed_vars();
    fibonacci_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut fibonacci_context);
    let circuit_proof = prove_circuit_assignment(
        fibonacci_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );
    stwo_verify(circuit_proof, &preprocessed_circuit);
}

#[test]
fn test_prove_and_stark_verify_m31_to_u32_context() {
    let mut m31_to_u32_context = build_m31_to_u32_context();
    m31_to_u32_context.finalize_guessed_vars();
    m31_to_u32_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut m31_to_u32_context);
    let circuit_proof = prove_circuit_assignment(
        m31_to_u32_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );
    stwo_verify(circuit_proof, &preprocessed_circuit);
}

/// Verifies a [`CircuitProof`] using the circuit verifier. Requires the expected
/// `preprocessed_root` of the preprocessed trace.
fn circuit_verify(
    circuit_proof: CircuitProof<Poseidon2M31MerkleHasher>,
    preprocessed_circuit: &PreprocessedCircuit,
    preprocessed_root: [u32; 8],
) {
    let all_components = all_circuit_components::<QM31>();
    let enabled_bits: Vec<bool> = vec![true; all_components.len()];
    let proof_config = ProofConfig::from_components(
        &all_components,
        enabled_bits,
        preprocessed_circuit.preprocessed_trace.log_sizes(),
        &circuit_proof.pcs_config,
        INTERACTION_POW_BITS,
    );
    let circuit_config = CircuitConfig {
        config: circuit_proof.pcs_config,
        output_addresses: preprocessed_circuit.params.output_addresses.clone(),
        preprocessed_column_ids: preprocessed_circuit.preprocessed_trace.ids(),
        preprocessed_column_log_sizes: preprocessed_circuit.preprocessed_trace.log_sizes(),
        preprocessed_root: preprocessed_root.into(),
    };
    let (proof, public_data) =
        prepare_circuit_proof_for_circuit_verifier(circuit_proof, &proof_config);
    verify_circuit(circuit_config, proof, public_data).unwrap();
}

const FIBONACCI_CIRCUIT_PREPROCESSED_ROOT: [u32; 8] =
    [1228621624, 1400444575, 2071683022, 1347216230, 951524942, 274707708, 335154903, 383538658];

#[test]
fn test_prove_and_circuit_verify_fibonacci_context() {
    let mut fibonacci_context = build_fibonacci_context();
    fibonacci_context.finalize_guessed_vars();
    fibonacci_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut fibonacci_context);
    let circuit_proof = prove_circuit_assignment(
        fibonacci_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );
    circuit_verify(circuit_proof, &preprocessed_circuit, FIBONACCI_CIRCUIT_PREPROCESSED_ROOT);
}

const M31_TO_U32_CIRCUIT_PREPROCESSED_ROOT: [u32; 8] =
    [316480374, 1333804270, 165422386, 212229647, 1065228925, 182130970, 648747840, 1585670006];

#[test]
fn test_prove_and_circuit_verify_m31_to_u32_context() {
    let mut m31_to_u32_context = build_m31_to_u32_context();
    m31_to_u32_context.finalize_guessed_vars();
    m31_to_u32_context.validate_circuit();

    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut m31_to_u32_context);
    let circuit_proof = prove_circuit_assignment(
        m31_to_u32_context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );

    circuit_verify(circuit_proof, &preprocessed_circuit, M31_TO_U32_CIRCUIT_PREPROCESSED_ROOT);
}

#[test]
fn test_finalize_context() {
    let mut context = build_fibonacci_context();
    finalize_context(&mut context);

    assert!(context.circuit.add.len().is_power_of_two());
    context.validate_circuit();
}

struct ChildForRecursiveVerify {
    output_addresses: Vec<usize>,
    output_values: Vec<QM31>,
    pp_trace_ids: Vec<stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId>,
    pp_trace_log_sizes: Vec<u32>,
    root: circuits::blake::HashValue<QM31>,
    proof: CircuitVerifierProof<QM31>,
    proof_config: ProofConfig,
}

fn build_child_for_recursive_verify() -> ChildForRecursiveVerify {
    let mut child_context = build_m31_to_u32_context();
    child_context.finalize_guessed_vars();
    child_context.validate_circuit();

    let preprocessed_child = PreprocessedCircuit::preprocess_circuit(&mut child_context);
    let child_circuit_proof = prove_circuit_assignment(
        child_context.values(),
        &preprocessed_child,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );

    let root = child_circuit_proof.stark_proof.as_ref().unwrap().proof.commitments[0].into();
    let output_addresses = preprocessed_child.params.output_addresses.clone();
    let pp_trace_ids = preprocessed_child.preprocessed_trace.ids();
    let pp_trace_log_sizes = preprocessed_child.preprocessed_trace.log_sizes();
    let output_values = child_circuit_proof.claim.output_values.clone();

    let all_components = all_circuit_components::<QM31>();
    let enabled_bits: Vec<bool> = vec![true; all_components.len()];
    let proof_config = ProofConfig::from_components(
        &all_components,
        enabled_bits,
        pp_trace_log_sizes.clone(),
        &child_circuit_proof.pcs_config,
        INTERACTION_POW_BITS,
    );

    let (proof, _public_data) =
        prepare_circuit_proof_for_circuit_verifier(child_circuit_proof, &proof_config);

    ChildForRecursiveVerify {
        output_addresses,
        output_values,
        pp_trace_ids,
        pp_trace_log_sizes,
        root,
        proof,
        proof_config,
    }
}

#[test]
#[ignore = "Reproducer for recursive in-circuit verify panic when Blake gates are generated but Blake AIR is absent"]
#[should_panic(expected = "assertion `left == right` failed")]
fn test_repro_recursive_in_circuit_verify_lookup_sum_panic() {
    let child_left = build_child_for_recursive_verify();
    let child_right = build_child_for_recursive_verify();

    let mut merge_like_context = Context::<QM31>::default();

    for child in [child_left, child_right] {
        let statement = CircuitStatement::new(
            &mut merge_like_context,
            &child.output_addresses,
            &child.output_values,
            child.pp_trace_ids,
            child.pp_trace_log_sizes,
            child.root,
        );
        let proof_vars = child.proof.guess(&mut merge_like_context);
        verify(&mut merge_like_context, &proof_vars, &child.proof_config, &statement);
    }

    merge_like_context.finalize_guessed_vars();
    merge_like_context.validate_circuit();

    let merge_preprocessed = PreprocessedCircuit::preprocess_circuit(&mut merge_like_context);
    let _ = prove_circuit_assignment(
        merge_like_context.values(),
        &merge_preprocessed,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    );
}
