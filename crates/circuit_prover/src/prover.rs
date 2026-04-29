use crate::circuit_air::components::{eq, m_31_to_u_32, poseidon_gate, qm31_ops, range_check_16};
use crate::witness::trace::TraceGenerator;
use crate::witness::trace::write_interaction_trace;
use crate::witness::trace::write_trace;
use circuit_common::CircuitParams;
use circuit_common::Qm31OpsTraceGenerator;
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_verifier::circuit_claim::{
    CircuitClaim, CircuitInteractionClaim, CircuitInteractionElements, lookup_sum,
};
use circuit_verifier::circuit_components::ComponentList;
use circuit_verifier::statement::INTERACTION_POW_BITS;
use circuit_verifier::verify::CircuitPublicData;
use circuits::context::Context;
use circuits_stark_verifier::proof::Proof;
use circuits_stark_verifier::proof::{Claim, ProofConfig};
use circuits_stark_verifier::proof_from_stark_proof::{
    pack_component_log_sizes, proof_from_stark_proof,
};
use num_traits::Zero;
use stwo::core::air::Component;
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::proof::ExtendedStarkProof;
use stwo::core::proof_of_work::GrindOps;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleHasher;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;
use stwo::prover::CommitmentSchemeProver;
use stwo::prover::CommitmentTreeProver;
use stwo::prover::ComponentProver;
pub use stwo::prover::backend::simd::SimdBackend;
pub use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::{ProvingError, prove_ex};
use stwo_constraint_framework::TraceLocationAllocator;

const COMPOSITION_POLYNOMIAL_LOG_DEGREE_BOUND: u32 = 1;

pub struct CircuitProof<H: MerkleHasherLifted> {
    pub pcs_config: PcsConfig,
    pub claim: CircuitClaim,
    pub interaction_pow_nonce: u64,
    pub interaction_claim: CircuitInteractionClaim,
    pub components: Vec<Box<dyn Component>>,
    pub stark_proof: Result<ExtendedStarkProof<H>, ProvingError>,
    pub channel_salt: u32,
}

#[cfg(test)]
#[path = "prover_test.rs"]
pub mod test;

pub fn prove_circuit(context: &mut Context<QM31>) -> CircuitProof<Blake2sM31MerkleHasher> {
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(context);
    prove_circuit_assignment(
        context.values(),
        &preprocessed_circuit,
        &BaseColumnPool::<SimdBackend>::new(),
        PcsConfig::default(),
    )
}

pub fn prove_circuit_assignment(
    values: &[QM31],
    preprocessed_circuit: &PreprocessedCircuit,
    base_column_pool: &BaseColumnPool<SimdBackend>,
    pcs_config: PcsConfig,
) -> CircuitProof<Blake2sM31MerkleHasher> {
    prove_circuit_assignment_with_channel::<Blake2sM31MerkleChannel>(
        values,
        preprocessed_circuit,
        base_column_pool,
        pcs_config,
    )
}


pub fn prove_circuit_assignment_with_channel<MC>(
    values: &[QM31],
    preprocessed_circuit: &PreprocessedCircuit,
    base_column_pool: &BaseColumnPool<SimdBackend>,
    pcs_config: PcsConfig,
) -> CircuitProof<MC::H>
where
    MC: MerkleChannel,
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>,
{
    let trace_log_size = preprocessed_circuit.params.trace_log_size;
    let lifting_log_size = trace_log_size + pcs_config.fri_config.log_blowup_factor;
    let pcs_config = PcsConfig { lifting_log_size: Some(lifting_log_size), ..pcs_config };

    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(
            trace_log_size
                + std::cmp::max(
                    pcs_config.fri_config.log_blowup_factor,
                    COMPOSITION_POLYNOMIAL_LOG_DEGREE_BOUND,
                ),
        )
        .circle_domain()
        .half_coset,
    );

    let preprocessed_trace = preprocessed_circuit.preprocessed_trace.get_trace::<SimdBackend>();
    let preprocessed_trace_polys = SimdBackend::interpolate_columns(preprocessed_trace, &twiddles);

    let store_polynomials_coefficients = true;
    let preprocessed_tree = CommitmentTreeProver::<SimdBackend, MC>::new(
        preprocessed_trace_polys,
        pcs_config.fri_config.log_blowup_factor,
        &twiddles,
        store_polynomials_coefficients,
        pcs_config.lifting_log_size,
        base_column_pool,
    );

    prove_circuit_with_precompute::<MC>(
        base_column_pool,
        &twiddles,
        preprocessed_circuit,
        MaybeOwned::Owned(preprocessed_tree),
        values,
        pcs_config,
    )
}

pub fn prove_circuit_with_precompute<'a, MC>(
    base_column_pool: &BaseColumnPool<SimdBackend>,
    twiddles: &TwiddleTree<SimdBackend>,
    preprocessed_circuit: &PreprocessedCircuit,
    preprocessed_tree: MaybeOwned<'a, CommitmentTreeProver<SimdBackend, MC>>,
    values: &[QM31],
    pcs_config: PcsConfig,
) -> CircuitProof<MC::H>
where
    MC: MerkleChannel,
    SimdBackend: stwo::prover::backend::BackendForChannel<MC>,
{
    let PreprocessedCircuit { preprocessed_trace, params } = preprocessed_circuit;
    let CircuitParams { first_permutation_row, output_addresses, .. } = params;
    let trace_generator = TraceGenerator {
        qm31_ops_trace_generator: Qm31OpsTraceGenerator {
            first_permutation_row: *first_permutation_row,
        },
    };

    let channel = &mut MC::C::default();

    let channel_salt = 0_u32;
    channel.mix_felts(&[channel_salt.into()]);
    pcs_config.mix_into(channel);
    let mut commitment_scheme = CommitmentSchemeProver::<SimdBackend, MC>::with_memory_pool(
        pcs_config,
        twiddles,
        base_column_pool,
    );

    commitment_scheme.set_store_polynomials_coefficients();

    commitment_scheme.commit_tree(preprocessed_tree, channel);

    // Base trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    let (claim, interaction_generator) = write_trace(
        values,
        preprocessed_trace.clone(),
        output_addresses,
        &mut tree_builder,
        &trace_generator,
        twiddles,
    );
    claim.mix_into(channel);
    tree_builder.commit(channel);

    // Draw interaction elements.
    let interaction_pow_nonce = SimdBackend::grind(channel, INTERACTION_POW_BITS);
    channel.mix_u64(interaction_pow_nonce);
    let interaction_elements = CircuitInteractionElements::draw(channel);

    // Interaction trace.
    let mut tree_builder = commitment_scheme.tree_builder();
    let interaction_claim = write_interaction_trace(
        &claim,
        interaction_generator,
        &mut tree_builder,
        &interaction_elements,
        twiddles,
    );

    assert_eq!(
        lookup_sum(&claim, &interaction_claim, &interaction_elements, output_addresses),
        QM31::zero()
    );

    interaction_claim.mix_into(channel);
    tree_builder.commit(channel);

    // Construct components.
    let preprocessed_column_ids = preprocessed_trace.ids();
    let tree_span_provider =
        &mut TraceLocationAllocator::new_with_preprocessed_columns(&preprocessed_column_ids);

    let eq_component = eq::Component::new(
        tree_span_provider,
        eq::Eval {
            log_size: claim.log_sizes[ComponentList::Eq as usize],
            common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
        },
        interaction_claim.claimed_sums[ComponentList::Eq as usize],
    );
    let qm31_ops_component = qm31_ops::Component::new(
        tree_span_provider,
        qm31_ops::Eval {
            log_size: claim.log_sizes[ComponentList::Qm31Ops as usize],
            common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
        },
        interaction_claim.claimed_sums[ComponentList::Qm31Ops as usize],
    );
    let poseidon_gate_component = poseidon_gate::Component::new(
        tree_span_provider,
        poseidon_gate::Eval {
            claim: poseidon_gate::Claim {
                log_size: claim.log_sizes[ComponentList::PoseidonGate as usize],
            },
            common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
        },
        interaction_claim.claimed_sums[ComponentList::PoseidonGate as usize],
    );
    let m_31_to_u_32_component = m_31_to_u_32::Component::new(
        tree_span_provider,
        m_31_to_u_32::Eval {
            claim: m_31_to_u_32::Claim {
                log_size: claim.log_sizes[ComponentList::M31ToU32 as usize],
            },
            common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
        },
        interaction_claim.claimed_sums[ComponentList::M31ToU32 as usize],
    );
    let range_check_16_component = range_check_16::Component::new(
        tree_span_provider,
        range_check_16::Eval {
            claim: range_check_16::Claim {},
            common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
        },
        interaction_claim.claimed_sums[ComponentList::RangeCheck16 as usize],
    );

    let components: Vec<&dyn ComponentProver<SimdBackend>> = vec![
        &eq_component,
        &qm31_ops_component,
        &poseidon_gate_component,
        &m_31_to_u_32_component,
        &range_check_16_component,
    ];

    let proof = prove_ex::<SimdBackend, _>(&components, channel, commitment_scheme, true);
    CircuitProof {
        pcs_config,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components: vec![
            Box::new(eq_component) as Box<dyn Component>,
            Box::new(qm31_ops_component) as Box<dyn Component>,
            Box::new(poseidon_gate_component) as Box<dyn Component>,
            Box::new(m_31_to_u_32_component) as Box<dyn Component>,
            Box::new(range_check_16_component) as Box<dyn Component>,
        ],
        stark_proof: proof,
        channel_salt,
    }
}

pub fn prepare_circuit_proof_for_circuit_verifier(
    circuit_proof: CircuitProof<Blake2sM31MerkleHasher>,
    proof_config: &ProofConfig,
) -> (Proof<QM31>, CircuitPublicData) {
    let CircuitProof {
        pcs_config: _,
        claim,
        interaction_pow_nonce,
        interaction_claim,
        components: _,
        stark_proof,
        channel_salt,
    } = circuit_proof;
    assert!(stark_proof.is_ok());
    let stark_proof = stark_proof.unwrap();

    let public_data = CircuitPublicData { output_values: claim.output_values.clone() };

    let packed_claim = Claim {
        packed_component_log_sizes: pack_component_log_sizes(&claim.log_sizes),
        claimed_sums: interaction_claim.claimed_sums.to_vec(),
    };

    let proof = proof_from_stark_proof(
        &stark_proof,
        proof_config,
        packed_claim,
        interaction_pow_nonce,
        channel_salt,
    );
    (proof, public_data)
}
