use std::mem::MaybeUninit;
use std::sync::Arc;

use crate::witness::components::eq;
use crate::witness::components::m_31_to_u_32;
use crate::witness::components::poseidon_gate;
use crate::witness::components::qm31_ops;
use crate::witness::components::range_check_16;
use circuit_common::Qm31OpsTraceGenerator;
use circuit_common::preprocessed::PreProcessedTrace;
use circuit_verifier::circuit_claim::CircuitClaim;
use circuit_verifier::circuit_claim::CircuitInteractionClaim;
use circuit_verifier::circuit_claim::CircuitInteractionElements;
use itertools::Itertools;
use num_traits::Zero;
use rayon::scope;
use stwo::core::channel::MerkleChannel;
use stwo::core::fields::qm31::QM31;
use stwo::prover::TreeBuilder;
use stwo::prover::backend::BackendForChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;

pub struct TraceGenerator {
    pub qm31_ops_trace_generator: Qm31OpsTraceGenerator,
}

pub fn write_trace<MC: MerkleChannel>(
    context_values: &[QM31],
    preprocessed_trace: Arc<PreProcessedTrace>,
    output_addresses: &[usize],
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, MC>,
    trace_generator: &TraceGenerator,
    twiddles: &TwiddleTree<SimdBackend>,
) -> (CircuitClaim, CircuitInteractionClaimGenerator)
where
    SimdBackend: BackendForChannel<MC>,
{
    let preprocessed_trace_ref = preprocessed_trace.as_ref();

    let mut eq_result = MaybeUninit::uninit();
    let mut qm31_ops_result = MaybeUninit::uninit();
    let mut poseidon_gate_result = MaybeUninit::uninit();
    let mut m_31_to_u_32_polys_result = MaybeUninit::uninit();
    let mut m_31_to_u_32_claim_icg = MaybeUninit::uninit();
    let mut range_check_16_polys_result = MaybeUninit::uninit();
    let mut range_check_16_icg_result = MaybeUninit::uninit();

    scope(|s| {
        // eq, qm31_ops, poseidon_gate are fully independent — run in parallel.
        s.spawn(|_| {
            let (trace, log_size, lookup_data) = qm31_ops::write_trace(
                context_values,
                preprocessed_trace_ref,
                &trace_generator.qm31_ops_trace_generator,
            );
            let polys = SimdBackend::interpolate_columns(trace.to_evals(), twiddles);
            qm31_ops_result.write((polys, log_size, lookup_data));
        });
        s.spawn(|_| {
            let (trace, log_size, lookup_data) =
                eq::write_trace(context_values, preprocessed_trace_ref);
            let polys = SimdBackend::interpolate_columns(trace.to_evals(), twiddles);
            eq_result.write((polys, log_size, lookup_data));
        });
        s.spawn(|_| {
            let (trace, log_size, lookup_data) =
                poseidon_gate::write_trace(context_values, preprocessed_trace_ref);
            let polys = SimdBackend::interpolate_columns(trace.to_evals(), twiddles);
            poseidon_gate_result.write((polys, log_size, lookup_data));
        });

        // m_31_to_u_32 writes into range_check_16's multiplicity table, so they must be
        // sequential. The main thread handles both while the three spawns run in parallel.
        let range_check_16_state = range_check_16::ClaimGenerator::new(preprocessed_trace.clone());
        let (m31_trace, m31_claim, m31_icg) = m_31_to_u_32::write_trace(
            context_values,
            preprocessed_trace_ref,
            &range_check_16_state,
        );
        m_31_to_u_32_claim_icg.write((m31_claim, m31_icg));
        m_31_to_u_32_polys_result
            .write(SimdBackend::interpolate_columns(m31_trace.to_evals(), twiddles));

        let (rc16_trace, _rc16_claim, rc16_icg) = range_check_16_state.write_trace();
        range_check_16_icg_result.write(rc16_icg);
        range_check_16_polys_result
            .write(SimdBackend::interpolate_columns(rc16_trace.to_evals(), twiddles));
    });

    // SAFETY: All MaybeUninit values were initialized by the scope above.
    let (eq_polys, eq_log_size, eq_lookup_data) = unsafe { eq_result.assume_init() };
    let (qm31_ops_polys, qm31_ops_log_size, qm31_ops_lookup_data) =
        unsafe { qm31_ops_result.assume_init() };
    let (poseidon_gate_polys, poseidon_gate_log_size, poseidon_gate_lookup_data) =
        unsafe { poseidon_gate_result.assume_init() };
    let m_31_to_u_32_polys = unsafe { m_31_to_u_32_polys_result.assume_init() };
    let (m_31_to_u_32_claim, m_31_to_u_32_interaction_claim_gen) =
        unsafe { m_31_to_u_32_claim_icg.assume_init() };
    let range_check_16_polys = unsafe { range_check_16_polys_result.assume_init() };
    let range_check_16_interaction_claim_gen = unsafe { range_check_16_icg_result.assume_init() };

    tree_builder.extend_polys(eq_polys);
    tree_builder.extend_polys(qm31_ops_polys);
    tree_builder.extend_polys(poseidon_gate_polys);
    tree_builder.extend_polys(m_31_to_u_32_polys);
    tree_builder.extend_polys(range_check_16_polys);

    let output_values = output_addresses.iter().map(|addr| context_values[*addr]).collect_vec();

    (
        CircuitClaim {
            log_sizes: [
                eq_log_size,
                qm31_ops_log_size,
                poseidon_gate_log_size,
                m_31_to_u_32_claim.log_size,
                crate::circuit_air::components::range_check_16::LOG_SIZE,
            ],
            output_values,
        },
        CircuitInteractionClaimGenerator {
            eq_lookup_data,
            qm31_ops_lookup_data,
            poseidon_gate_lookup_data,
            m_31_to_u_32: m_31_to_u_32_interaction_claim_gen,
            range_check_16: range_check_16_interaction_claim_gen,
        },
    )
}

pub struct CircuitInteractionClaimGenerator {
    pub eq_lookup_data: eq::LookupData,
    pub qm31_ops_lookup_data: qm31_ops::LookupData,
    pub poseidon_gate_lookup_data: poseidon_gate::LookupData,
    pub m_31_to_u_32: m_31_to_u_32::InteractionClaimGenerator,
    pub range_check_16: range_check_16::InteractionClaimGenerator,
}

pub fn write_interaction_trace<MC: MerkleChannel>(
    circuit_claim: &CircuitClaim,
    circuit_interaction_claim_generator: CircuitInteractionClaimGenerator,
    tree_builder: &mut TreeBuilder<'_, '_, SimdBackend, MC>,
    interaction_elements: &CircuitInteractionElements,
    twiddles: &TwiddleTree<SimdBackend>,
) -> CircuitInteractionClaim
where
    SimdBackend: BackendForChannel<MC>,
{
    let CircuitClaim { log_sizes, output_values: _ } = circuit_claim;
    let mut component_log_size_iter = log_sizes.iter();

    let eq_log_size = *component_log_size_iter.next().unwrap();
    let qm31_ops_log_size = *component_log_size_iter.next().unwrap();
    let poseidon_gate_log_size = *component_log_size_iter.next().unwrap();

    // All 5 interaction traces are independent — write and interpolate in parallel.
    let mut all_polys: [Vec<_>; 5] = std::array::from_fn(|_| Vec::new());
    let [
        eq_polys,
        qm31_ops_polys,
        poseidon_gate_polys,
        m_31_to_u_32_polys,
        range_check_16_polys,
    ] = &mut all_polys;
    let mut claimed_sums = [QM31::zero(); 5];
    let [
        eq_claimed_sum,
        qm31_ops_claimed_sum,
        poseidon_gate_claimed_sum,
        m_31_to_u_32_claimed_sum,
        range_check_16_claimed_sum,
    ] = &mut claimed_sums;
    {
        let eq_lookup_data = circuit_interaction_claim_generator.eq_lookup_data;
        let qm31_ops_lookup_data = circuit_interaction_claim_generator.qm31_ops_lookup_data;
        let poseidon_gate_lookup_data = circuit_interaction_claim_generator.poseidon_gate_lookup_data;
        let m_31_to_u_32 = circuit_interaction_claim_generator.m_31_to_u_32;
        let range_check_16 = circuit_interaction_claim_generator.range_check_16;
        scope(|s| {
            s.spawn(|_| {
                let (trace, claimed_sum) = eq::write_interaction_trace(
                    eq_log_size,
                    eq_lookup_data,
                    &interaction_elements.common_lookup_elements,
                );
                *eq_polys = SimdBackend::interpolate_columns(trace, twiddles);
                *eq_claimed_sum = claimed_sum;
            });
            s.spawn(|_| {
                let (trace, claimed_sum) = qm31_ops::write_interaction_trace(
                    qm31_ops_log_size,
                    qm31_ops_lookup_data,
                    &interaction_elements.common_lookup_elements,
                );
                *qm31_ops_polys = SimdBackend::interpolate_columns(trace, twiddles);
                *qm31_ops_claimed_sum = claimed_sum;
            });
            s.spawn(|_| {
                let (trace, claimed_sum) = poseidon_gate::write_interaction_trace(
                    poseidon_gate_log_size,
                    poseidon_gate_lookup_data,
                    &interaction_elements.common_lookup_elements,
                );
                *poseidon_gate_polys = SimdBackend::interpolate_columns(trace, twiddles);
                *poseidon_gate_claimed_sum = claimed_sum;
            });
            s.spawn(|_| {
                let (trace, claim) = m_31_to_u_32
                    .write_interaction_trace(&interaction_elements.common_lookup_elements);
                *m_31_to_u_32_polys = SimdBackend::interpolate_columns(trace, twiddles);
                *m_31_to_u_32_claimed_sum = claim.claimed_sum;
            });
            s.spawn(|_| {
                let (trace, claim) = range_check_16
                    .write_interaction_trace(&interaction_elements.common_lookup_elements);
                *range_check_16_polys = SimdBackend::interpolate_columns(trace, twiddles);
                *range_check_16_claimed_sum = claim.claimed_sum;
            });
        });
    }

    tree_builder.extend_polys(all_polys.into_iter().flatten());

    CircuitInteractionClaim { claimed_sums }
}
