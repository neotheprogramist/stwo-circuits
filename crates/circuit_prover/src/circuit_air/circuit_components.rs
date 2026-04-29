use crate::circuit_air::components::{eq, m_31_to_u_32, poseidon_gate, qm31_ops, range_check_16};
use circuit_verifier::circuit_claim::{
    CircuitClaim, CircuitInteractionClaim, CircuitInteractionElements,
};
use circuit_verifier::circuit_components::ComponentList;
use stwo::core::air::Component;
use stwo_constraint_framework::TraceLocationAllocator;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

pub struct CircuitComponents {
    pub eq: eq::Component,
    pub qm31_ops: qm31_ops::Component,
    pub poseidon_gate: poseidon_gate::Component,
    pub m_31_to_u_32: m_31_to_u_32::Component,
    pub range_check_16: range_check_16::Component,
}
impl CircuitComponents {
    pub fn new(
        circuit_claim: &CircuitClaim,
        interaction_elements: &CircuitInteractionElements,
        interaction_claim: &CircuitInteractionClaim,
        preprocessed_column_ids: &[PreProcessedColumnId],
    ) -> Self {
        let tree_span_provider =
            &mut TraceLocationAllocator::new_with_preprocessed_columns(preprocessed_column_ids);

        let eq_component = eq::Component::new(
            tree_span_provider,
            eq::Eval {
                log_size: circuit_claim.log_sizes[ComponentList::Eq as usize],
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::Eq as usize],
        );
        let qm31_ops_component = qm31_ops::Component::new(
            tree_span_provider,
            qm31_ops::Eval {
                log_size: circuit_claim.log_sizes[ComponentList::Qm31Ops as usize],
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::Qm31Ops as usize],
        );
        let poseidon_gate_component = poseidon_gate::Component::new(
            tree_span_provider,
            poseidon_gate::Eval {
                claim: poseidon_gate::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::PoseidonGate as usize],
                },
                common_lookup_elements: interaction_elements.common_lookup_elements.clone(),
            },
            interaction_claim.claimed_sums[ComponentList::PoseidonGate as usize],
        );
        let m_31_to_u_32_component = m_31_to_u_32::Component::new(
            tree_span_provider,
            m_31_to_u_32::Eval {
                claim: m_31_to_u_32::Claim {
                    log_size: circuit_claim.log_sizes[ComponentList::M31ToU32 as usize],
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
        Self {
            eq: eq_component,
            qm31_ops: qm31_ops_component,
            poseidon_gate: poseidon_gate_component,
            m_31_to_u_32: m_31_to_u_32_component,
            range_check_16: range_check_16_component,
        }
    }

    pub fn components(self) -> Vec<Box<dyn Component>> {
        vec![
            Box::new(self.eq) as Box<dyn Component>,
            Box::new(self.qm31_ops) as Box<dyn Component>,
            Box::new(self.poseidon_gate) as Box<dyn Component>,
            Box::new(self.m_31_to_u_32) as Box<dyn Component>,
            Box::new(self.range_check_16) as Box<dyn Component>,
        ]
    }
}
