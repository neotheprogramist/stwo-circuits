use crate::circuit_components::N_COMPONENTS;
use crate::relations::{CommonLookupElements, GATE_RELATION_ID};
use circuits::ivalue::qm31_from_u32s;
use circuits_stark_verifier::proof_from_stark_proof::{pack_component_log_sizes, pack_enable_bits};
use itertools::zip_eq;
use num_traits::Zero;
use stwo::core::channel::Channel;
use stwo::core::fields::FieldExpOps;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::Relation;

pub type ComponentLogSize = u32;
pub type ClaimedSum = QM31;

#[derive(Debug, PartialEq)]
pub struct CircuitClaim {
    pub log_sizes: [ComponentLogSize; N_COMPONENTS],
    pub output_values: Vec<QM31>,
}
impl CircuitClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        let Self { log_sizes, output_values } = self;

        // mix the number of components.
        let n_components = log_sizes.len();
        channel.mix_felts(&[qm31_from_u32s(n_components as u32, 0, 0, 0)]);

        // Mix enable bits according to active component log sizes.
        let enable_bits = log_sizes.map(|log_size| log_size > 0);
        channel.mix_felts(&pack_enable_bits(&enable_bits));
        channel.mix_felts(&pack_component_log_sizes(log_sizes));
        // mix the output values into the channel.
        channel.mix_felts(output_values);
    }
}

pub struct CircuitInteractionElements {
    pub common_lookup_elements: CommonLookupElements,
}
impl CircuitInteractionElements {
    pub fn draw(channel: &mut impl Channel) -> CircuitInteractionElements {
        CircuitInteractionElements { common_lookup_elements: CommonLookupElements::draw(channel) }
    }
}

#[derive(Debug, PartialEq)]
pub struct CircuitInteractionClaim {
    pub claimed_sums: [ClaimedSum; N_COMPONENTS],
}
impl CircuitInteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        let Self { claimed_sums } = self;
        channel.mix_felts(claimed_sums);
    }
}

pub fn lookup_sum(
    claim: &CircuitClaim,
    interaction_claim: &CircuitInteractionClaim,
    interaction_elements: &CircuitInteractionElements,
    output_addresses: &[usize],
) -> QM31 {
    let CircuitInteractionClaim { claimed_sums } = interaction_claim;
    let component_sum: QM31 = claimed_sums.iter().sum();

    // Compute the public logup sum from output gates.
    let mut output_sum = QM31::zero();
    let gate_relation_id = M31::from(GATE_RELATION_ID);
    for (addr, value) in zip_eq(output_addresses, &claim.output_values) {
        let values =
            [gate_relation_id, M31::from(*addr as u32), value.0.0, value.0.1, value.1.0, value.1.1];
        let denom: QM31 = interaction_elements.common_lookup_elements.combine(&values);
        output_sum += denom.inverse();
    }

    component_sum + output_sum
}
