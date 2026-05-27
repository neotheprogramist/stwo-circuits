use circuits::blake::HashValue;
use circuits::context::{Context, Var};
use circuits::eval;
use circuits::ivalue::IValue;
use circuits::ops::Guess;
use circuits::simd::Simd;
use circuits::wrappers::M31Wrapper;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::logup::logup_use_term;
use circuits_stark_verifier::statement::Statement;
use indexmap::IndexMap;
use itertools::{Itertools, zip_eq};
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::components::eq::CircuitEqComponent;
use crate::components::m_31_to_u_32::Component as CircuitM31ToU32Component;
use crate::components::poseidon_gate::Component as CircuitPoseidonGateComponent;
use crate::components::qm31_ops::CircuitQm31OpsComponent;
use crate::components::range_check_16::Component as CircuitRangeCheck16Component;
use crate::relations::GATE_RELATION_ID;

// TODO(ilya): Update this to the correct values.
pub const INTERACTION_POW_BITS: u32 = 20;

pub struct CircuitStatement<Value: IValue> {
    pub components: IndexMap<&'static str, Box<dyn CircuitEval<Value>>>,
    /// The variable indices (addresses) of the output gates.
    pub output_addresses: Vec<M31Wrapper<Var>>,
    /// The values of the output gates.
    pub output_values: Vec<Var>,
    /// Preprocessed column ids in the exact order used by the prover's preprocessed trace.
    pub preprocessed_column_ids: Vec<PreProcessedColumnId>,
    /// Log size of each preprocessed column, in the same order as `preprocessed_column_ids`.
    pub preprocessed_column_log_sizes: Vec<u32>,
    /// The preprocessed trace root.
    pub preprocessed_root: HashValue<QM31>,
}
impl<Value: IValue> CircuitStatement<Value> {
    pub fn new(
        context: &mut Context<Value>,
        output_addresses: &[usize],
        output_values: &[QM31],
        preprocessed_column_ids: Vec<PreProcessedColumnId>,
        preprocessed_column_log_sizes: Vec<u32>,
        preprocessed_root: HashValue<QM31>,
    ) -> Self {
        let output_addresses = output_addresses
            .iter()
            .map(|&addr| M31Wrapper::new_unsafe(context.constant(addr.into())))
            .collect_vec();
        let output_values =
            output_values.iter().map(|value| Value::from_qm31(*value).guess(context)).collect_vec();
        Self {
            components: all_circuit_components(),
            output_addresses,
            output_values,
            preprocessed_column_ids,
            preprocessed_column_log_sizes,
            preprocessed_root,
        }
    }
}
impl<Value: IValue> Statement<Value> for CircuitStatement<Value> {
    fn claims_to_mix(&self, _context: &mut Context<Value>) -> Vec<Vec<Var>> {
        vec![self.output_values.clone()]
    }

    fn get_components(&self) -> &IndexMap<&'static str, Box<dyn CircuitEval<Value>>> {
        &self.components
    }

    fn public_logup_sum(
        &self,
        context: &mut Context<Value>,
        interaction_elements: [Var; 2],
    ) -> Var {
        let mut sum = context.zero();

        // Output gates public logup sum contribution.
        let gate_relation_id = context.constant(GATE_RELATION_ID.into());
        for (output_address, output_value) in zip_eq(&self.output_addresses, &self.output_values) {
            let [output_value_0, output_value_1, output_value_2, output_value_3] =
                Simd::unpack(context, &Simd::from_packed(vec![*output_value], 4))
                    .try_into()
                    .unwrap();
            let term = logup_use_term(
                context,
                &[
                    gate_relation_id,
                    *output_address.get(),
                    output_value_0,
                    output_value_1,
                    output_value_2,
                    output_value_3,
                ],
                interaction_elements,
            );
            sum = eval!(context, (sum) + (term));
        }

        sum
    }

    fn get_preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        self.preprocessed_column_ids.clone()
    }

    fn get_preprocessed_column_log_sizes(&self) -> Vec<u32> {
        self.preprocessed_column_log_sizes.clone()
    }

    fn get_preprocessed_root(&self, context: &mut Context<Value>) -> HashValue<Var> {
        HashValue(
            context.constant(self.preprocessed_root.0),
            context.constant(self.preprocessed_root.1),
        )
    }
}

pub fn all_circuit_components<Value: IValue>() -> IndexMap<&'static str, Box<dyn CircuitEval<Value>>>
{
    IndexMap::from([
        ("eq", Box::new(CircuitEqComponent {}) as Box<dyn CircuitEval<Value>>),
        ("qm31_ops", Box::new(CircuitQm31OpsComponent {}) as Box<dyn CircuitEval<Value>>),
        ("poseidon_gate", Box::new(CircuitPoseidonGateComponent {}) as Box<dyn CircuitEval<Value>>),
        ("m_31_to_u_32", Box::new(CircuitM31ToU32Component {}) as Box<dyn CircuitEval<Value>>),
        (
            "range_check_16",
            Box::new(CircuitRangeCheck16Component {}) as Box<dyn CircuitEval<Value>>,
        ),
    ])
}
