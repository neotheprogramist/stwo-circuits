use circuits::blake::HashValue;
use indexmap::IndexMap;
use num_traits::One;
use stwo::core::fields::m31::M31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use super::simple_air::FIB_SEQUENCE_LENGTH;
use crate::simple_air::{FIB_PREPROCESSED_COLUMNS, LOG_SIZE_LONG, LOG_SIZE_SHORT};
use circuits::context::{Context, Var};
use circuits::eval;
use circuits::ivalue::{IValue, qm31_from_u32s};
use circuits::ops::div;
use circuits_stark_verifier::constraint_eval::RelationUse;
use circuits_stark_verifier::constraint_eval::{
    CircuitEval, ComponentDataTrait, CompositionConstraintAccumulator,
};
use circuits_stark_verifier::logup::combine_term;
use circuits_stark_verifier::statement::Statement;

/// Log sizes of the enabled components in [`SimpleStatement`].
/// The stwo prover in `create_proof` runs with an additional disabled component (see
/// [`COMPONENT_ENABLE_BITS`]); the disabled slot has log size `0` and is filled in by
/// `pad_disabled` during channel mixing.
pub const COMPONENT_LOG_SIZES: [u32; 2] = [LOG_SIZE_LONG, LOG_SIZE_SHORT];
pub const COMPONENT_ENABLE_BITS: [bool; 3] = [true, true, false];

pub struct SimpleStatement<Value: IValue> {
    components: IndexMap<&'static str, Box<dyn CircuitEval<Value>>>,
}

impl<Value: IValue> Default for SimpleStatement<Value> {
    fn default() -> Self {
        Self {
            components: IndexMap::from([
                (
                    "squared_fibonacci_long",
                    Box::new(SquaredFibonacciComponent {
                        preprocessed_column_id: PreProcessedColumnId {
                            id: "row_const_long".to_string(),
                        },
                    }) as Box<dyn CircuitEval<Value>>,
                ),
                (
                    "squared_fibonacci_short",
                    Box::new(SquaredFibonacciComponent {
                        preprocessed_column_id: PreProcessedColumnId {
                            id: "row_const_short".to_string(),
                        },
                    }) as Box<dyn CircuitEval<Value>>,
                ),
            ]),
        }
    }
}

pub struct SquaredFibonacciComponent {
    pub preprocessed_column_id: PreProcessedColumnId,
}
impl<Value: IValue> CircuitEval<Value> for SquaredFibonacciComponent {
    fn name(&self) -> String {
        "squared_fibonacci".to_string()
    }

    fn trace_columns(&self) -> usize {
        4
    }

    fn interaction_columns(&self) -> usize {
        8
    }

    fn relation_uses_per_row(&self) -> &[RelationUse] {
        &[RelationUse { relation_id: "fib_relation", uses: 3 }]
    }

    fn evaluate(
        &self,
        context: &mut Context<Value>,
        component_data: &dyn ComponentDataTrait<Value>,
        acc: &mut CompositionConstraintAccumulator,
    ) {
        let const_val = acc.get_preprocessed_column(&self.preprocessed_column_id);
        let [a, b, c, d] = *component_data.trace_columns() else {
            panic!("Expected 4 trace columns")
        };

        // Constraints.
        let constraint0_val = eval!(context, (c) - ((((a) * (a)) + ((b) * (b))) + (const_val)));
        acc.add_constraint(context, constraint0_val);

        let constraint1_val = eval!(context, (d) - ((((b) * (b)) + ((c) * (c))) + (const_val)));
        acc.add_constraint(context, constraint1_val);

        // Logup constraint.
        acc.add_to_relation(context, context.one(), &[c, d]);
        acc.add_to_relation(context, context.one(), &[c, d]);
        acc.add_to_relation(context, context.one(), &[c, d]);
    }
}

fn squared_fibonacci_public_logup_sum(
    context: &mut Context<impl IValue>,
    interaction_elements: [Var; 2],
    log_n_instances: u32,
) -> Var {
    let mut sum = context.zero();
    for j in 0..(1 << log_n_instances) {
        let mut a: M31 = M31::one();
        let mut b: M31 = j.into();
        for _ in 0..(FIB_SEQUENCE_LENGTH - 2) {
            (a, b) = (b, a * a + b * b + M31::from(j));
        }
        let elements = [context.constant(a.into()), context.constant(b.into())];
        let denom1 = combine_term(context, &elements, interaction_elements);

        let denom = eval!(context, (denom1) * (denom1));
        let numerator = eval!(context, (denom1) + (denom1));

        let frac0 = div(context, numerator, denom);
        let frac1 = div(context, context.one(), denom1);
        let frac = eval!(context, (frac0) + (frac1));

        // Note that the sum is negated because we want to use the values that are yielded in
        // the witness.
        sum = eval!(context, (sum) - (frac));
    }
    sum
}

impl<Value: IValue> Statement<Value> for SimpleStatement<Value> {
    fn claims_to_mix(&self, _context: &mut Context<Value>) -> Vec<Vec<Var>> {
        vec![vec![]]
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

        for log_n_instances in COMPONENT_LOG_SIZES {
            let fib_logup_sum =
                squared_fibonacci_public_logup_sum(context, interaction_elements, log_n_instances);
            sum = eval!(context, (sum) + (fib_logup_sum));
        }
        sum
    }

    fn get_preprocessed_column_ids(&self) -> Vec<PreProcessedColumnId> {
        FIB_PREPROCESSED_COLUMNS
            .iter()
            .map(|id| PreProcessedColumnId { id: id.to_string() })
            .collect()
    }

    fn get_preprocessed_column_log_sizes(&self) -> Vec<u32> {
        vec![LOG_SIZE_SHORT, LOG_SIZE_LONG]
    }

    fn get_preprocessed_root(&self, context: &mut Context<Value>) -> HashValue<Var> {
        HashValue(
            context.constant(qm31_from_u32s(454922211, 1076832436, 653013005, 1774755757)),
            context.constant(qm31_from_u32s(1225142408, 790639217, 528131279, 363891668)),
        )
    }
}
