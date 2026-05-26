use circuits::poseidon2::{N_STATE, Poseidon2Backend, poseidon2_permutation};
use circuits::{
    context::{Context, Var},
    ivalue::IValue,
    *,
};
use circuits_stark_verifier::constraint_eval::{
    CircuitEval, ComponentDataTrait, CompositionConstraintAccumulator, RelationUse,
};
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

const N_TRACE_COLUMNS: usize = 662;
const N_INTERACTION_COLUMNS: usize = 8;
const RELATION_USES_PER_ROW: [RelationUse; 1] = [RelationUse { relation_id: "gate", uses: 3 }];

pub struct Component {}

struct VerifierPoseidonBackend<'a, Value: IValue> {
    context: &'a mut Context<Value>,
    acc: &'a mut CompositionConstraintAccumulator,
    cols: &'a [Var],
    col_idx: usize,
}

impl<Value: IValue> Poseidon2Backend for VerifierPoseidonBackend<'_, Value> {
    type Elem = Var;

    fn zero(&mut self) -> Self::Elem {
        self.context.zero()
    }

    fn constant(&mut self, value: u32) -> Self::Elem {
        self.context.constant(QM31::from(M31::from_u32_unchecked(value)))
    }

    fn add(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem {
        eval!(self.context, (a) + (b))
    }

    fn mul(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem {
        eval!(self.context, (a) * (b))
    }

    fn witness(&mut self, value: Self::Elem) -> Self::Elem {
        let witness = self.cols[self.col_idx];
        self.col_idx += 1;
        let constraint = eval!(self.context, (value) - (witness));
        self.acc.add_constraint(self.context, constraint);
        witness
    }
}

impl<Value: IValue> CircuitEval<Value> for Component {
    fn name(&self) -> String {
        "poseidon_gate".to_string()
    }

    fn trace_columns(&self) -> usize {
        N_TRACE_COLUMNS
    }

    fn interaction_columns(&self) -> usize {
        N_INTERACTION_COLUMNS
    }

    fn evaluate(
        &self,
        context: &mut Context<Value>,
        component_data: &dyn ComponentDataTrait<Value>,
        acc: &mut CompositionConstraintAccumulator,
    ) {
        let cols = component_data.trace_columns();

        let in0_l0 = cols[0];
        let in0_l1 = cols[1];
        let in0_l2 = cols[2];
        let in0_l3 = cols[3];
        let in1_l0 = cols[4];
        let in1_l1 = cols[5];
        let in1_l2 = cols[6];
        let in1_l3 = cols[7];
        let out_l0 = cols[8];
        let out_l1 = cols[9];
        let out_l2 = cols[10];
        let out_l3 = cols[11];

        let in0_addr = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_in0_address".to_owned(),
        });
        let in1_addr = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_in1_address".to_owned(),
        });
        let out_addr = acc.get_preprocessed_column(&PreProcessedColumnId {
            id: "poseidon_out_address".to_owned(),
        });
        let out_mults = acc
            .get_preprocessed_column(&PreProcessedColumnId { id: "poseidon_out_mults".to_owned() });

        let zero = context.zero();
        let state: [Var; N_STATE] = std::array::from_fn(|i| match i {
            0 => in0_l0,
            1 => in1_l0,
            2 => in0_l1,
            3 => in0_l2,
            4 => in0_l3,
            5 => in1_l1,
            6 => in1_l2,
            7 => in1_l3,
            _ => zero,
        });

        let state = {
            let mut backend =
                VerifierPoseidonBackend { context, acc, cols, col_idx: 12usize };
            let state = poseidon2_permutation(&mut backend, state);
            assert_eq!(
                backend.col_idx, N_TRACE_COLUMNS,
                "wrong Poseidon verifier column count: {}",
                backend.col_idx
            );
            state
        };

        // Final output constraints.
        let c0 = eval!(context, (out_l0) - (state[0]));
        acc.add_constraint(context, c0);
        let c1 = eval!(context, (out_l1) - (state[1]));
        acc.add_constraint(context, c1);
        let c2 = eval!(context, (out_l2) - (state[2]));
        acc.add_constraint(context, c2);
        let c3 = eval!(context, (out_l3) - (state[3]));
        acc.add_constraint(context, c3);

        // Logup: use in0, use in1, yield out.
        let gate_id = eval!(context, 378353459);
        let tuple_in0 = &[
            gate_id,
            eval!(context, in0_addr),
            eval!(context, in0_l0),
            eval!(context, in0_l1),
            eval!(context, in0_l2),
            eval!(context, in0_l3),
        ];
        acc.add_to_relation(context, context.one(), tuple_in0);

        let tuple_in1 = &[
            gate_id,
            eval!(context, in1_addr),
            eval!(context, in1_l0),
            eval!(context, in1_l1),
            eval!(context, in1_l2),
            eval!(context, in1_l3),
        ];
        acc.add_to_relation(context, context.one(), tuple_in1);

        let tuple_out = &[
            gate_id,
            eval!(context, out_addr),
            eval!(context, out_l0),
            eval!(context, out_l1),
            eval!(context, out_l2),
            eval!(context, out_l3),
        ];
        let num_out = eval!(context, -(out_mults));
        acc.add_to_relation(context, num_out, tuple_out);
    }

    fn relation_uses_per_row(&self) -> &[RelationUse] {
        &RELATION_USES_PER_ROW
    }
}
