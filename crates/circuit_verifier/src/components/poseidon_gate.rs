use circuits::poseidon2::{INTERNAL_DIAG, N_HALF_FULL_ROUNDS, N_STATE, RC_EXTERNAL, RC_INTERNAL};
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

fn apply_m4_circuit<Value: IValue>(context: &mut Context<Value>, x: [Var; 4]) -> [Var; 4] {
    let t0 = eval!(context, (x[0]) + (x[1]));
    let t02 = eval!(context, (t0) + (t0));
    let t1 = eval!(context, (x[2]) + (x[3]));
    let t12 = eval!(context, (t1) + (t1));
    let t2 = eval!(context, ((x[1]) + (x[1])) + (t1));
    let t3 = eval!(context, ((x[3]) + (x[3])) + (t0));
    let t4 = eval!(context, ((t12) + (t12)) + (t3));
    let t5 = eval!(context, ((t02) + (t02)) + (t2));
    let t6 = eval!(context, (t3) + (t5));
    let t7 = eval!(context, (t2) + (t4));
    [t6, t5, t7, t4]
}

fn apply_external_round_matrix_circuit<Value: IValue>(
    context: &mut Context<Value>,
    state: &mut [Var; N_STATE],
) {
    for i in 0..4 {
        let [a, b, c, d] = apply_m4_circuit(
            context,
            [state[4 * i], state[4 * i + 1], state[4 * i + 2], state[4 * i + 3]],
        );
        state[4 * i] = a;
        state[4 * i + 1] = b;
        state[4 * i + 2] = c;
        state[4 * i + 3] = d;
    }
    for j in 0..4 {
        let s = eval!(context, (((state[j]) + (state[j + 4])) + (state[j + 8])) + (state[j + 12]));
        for i in 0..4 {
            state[4 * i + j] = eval!(context, (state[4 * i + j]) + (s));
        }
    }
}

fn apply_internal_round_matrix_circuit<Value: IValue>(
    context: &mut Context<Value>,
    state: &mut [Var; N_STATE],
) {
    let mut sum = state[0];
    for &x in state.iter().skip(1) {
        sum = eval!(context, (sum) + (x));
    }
    let diags: [Var; N_STATE] =
        INTERNAL_DIAG.map(|d| context.constant(QM31::from(M31::from_u32_unchecked(d))));
    for (x, diag) in state.iter_mut().zip(diags) {
        let scaled = eval!(context, (*x) * (diag));
        *x = eval!(context, (scaled) + (sum));
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
        let mut state: [Var; N_STATE] = std::array::from_fn(|i| match i {
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

        apply_external_round_matrix_circuit(context, &mut state);

        let mut col_idx = 12usize;

        // First 4 full rounds.
        for rc_row in &RC_EXTERNAL[..N_HALF_FULL_ROUNDS] {
            let rcs: [Var; N_STATE] =
                rc_row.map(|rc| context.constant(QM31::from(M31::from_u32_unchecked(rc))));
            for (x, rc) in state.iter_mut().zip(rcs) {
                *x = eval!(context, (*x) + (rc));
            }
            let before = state;

            // x^2 step.
            for x in state.iter_mut() {
                let sq = eval!(context, (*x) * (*x));
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (sq) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }

            // x^4 step.
            for x in state.iter_mut() {
                let sq = eval!(context, (*x) * (*x));
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (sq) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }

            // x^5 = x^4 * x_before, external matrix, store witnesses.
            for (x, &bx) in state.iter_mut().zip(before.iter()) {
                *x = eval!(context, (*x) * (bx));
            }
            apply_external_round_matrix_circuit(context, &mut state);
            for x in state.iter_mut() {
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (*x) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }
        }

        // 14 partial rounds.
        for &rc_val in RC_INTERNAL.iter() {
            let rc = context.constant(QM31::from(M31::from_u32_unchecked(rc_val)));
            state[0] = eval!(context, (state[0]) + (rc));
            let s0 = state[0];

            let s2 = eval!(context, (s0) * (s0));
            let w = cols[col_idx];
            col_idx += 1;
            let c = eval!(context, (s2) - (w));
            acc.add_constraint(context, c);
            state[0] = w;

            let s4 = eval!(context, (state[0]) * (state[0]));
            let w = cols[col_idx];
            col_idx += 1;
            let c = eval!(context, (s4) - (w));
            acc.add_constraint(context, c);
            state[0] = w;

            let s5 = eval!(context, (state[0]) * (s0));
            let w = cols[col_idx];
            col_idx += 1;
            let c = eval!(context, (s5) - (w));
            acc.add_constraint(context, c);
            state[0] = w;

            apply_internal_round_matrix_circuit(context, &mut state);
            for x in state.iter_mut() {
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (*x) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }
        }

        // Last 4 full rounds.
        for rc_row in &RC_EXTERNAL[N_HALF_FULL_ROUNDS..] {
            let rcs: [Var; N_STATE] =
                rc_row.map(|rc| context.constant(QM31::from(M31::from_u32_unchecked(rc))));
            for (x, rc) in state.iter_mut().zip(rcs) {
                *x = eval!(context, (*x) + (rc));
            }
            let before = state;

            for x in state.iter_mut() {
                let sq = eval!(context, (*x) * (*x));
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (sq) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }

            for x in state.iter_mut() {
                let sq = eval!(context, (*x) * (*x));
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (sq) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }

            for (x, &bx) in state.iter_mut().zip(before.iter()) {
                *x = eval!(context, (*x) * (bx));
            }
            apply_external_round_matrix_circuit(context, &mut state);
            for x in state.iter_mut() {
                let w = cols[col_idx];
                col_idx += 1;
                let c = eval!(context, (*x) - (w));
                acc.add_constraint(context, c);
                *x = w;
            }
        }

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
