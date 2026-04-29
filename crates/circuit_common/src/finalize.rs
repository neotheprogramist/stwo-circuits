use crate::N_LANES;
use circuits::context::{Context, Var};
use circuits::eval;
use circuits::ivalue::{IValue, qm31_from_u32s};
use circuits::ops::{eq, output};
use rand_chacha::rand_core::{RngCore, SeedableRng};

fn pad_qm31_ops(context: &mut Context<impl IValue>) {
    let qm31_ops_n_rows = context.circuit.add.len()
        + context.circuit.sub.len()
        + context.circuit.mul.len()
        + context.circuit.pointwise_mul.len()
        + context
            .circuit
            .permutation
            .iter()
            .map(|p| p.inputs.len() + p.outputs.len())
            .sum::<usize>();

    let qm31_padding =
        std::cmp::max(qm31_ops_n_rows.next_power_of_two(), N_LANES) - qm31_ops_n_rows;
    let zero = context.zero();
    for _ in 0..qm31_padding {
        eval!(context, (zero) + (zero));
    }
}

fn pad_eq(context: &mut Context<impl IValue>) {
    let eq_n_rows = context.circuit.eq.len();
    let eq_padding = std::cmp::max(eq_n_rows.next_power_of_two(), N_LANES) - eq_n_rows;
    let zero = context.zero();
    for _ in 0..eq_padding {
        circuits::ops::eq(context, zero, zero);
    }
}

fn pad_poseidon(context: &mut Context<impl IValue>) {
    let n = context.circuit.poseidon.len();
    let padded = std::cmp::max(n.next_power_of_two().max(1), N_LANES);
    let zero = context.zero();
    for _ in n..padded {
        circuits::poseidon2::poseidon_gate(context, zero, zero);
    }
}

fn pad_m31_to_u32(context: &mut Context<impl IValue>) {
    let n_rows = context.circuit.m31_to_u32.len();
    let padded = std::cmp::max(n_rows.next_power_of_two(), N_LANES);
    let zero = context.zero();
    for _ in n_rows..padded {
        circuits::blake::m31_to_u32(context, zero);
    }
}

fn hash_constants(context: &mut Context<impl IValue>) -> Var {
    let constants: Vec<_> = context.constants().values().copied().collect();
    let zero = context.zero();
    if constants.is_empty() {
        return circuits::poseidon2::poseidon_gate(context, zero, zero);
    }
    let first = constants[0];
    let second = if constants.len() > 1 { constants[1] } else { zero };
    let mut state = circuits::poseidon2::poseidon_gate(context, first, second);
    for &c in constants.iter().skip(2) {
        state = circuits::poseidon2::poseidon_gate(context, state, c);
    }
    state
}

/// Finalizes the context by appending gates to the context for:
/// - Hashing the constants.
/// - Hashing the outputs.
/// - Padding the components to a power of two.
// TODO(Gali): Have it under a trait.
// TODO(Ilya): Make it pub(crate).
pub fn finalize_context(context: &mut Context<impl IValue>) {
    let hash = hash_constants(context);
    output(context, hash);

    // Padding the components to a power of two.
    pad_eq(context);
    pad_qm31_ops(context);
    pad_poseidon(context);
    pad_m31_to_u32(context);
}

/// Adds ZK blinding to the circuit by adding random values to the qm31_ops and eq components.
pub fn add_zk_blinding(context: &mut Context<impl IValue>, seed_bytes: [u8; 32], n_padding: usize) {
    let mut rng = rand_chacha::ChaCha20Rng::from_seed(seed_bytes);
    for _ in 0..n_padding {
        // Note that we don't use the guess function here because we want to be able to run this
        // function after finalize_guessed_vars.
        let value1 = qm31_from_u32s(rng.next_u32(), rng.next_u32(), rng.next_u32(), rng.next_u32());
        let var1 = context.new_var(IValue::from_qm31(value1));
        context.circuit.add.push(circuits::circuit::Add {
            in0: var1.idx,
            in1: context.zero().idx,
            out: var1.idx,
        });
        let value2 = qm31_from_u32s(rng.next_u32(), rng.next_u32(), rng.next_u32(), rng.next_u32());
        let var2 = context.new_var(IValue::from_qm31(value2));
        context.circuit.add.push(circuits::circuit::Add {
            in0: context.zero().idx,
            in1: var2.idx,
            out: var2.idx,
        });
        eval!(context, (var1) + (var2));

        let value3 = qm31_from_u32s(rng.next_u32(), rng.next_u32(), rng.next_u32(), rng.next_u32());
        let var3 = context.new_var(IValue::from_qm31(value3));
        context.circuit.add.push(circuits::circuit::Add {
            in0: var3.idx,
            in1: context.zero().idx,
            out: var3.idx,
        });
        eq(context, var3, var3);
    }
}
