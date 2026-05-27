use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;

use crate::context::Context;
use crate::ivalue::qm31_from_u32s;
use crate::ops::{Guess, eq, guess};
use crate::poseidon2::{
    N_STATE, RATE, poseidon_gate, poseidon2_absorb_circuit, poseidon2_hash_two,
    poseidon2_permutation_circuit, poseidon2_sponge_circuit, poseidon2_value_from_state,
    poseidon2_value_qm31,
};

fn run_poseidon_gate(a: u32, b: u32) -> QM31 {
    let mut ctx = Context::<QM31>::default();
    let va = qm31_from_u32s(a, 0, 0, 0).guess(&mut ctx);
    let vb = qm31_from_u32s(b, 0, 0, 0).guess(&mut ctx);
    let out = poseidon_gate(&mut ctx, va, vb);
    ctx.get(out)
}

// Kakarot labs test vectors
#[test]
fn test_poseidon_gate_hash_vectors() {
    // hash(a, b) = state[0] after Poseidon2 with initial state=[a,b,0,...,0]
    assert_eq!(run_poseidon_gate(0, 0).0.0, M31::from_u32_unchecked(1183174448), "hash(0,0)");
    assert_eq!(run_poseidon_gate(1, 0).0.0, M31::from_u32_unchecked(846768668), "hash(1,0)");
    assert_eq!(run_poseidon_gate(0, 1).0.0, M31::from_u32_unchecked(1854499991), "hash(0,1)");
    assert_eq!(run_poseidon_gate(1, 2).0.0, M31::from_u32_unchecked(1975699496), "hash(1,2)");
    assert_eq!(
        run_poseidon_gate(100, 200).0.0,
        M31::from_u32_unchecked(844495285),
        "hash(100,200)"
    );
    // 2147483647 = p = 0 in M31, so hash(p,p) must equal hash(0,0)
    assert_eq!(
        run_poseidon_gate(2147483647, 2147483647).0.0,
        M31::from_u32_unchecked(1183174448),
        "hash(p,p)"
    );
}

#[test]
fn test_poseidon_gate_qm31_differs_from_m31() {
    // QM31(5, 0, 0, 0) and QM31(X, 0, 0, 0) — same as Kakarot's hash(5, X)
    let pure_m31 = run_poseidon_gate(5, 42);

    // QM31(5, 99, 0, 0) — non-zero higher limb → must give different result
    let mut ctx = Context::<QM31>::default();
    let va = qm31_from_u32s(5, 99, 0, 0).guess(&mut ctx);
    let vb = qm31_from_u32s(42, 0, 0, 0).guess(&mut ctx);
    let out = poseidon_gate(&mut ctx, va, vb);
    let qm31_result = ctx.get(out);

    assert_ne!(pure_m31, qm31_result, "QM31 with non-zero limbs must differ from pure M31");
}

#[test]
fn test_poseidon_gate_full_qm31_matches_native() {
    let a = qm31_from_u32s(5, 99, 123, 456);
    let b = qm31_from_u32s(42, 7, 8, 9);
    let [s0, s1, s2, s3] = poseidon2_value_qm31(a, b);
    let expected = qm31_from_u32s(s0.0, s1.0, s2.0, s3.0);

    let mut ctx = Context::<QM31>::default();
    let va = a.guess(&mut ctx);
    let vb = b.guess(&mut ctx);
    let out = poseidon_gate(&mut ctx, va, vb);

    assert_eq!(ctx.get(out), expected);
}

#[test]
fn test_poseidon2_hash_two_7_42() {
    let mut context = Context::default();
    let a = qm31_from_u32s(7, 0, 0, 0).guess(&mut context);
    let b = qm31_from_u32s(42, 0, 0, 0).guess(&mut context);

    let out = poseidon2_hash_two(&mut context, a, b);
    let expected = guess(&mut context, qm31_from_u32s(430726115, 0, 0, 0));
    eq(&mut context, out, expected);

    context.finalize_guessed_vars();
    assert!(context.is_circuit_valid());
}

#[test]
fn test_absorb_circuit_matches_native() {
    let state_vals: [u32; N_STATE] = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let block_vals: [u32; RATE] = [10, 20, 30, 40, 50, 60, 70, 80];

    // Native: state[0..RATE] += block, then permutation
    let mut native = state_vals;
    for i in 0..RATE {
        native[i] = ((native[i] as u64 + block_vals[i] as u64) % 0x7FFF_FFFF) as u32;
    }
    let native = poseidon2_value_from_state(native);

    // Circuit
    let mut ctx = Context::<QM31>::default();
    let state_vars: [_; N_STATE] =
        std::array::from_fn(|i| qm31_from_u32s(state_vals[i], 0, 0, 0).guess(&mut ctx));
    let block_vars: [_; RATE] =
        std::array::from_fn(|i| qm31_from_u32s(block_vals[i], 0, 0, 0).guess(&mut ctx));
    let out = poseidon2_absorb_circuit(&mut ctx, state_vars, block_vars);

    for i in 0..N_STATE {
        assert_eq!(ctx.get(out[i]).0.0.0, native[i], "state[{i}] mismatch");
    }
}

#[test]
fn test_permutation_circuit_matches_native() {
    let input: [u32; N_STATE] = [7, 42, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];

    // Native
    let native = poseidon2_value_from_state(input);

    // Circuit
    let mut ctx = Context::<QM31>::default();
    let state_vars: [_; N_STATE] =
        std::array::from_fn(|i| qm31_from_u32s(input[i], 0, 0, 0).guess(&mut ctx));
    let out = poseidon2_permutation_circuit(&mut ctx, state_vars);

    for i in 0..N_STATE {
        let circuit_val = ctx.get(out[i]).0.0.0;
        assert_eq!(circuit_val, native[i], "state[{i}] mismatch");
    }
}

#[test]
fn test_sponge_circuit_matches_native() {
    // 3 blocks of RATE=8 bytes each
    let blocks_vals: [[u32; RATE]; 3] =
        [[1, 2, 3, 4, 5, 6, 7, 8], [9, 10, 11, 12, 13, 14, 15, 16], [100, 200, 0, 0, 0, 0, 0, 0]];

    // Native sponge: start from zero state, absorb each block
    let mut native = [0u32; N_STATE];
    for block in &blocks_vals {
        for i in 0..RATE {
            native[i] = ((native[i] as u64 + block[i] as u64) % 0x7FFF_FFFF) as u32;
        }
        native = poseidon2_value_from_state(native);
    }

    // Circuit sponge
    let mut ctx = Context::<QM31>::default();
    let block_vars: Vec<[_; RATE]> = blocks_vals
        .iter()
        .map(|block| std::array::from_fn(|i| qm31_from_u32s(block[i], 0, 0, 0).guess(&mut ctx)))
        .collect();
    let out = poseidon2_sponge_circuit(&mut ctx, &block_vars);

    for i in 0..N_STATE {
        assert_eq!(ctx.get(out[i]).0.0.0, native[i], "state[{i}] mismatch");
    }
}
