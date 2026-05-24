use crate::preprocessed::PreprocessedCircuit;
use circuits::circuit::{Add, Circuit, Eq, M31ToU32, Mul, PointwiseMul, Poseidon, Sub};
use expect_test::expect;
use itertools::Itertools;
use stwo::prover::backend::Column;
use stwo::prover::backend::simd::SimdBackend;

#[test]
fn test_preprocess_circuit() {
    let mut circuit = Circuit::default();
    circuit.add.push(Add { in0: 0, in1: 1, out: 2 });
    circuit.add.push(Add { in0: 3, in1: 4, out: 5 });
    circuit.sub.push(Sub { in0: 6, in1: 7, out: 8 });
    circuit.sub.push(Sub { in0: 9, in1: 10, out: 11 });
    circuit.mul.push(Mul { in0: 12, in1: 13, out: 14 });
    circuit.mul.push(Mul { in0: 15, in1: 16, out: 17 });
    circuit.pointwise_mul.push(PointwiseMul { in0: 18, in1: 19, out: 20 });
    circuit.pointwise_mul.push(PointwiseMul { in0: 21, in1: 22, out: 23 });
    circuit.eq.push(Eq { in0: 0, in1: 1 });
    circuit.eq.push(Eq { in0: 0, in1: 2 });
    for i in 0..16 {
        circuit.poseidon.push(Poseidon { in0: (i * 2) % 24, in1: (i * 2 + 1) % 24, out: 24 + i });
    }
    for i in 0..16 {
        circuit.m31_to_u32.push(M31ToU32 { input: 0, out: 40 + i });
    }
    circuit.n_vars = 56;

    let preprocessed_trace = PreprocessedCircuit::from_finalized_circuit(&circuit)
        .preprocessed_trace
        .get_trace::<SimdBackend>();

    let lengths = preprocessed_trace.iter().map(|column| column.values.len()).collect_vec();
    expect![[r#"
        [
            2,
            2,
            8,
            8,
            8,
            8,
            8,
            8,
            8,
            8,
            16,
            16,
            16,
            16,
            16,
            16,
            16,
            65536,
        ]
    "#]]
    .assert_debug_eq(&lengths);
}
