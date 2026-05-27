use num_traits::One;
use rstest::rstest;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;

use crate::merkle::{
    AuthPath, AuthPaths, decommit_eval_domain_samples, hash_leaf_m31s, hash_leaf_qm31, hash_node,
    verify_merkle_path,
};
use crate::oods::EvalDomainSamples;
use circuits::blake::HashValue;
use circuits::context::TraceContext;
use circuits::ivalue::qm31_from_u32s;
use circuits::ops::Guess;
use circuits::poseidon2_hasher::poseidon2_qm31;
use circuits::wrappers::M31Wrapper;

/// Native (non-circuit) Poseidon2 node hash — must match `hash_node` in `merkle.rs`.
fn hash_node_qm31(left: HashValue<QM31>, right: HashValue<QM31>) -> HashValue<QM31> {
    let s = poseidon2_qm31(left.0, left.1);
    let s = poseidon2_qm31(s, right.0);
    let h1 = poseidon2_qm31(s, right.1);
    HashValue(s, h1)
}

/// Native leaf hash for an empty leaf (no M31 values) — matches `hash_leaf_m31s(&[])`.
///
/// With no inputs, the sponge state stays at zero:
/// `h0 = 0`, `h1 = poseidon2(0, 0)`.
fn hash_empty_leaf() -> HashValue<QM31> {
    let zero = QM31::default();
    HashValue(zero, poseidon2_qm31(zero, zero))
}

/// Native leaf hash for a single M31 value — matches `hash_leaf_m31s(&[value])`.
///
/// Packs `value` into the first M31 component of a QM31 (others are zero),
/// absorbs it: `state = poseidon2(0, qm31(value,0,0,0))`,
/// then finalizes: `h0 = state`, `h1 = poseidon2(state, 0)`.
fn hash_leaf(value: M31) -> HashValue<QM31> {
    let zero = QM31::default();
    let packed = qm31_from_u32s(value.0, 0, 0, 0);
    let state = poseidon2_qm31(zero, packed);
    HashValue(state, poseidon2_qm31(state, zero))
}

#[test]
fn hash_leaf_m31s_regression() {
    let mut context = TraceContext::default();

    // Single M31 value → packed as QM31(value, 0, 0, 0).
    let values = [M31Wrapper::from(M31::from(1641251221)).guess(&mut context)];
    let hash = hash_leaf_m31s(&mut context, &values);

    let zero = QM31::default();
    let packed1 = qm31_from_u32s(1641251221, 0, 0, 0);
    let state1 = poseidon2_qm31(zero, packed1);
    assert_eq!(context.get(hash.0), state1);
    assert_eq!(context.get(hash.1), poseidon2_qm31(state1, zero));

    // Four M31 values → one packed QM31.
    let values = [1, 1641251221, 1176667027, 568581975]
        .map(|v: u32| M31Wrapper::from(M31::from(v)))
        .guess(&mut context);
    let hash = hash_leaf_m31s(&mut context, &values);

    let packed4 = qm31_from_u32s(1, 1641251221, 1176667027, 568581975);
    let state4 = poseidon2_qm31(zero, packed4);
    assert_eq!(context.get(hash.0), state4);
    assert_eq!(context.get(hash.1), poseidon2_qm31(state4, zero));

    context.validate_circuit();
}

#[test]
fn hash_leaf_qm31_regression() {
    let mut context = TraceContext::default();

    let input = qm31_from_u32s(106879334, 2000582330, 760086299, 1036436096);
    let value = input.guess(&mut context);
    let hash = hash_leaf_qm31(&mut context, value);

    // poseidon_absorb(&[value]): state = poseidon2(0, input), h1 = poseidon2(state, 0).
    let zero = QM31::default();
    let state = poseidon2_qm31(zero, input);
    assert_eq!(context.get(hash.0), state);
    assert_eq!(context.get(hash.1), poseidon2_qm31(state, zero));

    context.validate_circuit();
}

#[test]
fn hash_node_regression() {
    let mut context = TraceContext::default();

    let left = HashValue(
        qm31_from_u32s(1206199574, 725559475, 484842011, 871283881),
        qm31_from_u32s(1827188342, 1597668943, 763527182, 238830106),
    )
    .guess(&mut context);
    let right = HashValue(
        qm31_from_u32s(314780017, 161087059, 1415631711, 1712686715),
        qm31_from_u32s(873946371, 993675704, 1750257287, 1496441219),
    )
    .guess(&mut context);

    let hash = hash_node(&mut context, left, right);

    // s = poseidon2(left.0, left.1); s = poseidon2(s, right.0); h1 = poseidon2(s, right.1)
    let s = poseidon2_qm31(
        qm31_from_u32s(1206199574, 725559475, 484842011, 871283881),
        qm31_from_u32s(1827188342, 1597668943, 763527182, 238830106),
    );
    let s = poseidon2_qm31(s, qm31_from_u32s(314780017, 161087059, 1415631711, 1712686715));
    let h1 = poseidon2_qm31(s, qm31_from_u32s(873946371, 993675704, 1750257287, 1496441219));
    assert_eq!(context.get(hash.0), s);
    assert_eq!(context.get(hash.1), h1);

    context.validate_circuit();
}

#[rstest]
#[case::success(false, false)]
#[case::wrong_bit(true, false)]
#[case::wrong_root(false, true)]
fn test_merkle_path(#[case] wrong_bit: bool, #[case] wrong_root: bool) {
    let mut context = TraceContext::default();

    let leaf_val = HashValue(qm31_from_u32s(1, 2, 3, 4), qm31_from_u32s(5, 6, 7, 8));
    let auth_path0 = HashValue(qm31_from_u32s(9, 10, 11, 12), qm31_from_u32s(13, 14, 15, 16));
    let auth_path1 = HashValue(qm31_from_u32s(17, 18, 19, 20), qm31_from_u32s(21, 22, 23, 24));
    let auth_path2 = HashValue(qm31_from_u32s(25, 26, 27, 28), qm31_from_u32s(29, 30, 31, 32));
    let auth_path3 = HashValue(qm31_from_u32s(33, 34, 35, 36), qm31_from_u32s(37, 38, 39, 40));
    let auth_path4 = HashValue(qm31_from_u32s(41, 42, 43, 44), qm31_from_u32s(45, 46, 47, 48));
    let auth_path = AuthPath(vec![auth_path0, auth_path1, auth_path2, auth_path3, auth_path4])
        .guess(&mut context);

    let leaf = HashValue(leaf_val.0, leaf_val.1).guess(&mut context);
    let bits = vec![
        qm31_from_u32s(if wrong_bit { 0 } else { 1 }, 0, 0, 0),
        qm31_from_u32s(1, 0, 0, 0),
        qm31_from_u32s(0, 0, 0, 0),
        qm31_from_u32s(0, 0, 0, 0),
        qm31_from_u32s(1, 0, 0, 0),
    ]
    .guess(&mut context);

    // Compute root using the Poseidon2 node hash, mirroring the bit pattern.
    // bits = [1, 1, 0, 0, 1] → for bit=1: sibling is left, for bit=0: node is left.
    let mut node = leaf_val;
    node = hash_node_qm31(auth_path0, node); // bit=1 → auth_path0 is left
    node = hash_node_qm31(auth_path1, node); // bit=1 → auth_path1 is left
    node = hash_node_qm31(node, auth_path2); // bit=0 → node is left
    node = hash_node_qm31(node, auth_path3); // bit=0 → node is left
    node = hash_node_qm31(auth_path4, node); // bit=1 → auth_path4 is left
    if wrong_root {
        node.0 += qm31_from_u32s(0, 0, 1, 0);
    }
    let root = HashValue(node.0, node.1).guess(&mut context);

    verify_merkle_path(&mut context, leaf, &bits, root, &auth_path);
    let success = !wrong_bit && !wrong_root;
    assert_eq!(context.is_circuit_valid(), success);
}

#[rstest]
#[case::success(None, false)]
#[case::wrong_bit(None, true)]
#[case::wrong_root0(Some(0), false)]
#[case::wrong_root1(Some(1), false)]
#[case::wrong_root2(Some(2), false)]
#[case::wrong_root3(Some(3), false)]
fn test_decommit_eval_domain_samples(#[case] wrong_root: Option<usize>, #[case] wrong_bit: bool) {
    use circuits::context::Var;

    let mut context = TraceContext::default();

    // 1 preprocessed trace with a single column + 3 traces with no columns.
    let eval_domain_samples =
        EvalDomainSamples::from_m31s(vec![vec![vec![M31::from(1)]], vec![], vec![], vec![]]);

    // 2 traces with no columns.
    let column_log_sizes: [Vec<Var>; 2] = [vec![], vec![]];

    let auth_path_val0 = HashValue(qm31_from_u32s(1, 2, 3, 4), qm31_from_u32s(5, 6, 7, 8));
    let auth_path_val1 = HashValue(qm31_from_u32s(9, 10, 11, 12), qm31_from_u32s(13, 14, 15, 16));
    let auth_paths = AuthPaths {
        data: vec![
            vec![AuthPath(vec![auth_path_val0])],
            vec![AuthPath(vec![auth_path_val1])],
            vec![AuthPath(vec![auth_path_val1])],
            vec![AuthPath(vec![auth_path_val1])],
        ],
    };
    let bits: Vec<Vec<QM31>> = vec![vec![(if wrong_bit { 1 } else { 0 }).into()]];

    let root0 = hash_node_qm31(hash_leaf(M31::from(1)), auth_path_val0);
    let root1 = hash_node_qm31(hash_empty_leaf(), auth_path_val1);

    let mut roots = [root0, root1, root1, root1];
    if let Some(wrong_root) = wrong_root {
        roots[wrong_root].1 += QM31::one();
    }

    let eval_domain_samples_vars = eval_domain_samples.guess(&mut context);
    let auth_paths_vars = auth_paths.guess(&mut context);
    let bits_vars = bits.guess(&mut context);
    let roots_vars = roots.guess(&mut context);
    let n_queries = 1;
    decommit_eval_domain_samples(
        &mut context,
        n_queries,
        &column_log_sizes,
        &eval_domain_samples_vars,
        &auth_paths_vars,
        &bits_vars,
        &roots_vars,
    );

    let success = wrong_root.is_none() && !wrong_bit;
    assert_eq!(context.is_circuit_valid(), success);
}
