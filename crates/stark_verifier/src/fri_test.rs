use crate::channel::Channel;
use crate::fri::{fold_coset, validate_query_position_in_coset};
use crate::fri_proof::FriCommitProof;
use circuits::blake::HashValue;
use circuits::context::TraceContext;
use circuits::ivalue::qm31_from_u32s;
use circuits::ops::Guess;
use circuits::poseidon2_hasher::poseidon2_qm31;
use rstest::rstest;
use stwo::core::circle::Coset;
use stwo::core::fields::qm31::SecureField;
use stwo::core::fri::fold_coset as stwo_fold_coset;
use stwo::core::poly::line::LineDomain;
use stwo::core::utils::bit_reverse_index;

use super::fri_commit;

#[test]
fn test_fri_commit() {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(375224163, 1270824854, 44060607, 991529112);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    let commits = [
        (
            qm31_from_u32s(370372302, 356302922, 2040089875, 232934191),
            qm31_from_u32s(1279830905, 1240360672, 1788604172, 465814885),
        ),
        (
            qm31_from_u32s(1558212721, 609186473, 1554074721, 1956195301),
            qm31_from_u32s(1243917617, 135256448, 1193318416, 1792104990),
        ),
        (
            qm31_from_u32s(1017503040, 1411053946, 1805475392, 1906875756),
            qm31_from_u32s(2035075097, 617472393, 571220918, 1577790110),
        ),
        (
            qm31_from_u32s(1290083578, 670256590, 203247471, 492011214),
            qm31_from_u32s(353269841, 1619070080, 770215254, 1663098736),
        ),
    ];
    let last_layer_coef = qm31_from_u32s(1802004671, 1018373769, 131996621, 1575090881);

    let proof = FriCommitProof {
        layer_commitments: commits.iter().map(|(a, b)| HashValue(*a, *b)).collect(),
        last_layer_coefs: vec![last_layer_coef],
    };
    let proof_vars = proof.guess(&mut context);

    let alphas = fri_commit(&mut context, &mut channel, &proof_vars);
    assert_eq!(alphas.len(), 4);

    // Compute expected alphas using poseidon2_qm31 — must match the circuit.
    let zero = qm31_from_u32s(0, 0, 0, 0);
    let mut expected_digest = init_digest;
    for (i, (root0, root1)) in commits.iter().enumerate() {
        let s = poseidon2_qm31(expected_digest, *root0);
        expected_digest = poseidon2_qm31(s, *root1);
        let expected_alpha = poseidon2_qm31(expected_digest, zero);
        assert_eq!(context.get(alphas[i]), expected_alpha);
    }
    // After last_layer_coef absorption.
    expected_digest = poseidon2_qm31(expected_digest, last_layer_coef);
    assert_eq!(context.get(channel.digest()), expected_digest);

    context.validate_circuit();
}

#[test]
fn test_fold_coset() {
    let mut context = TraceContext::default();
    let coset_log_size = 3_u32;

    let coset_values_qm31: Vec<_> = (0..(1 << coset_log_size))
        .map(|i| qm31_from_u32s(4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3))
        .collect();
    let coset_values: Vec<_> = coset_values_qm31.iter().map(|x| context.constant(*x)).collect();

    let alpha_qm31 = qm31_from_u32s(98, 76, 54, 32);
    let mut alpha_pow = alpha_qm31;
    let mut alphas = Vec::with_capacity(coset_log_size as usize);
    for _ in 0..coset_log_size {
        alphas.push(context.constant(alpha_pow));
        alpha_pow = alpha_pow * alpha_pow;
    }

    let mut fold_domain = LineDomain::new(Coset::half_odds(coset_log_size));
    let mut twiddles_per_fold = Vec::with_capacity(coset_log_size as usize);
    for i in 0..coset_log_size {
        let twiddles_len = 1 << (coset_log_size - i - 1);
        let twiddles = (0..twiddles_len)
            .map(|k| {
                let j = 2 * k;
                let x = fold_domain.at(bit_reverse_index(j, fold_domain.log_size()));
                context.constant(SecureField::from(x.inverse()))
            })
            .collect::<Vec<_>>();
        twiddles_per_fold.push(twiddles);
        fold_domain = fold_domain.double();
    }

    let actual = fold_coset(&mut context, &coset_values, &twiddles_per_fold, &alphas);
    let expected = stwo_fold_coset(
        coset_values_qm31,
        LineDomain::new(Coset::half_odds(coset_log_size)),
        alpha_qm31,
    );

    assert_eq!(context.get(actual), expected);
    context.validate_circuit();
}

#[rstest]
#[case::success(true)]
#[case::failure(false)]
fn test_validate_query_position_in_coset(#[case] success: bool) {
    let mut context = TraceContext::default();
    let mut const_var = |value: u32| context.constant(qm31_from_u32s(value, 0, 0, 0));

    // 3 queries, layer step = 2 (hence coset size = 2^2).
    let fri_coset_per_query = vec![
        vec![const_var(10), const_var(11), const_var(12), const_var(13)],
        vec![const_var(20), const_var(21), const_var(22), const_var(23)],
        vec![const_var(30), const_var(31), const_var(32), const_var(33)],
    ];

    let bits = vec![
        vec![const_var(0), const_var(1), const_var(0)],
        vec![const_var(0), const_var(0), const_var(1)],
    ];

    let mut fri_data = vec![const_var(10), const_var(21), const_var(32)];
    if !success {
        fri_data[2] = const_var(33);
    }

    validate_query_position_in_coset(&mut context, &fri_coset_per_query, &fri_data, &bits);
    assert_eq!(context.is_circuit_valid(), success);
}
