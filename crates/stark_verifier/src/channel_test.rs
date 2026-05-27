use rstest::rstest;

use circuits::blake::HashValue;
use circuits::context::TraceContext;
use circuits::ivalue::qm31_from_u32s;
use circuits::poseidon2_hasher::poseidon2_qm31;

use super::Channel;

#[test]
fn test_mix_commitment() {
    let mut context = TraceContext::default();

    let mut channel = Channel::new(&mut context);
    let root0 = HashValue(
        context.new_var(qm31_from_u32s(637418335, 1672023491, 980858689, 607764934)),
        context.new_var(qm31_from_u32s(386900718, 430556311, 1187803054, 669301442)),
    );
    let root1 = HashValue(
        context.new_var(qm31_from_u32s(1477561267, 1244239078, 1979857528, 1316512771)),
        context.new_var(qm31_from_u32s(490980261, 2016799283, 79573118, 1350641448)),
    );
    channel.mix_commitment(&mut context, root0);
    let digest0 = channel.digest;
    channel.mix_commitment(&mut context, root1);
    let digest1 = channel.digest;

    // Verify expected Poseidon2 values:
    // digest0 = poseidon2(poseidon2(0, root0.0), root0.1)
    let expected_d0 = poseidon2_qm31(
        poseidon2_qm31(
            qm31_from_u32s(0, 0, 0, 0),
            qm31_from_u32s(637418335, 1672023491, 980858689, 607764934),
        ),
        qm31_from_u32s(386900718, 430556311, 1187803054, 669301442),
    );
    assert_eq!(context.get(digest0), expected_d0);

    // digest1 = poseidon2(poseidon2(expected_d0, root1.0), root1.1)
    let expected_d1 = poseidon2_qm31(
        poseidon2_qm31(expected_d0, qm31_from_u32s(1477561267, 1244239078, 1979857528, 1316512771)),
        qm31_from_u32s(490980261, 2016799283, 79573118, 1350641448),
    );
    assert_eq!(context.get(digest1), expected_d1);

    context.validate_circuit();
}

#[test]
fn test_mix_qm31s() {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(266526289, 1341429509, 1126614795, 1001621831);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    let felts = [
        context.new_var(qm31_from_u32s(1, 0, 0, 0)),
        context.new_var(qm31_from_u32s(485399786, 1255952693, 1939438763, 1561715227)),
        context.new_var(qm31_from_u32s(1757357815, 8864493, 674769946, 1715431414)),
    ];
    channel.mix_qm31s(&mut context, felts);

    // Compute expected: chain of poseidon2 calls
    let mut expected = init_digest;
    expected = poseidon2_qm31(expected, qm31_from_u32s(1, 0, 0, 0));
    expected =
        poseidon2_qm31(expected, qm31_from_u32s(485399786, 1255952693, 1939438763, 1561715227));
    expected = poseidon2_qm31(expected, qm31_from_u32s(1757357815, 8864493, 674769946, 1715431414));

    assert_eq!(context.get(channel.digest), expected);
    assert_eq!(channel.n_draws, 0);

    context.validate_circuit();
}

#[test]
fn test_draw_qm31() {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(800533588, 1994201536, 2099095392, 678020158);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    let res = channel.draw_qm31(&mut context);
    let expected = poseidon2_qm31(init_digest, qm31_from_u32s(0, 0, 0, 0));
    assert_eq!(context.get(res), expected);

    let res2 = channel.draw_qm31(&mut context);
    let expected2 = poseidon2_qm31(init_digest, qm31_from_u32s(1, 0, 0, 0));
    assert_eq!(context.get(res2), expected2);

    context.validate_circuit();
}

#[test]
fn test_draw_two_qm31s() {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(800533588, 1994201536, 2099095392, 678020158);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    let res = channel.draw_two_qm31s(&mut context);
    let expected0 = poseidon2_qm31(init_digest, qm31_from_u32s(0, 0, 0, 0));
    let expected1 = poseidon2_qm31(init_digest, qm31_from_u32s(1, 0, 0, 0));
    assert_eq!(context.get(res[0]), expected0);
    assert_eq!(context.get(res[1]), expected1);

    let res2 = channel.draw_two_qm31s(&mut context);
    let expected2 = poseidon2_qm31(init_digest, qm31_from_u32s(2, 0, 0, 0));
    let expected3 = poseidon2_qm31(init_digest, qm31_from_u32s(3, 0, 0, 0));
    assert_eq!(context.get(res2[0]), expected2);
    assert_eq!(context.get(res2[1]), expected3);

    context.validate_circuit();
}

#[test]
fn test_draw_point() {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(2072130922, 1322677507, 1508142866, 1010842681);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    let pt = channel.draw_point(&mut context);

    // Just verify the circuit validates — point computation is deterministic.
    assert_ne!(context.get(pt.x), qm31_from_u32s(0, 0, 0, 0));
    assert_ne!(context.get(pt.y), qm31_from_u32s(0, 0, 0, 0));

    context.validate_circuit();
}

#[rstest]
#[case::success(10, true)]
#[case::wrong_n_bits(11, false)]
fn test_pow(#[case] n_bits: u32, #[case] success: bool) {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(968886948, 725376924, 836084817, 484428276);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    // Compute a valid nonce using the outer Poseidon2 PoW chain.
    let prefix = qm31_from_u32s(Channel::POW_PREFIX, 0, 0, 0);
    let s = poseidon2_qm31(prefix, init_digest);
    let pre = poseidon2_qm31(s, qm31_from_u32s(10, 0, 0, 0)); // always 10 bits
    let mask = (1u32 << 10) - 1;
    let valid_nonce_u32 = (0u32..)
        .find(|&n| poseidon2_qm31(pre, qm31_from_u32s(n, 0, 0, 0)).to_m31_array()[0].0 & mask == 0)
        .unwrap();

    let nonce = context.new_var(qm31_from_u32s(valid_nonce_u32, 0, 0, 0));
    channel.pow(&mut context, n_bits, nonce);

    assert_eq!(context.is_circuit_valid(), success);

    if success {
        // After pow, digest = poseidon2(init_digest, nonce)
        let expected_digest = poseidon2_qm31(init_digest, qm31_from_u32s(valid_nonce_u32, 0, 0, 0));
        assert_eq!(context.get(channel.digest), expected_digest);
    }
}
