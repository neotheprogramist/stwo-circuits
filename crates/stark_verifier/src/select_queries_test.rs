use itertools::Itertools;
use num_traits::{One, Zero};
use stwo::core::circle::CirclePoint;
use stwo::core::fields::m31::M31;

use crate::channel::Channel;
use crate::circle::generator_point;
use crate::select_queries::{get_query_selection_input_from_channel, select_queries};
use circuits::context::TraceContext;
use circuits::ivalue::qm31_from_u32s;
use circuits::poseidon2_hasher::poseidon2_qm31;
use circuits::test_utils::{packed_values, simd_from_u32s};

#[test]
fn test_select_queries() {
    let mut context = TraceContext::default();

    const LOG_DOMAIN_SIZE: usize = 5;

    let input = simd_from_u32s(&mut context, vec![24, 25]);
    let queries = select_queries(&mut context, &input, LOG_DOMAIN_SIZE);

    // Check that the first point is on the circle and in the relevant coset
    // (after `LOG_DOMAIN_SIZE` times doubling, we should get `(-1, 0)`).
    let x = packed_values(&context, &queries.points.x)[0].0.0;
    let y = packed_values(&context, &queries.points.y)[0].0.0;
    assert_eq!(x * x + y * y, 1.into());
    assert_eq!(
        CirclePoint { x, y }.repeated_double(LOG_DOMAIN_SIZE as u32),
        CirclePoint { x: -M31::one(), y: M31::zero() }
    );

    // The first query index is `24 = 0b11000`. Removing the LSB and computing bit-reverse we
    // get 0b0011.
    assert_eq!(
        CirclePoint { x, y },
        generator_point(LOG_DOMAIN_SIZE + 1) + generator_point(LOG_DOMAIN_SIZE - 1).mul(0b0011)
    );

    // The second query index is `25 = 0b11001`. Removing the LSB and computing bit-reverse we
    // get 0b0011. Since the LSB is 1, we negate the result.
    let x = packed_values(&context, &queries.points.x)[0].0.1;
    let y = packed_values(&context, &queries.points.y)[0].0.1;
    assert_eq!(
        CirclePoint { x, y },
        -(generator_point(LOG_DOMAIN_SIZE + 1) + generator_point(LOG_DOMAIN_SIZE - 1).mul(0b0011))
    );

    context.validate_circuit();
}

#[test]
fn test_full_select_queries() {
    let mut context = TraceContext::default();

    let init_digest = qm31_from_u32s(271333035, 1833401714, 819175623, 1270120203);
    let mut channel = Channel::from_digest(&mut context, init_digest);

    const N_QUERIES: usize = 3;
    const LOG_DOMAIN_SIZE: usize = 5;

    let query_selection_input =
        get_query_selection_input_from_channel(&mut context, &mut channel, N_QUERIES);

    assert_eq!(query_selection_input.len(), N_QUERIES);

    // draw_two_qm31s uses counter 0 and 1; only counter-0 result is kept.
    let expected_r0 = poseidon2_qm31(init_digest, qm31_from_u32s(0, 0, 0, 0));
    assert_eq!(packed_values(&context, &query_selection_input), [expected_r0]);

    let queries = select_queries(&mut context, &query_selection_input, LOG_DOMAIN_SIZE);

    assert_eq!(queries.points.x.len(), N_QUERIES);
    assert_eq!(queries.points.y.len(), N_QUERIES);
    assert_eq!(
        queries.bits.iter().map(|bits| bits.len()).collect_vec(),
        vec![N_QUERIES; LOG_DOMAIN_SIZE]
    );

    context.validate_circuit();
}
