use stwo::core::circle::CirclePoint;
use stwo::core::fields::m31::MODULUS_BITS;

use circuits::blake::HashValue;
use circuits::context::{Context, Var};
use circuits::eval;
use circuits::extract_bits::extract_bits;
use circuits::ivalue::{IValue, qm31_from_u32s};
use circuits::ops::{div, eq, pointwise_mul};
use circuits::poseidon2::poseidon_gate;
use circuits::simd::Simd;

#[cfg(test)]
#[path = "channel_test.rs"]
pub mod test;

pub struct Channel {
    /// The current digest of the channel (single QM31).
    digest: Var,
    /// The number of times values were taken from the channel.
    n_draws: usize,
}

impl Channel {
    pub const POW_PREFIX: u32 = 0x12345678;

    /// Constructs a new channel with a zero digest.
    pub fn new(context: &mut Context<impl IValue>) -> Self {
        Self { digest: context.zero(), n_draws: 0 }
    }

    fn update_digest(&mut self, new_digest: Var) {
        self.digest = new_digest;
        self.n_draws = 0;
    }

    #[cfg(test)]
    pub fn digest(&self) -> Var {
        self.digest
    }

    #[cfg(test)]
    pub fn from_digest(
        context: &mut circuits::context::TraceContext,
        init_digest: stwo::core::fields::qm31::QM31,
    ) -> Self {
        Self { digest: context.constant(init_digest), n_draws: 0 }
    }

    /// Mixes the given root into the channel's digest.
    ///
    /// Matches `Poseidon2M31MerkleChannel::mix_root` → `mix_felts(&[root.0, root.1])`:
    /// two sequential poseidon2 calls, one for each half of the root.
    pub fn mix_commitment(&mut self, context: &mut Context<impl IValue>, root: HashValue<Var>) {
        let s = poseidon_gate(context, self.digest, root.0);
        self.update_digest(poseidon_gate(context, s, root.1));
    }

    /// Mixes the given list of `QM31` values into the channel.
    ///
    /// Matches `Poseidon2M31Channel::mix_felts`: one poseidon2 call per value.
    pub fn mix_qm31s(
        &mut self,
        context: &mut Context<impl IValue>,
        values: impl IntoIterator<Item = Var>,
    ) {
        let mut state = self.digest;
        for v in values {
            state = poseidon_gate(context, state, v);
        }
        self.update_digest(state);
    }

    /// Draws one `QM31` random value from the channel.
    ///
    /// Matches `Poseidon2M31Channel::draw_secure_felt`: one poseidon2 call with the counter.
    pub fn draw_qm31(&mut self, context: &mut Context<impl IValue>) -> Var {
        let n = context.constant(qm31_from_u32s(self.n_draws.try_into().unwrap(), 0, 0, 0));
        let result = poseidon_gate(context, self.digest, n);
        self.n_draws += 1;
        result
    }

    /// Draws two `QM31` random values from the channel.
    ///
    /// Matches two sequential `Poseidon2M31Channel::draw_secure_felt` calls: each uses its own
    /// counter, so `n_draws` advances by 2.
    pub fn draw_two_qm31s(&mut self, context: &mut Context<impl IValue>) -> [Var; 2] {
        let n0 = context.constant(qm31_from_u32s(self.n_draws.try_into().unwrap(), 0, 0, 0));
        let r0 = poseidon_gate(context, self.digest, n0);
        let n1 = context.constant(qm31_from_u32s((self.n_draws + 1).try_into().unwrap(), 0, 0, 0));
        let r1 = poseidon_gate(context, self.digest, n1);
        self.n_draws += 2;
        [r0, r1]
    }

    /// Draws a random point on the (`QM31`) circle from the channel.
    pub fn draw_point(&mut self, context: &mut Context<impl IValue>) -> CirclePoint<Var> {
        let t = self.draw_qm31(context);
        let t2 = eval!(context, (t) * (t));

        let denom = eval!(context, (t2) + (1));
        let denom_inv = div(context, context.one(), denom);
        let x = eval!(context, ((1) - (t2)) * (denom_inv));
        let y = eval!(context, ((2) * (t)) * (denom_inv));
        CirclePoint { x, y }
    }

    /// Verifies proof-of-work and updates the digest.
    ///
    /// Chain (matches `Poseidon2M31Channel::verify_pow_nonce`):
    ///   `s = poseidon2(POW_PREFIX, digest)`,
    ///   `pre = poseidon2(s, n_bits)`,
    ///   `result = poseidon2(pre, nonce)`.
    /// Checks that `n_bits` least-significant bits of `result`'s first M31 are zero,
    /// then updates `digest = poseidon2(digest, nonce)` (matches `mix_u64(nonce)`).
    pub fn pow(&mut self, context: &mut Context<impl IValue>, n_bits: u32, nonce: Var) {
        assert!(n_bits <= 30);

        // Check that nonce's upper two M31 components are zero (nonce fits in two u32s).
        let nonce_high_mask = context.constant(qm31_from_u32s(0, 0, 1, 1));
        let masked_nonce = pointwise_mul(context, nonce, nonce_high_mask);
        eq(context, masked_nonce, context.zero());

        // Compute s = poseidon(POW_PREFIX, digest).
        let prefix = context.constant(qm31_from_u32s(Self::POW_PREFIX, 0, 0, 0));
        let s = poseidon_gate(context, prefix, self.digest);

        // Compute pre = poseidon(s, n_bits).
        let n_bits_var = context.constant(qm31_from_u32s(n_bits, 0, 0, 0));
        let pre = poseidon_gate(context, s, n_bits_var);

        // Compute result = poseidon(pre, nonce) and check n_bits LSBs of first M31 are zero.
        // Unpack only the first M31 component — PoW uses result.to_m31_array()[0] only.
        let result = poseidon_gate(context, pre, nonce);
        let result_first_m31 = Simd::unpack_idx(context, &Simd::from_packed(vec![result], 1), 0);
        let bits =
            extract_bits(context, &Simd::from_packed(vec![result_first_m31], 1), MODULUS_BITS);
        for bit in &bits[0..n_bits.try_into().unwrap()] {
            eq(context, bit.get_packed()[0], context.zero());
        }

        // Update channel state: poseidon(digest, nonce) matches mix_u64(nonce).
        let new_state = poseidon_gate(context, self.digest, nonce);
        self.update_digest(new_state);
    }
}
