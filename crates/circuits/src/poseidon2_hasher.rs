use std::fmt;

use serde::{Deserialize, Serialize};
use stwo::core::channel::{Channel, MerkleChannel};
use stwo::core::fields::cm31::CM31;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::vcs::hash::Hash;
use stwo::core::vcs_lifted::merkle_hasher::MerkleHasherLifted;

use crate::ivalue::qm31_from_u32s;
use crate::poseidon2::poseidon2_value_qm31;

// ---------------------------------------------------------------------------
// Core function
// ---------------------------------------------------------------------------

/// Computes Poseidon2 on two QM31 inputs and returns one QM31 output.
/// This is the non-circuit version — must match `poseidon_gate` in circuit.
pub fn poseidon2_qm31(a: QM31, b: QM31) -> QM31 {
    let [s0, s1, s2, s3] = poseidon2_value_qm31(a, b);
    qm31_from_u32s(s0.0, s1.0, s2.0, s3.0)
}

// ---------------------------------------------------------------------------
// Hash type
// ---------------------------------------------------------------------------

/// A hash produced by Poseidon2-M31: two QM31 values (8 M31 limbs total).
#[derive(Copy, Clone, Default, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Poseidon2M31Hash(pub QM31, pub QM31);

impl fmt::Display for Poseidon2M31Hash {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}

impl Hash for Poseidon2M31Hash {}

impl From<Poseidon2M31Hash> for crate::blake::HashValue<QM31> {
    fn from(h: Poseidon2M31Hash) -> Self {
        crate::blake::HashValue(h.0, h.1)
    }
}

// ---------------------------------------------------------------------------
// Merkle hasher (leaf + node)
// ---------------------------------------------------------------------------

/// Merkle hasher built on Poseidon2-M31.
///
/// Leaf: absorb M31 values 4-at-a-time (packed as QM31) via chained poseidon2 calls.
/// Node: `s = poseidon2(left.0, left.1)`, `s = poseidon2(s, right.0)`,
///       `h1 = poseidon2(s, right.1)` → `HashValue(s, h1)`.
///
/// The node scheme must exactly match `hash_node` in `stark_verifier/src/merkle.rs`.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Poseidon2M31MerkleHasher {
    state: QM31,
    buffer: Vec<M31>,
}

impl MerkleHasherLifted for Poseidon2M31MerkleHasher {
    type Hash = Poseidon2M31Hash;

    fn hash_children((left, right): (Self::Hash, Self::Hash)) -> Self::Hash {
        let s = poseidon2_qm31(left.0, left.1);
        let s = poseidon2_qm31(s, right.0);
        let h1 = poseidon2_qm31(s, right.1);
        Poseidon2M31Hash(s, h1)
    }

    fn update_leaf(&mut self, values: &[M31]) {
        let mut all: Vec<M31> = self.buffer.drain(..).collect();
        all.extend_from_slice(values);
        let n_complete = (all.len() / 4) * 4;
        for chunk in all[..n_complete].chunks(4) {
            let qm31 = QM31(CM31(chunk[0], chunk[1]), CM31(chunk[2], chunk[3]));
            self.state = poseidon2_qm31(self.state, qm31);
        }
        self.buffer = all[n_complete..].to_vec();
    }

    fn finalize(mut self) -> Self::Hash {
        if !self.buffer.is_empty() {
            let mut chunk = [M31::from_u32_unchecked(0); 4];
            chunk[..self.buffer.len()].copy_from_slice(&self.buffer);
            let qm31 = QM31(CM31(chunk[0], chunk[1]), CM31(chunk[2], chunk[3]));
            self.state = poseidon2_qm31(self.state, qm31);
        }
        let h0 = self.state;
        let h1 = poseidon2_qm31(self.state, QM31::default());
        Poseidon2M31Hash(h0, h1)
    }
}

// ---------------------------------------------------------------------------
// Channel
// ---------------------------------------------------------------------------

/// Fiat-Shamir channel built on Poseidon2-M31.
///
/// State is a single QM31. Draw uses counter: `poseidon2(state, counter_qm31)`.
/// Mix resets counter and chains poseidon2 calls one per absorbed QM31.
///
/// Must match `Channel` in `stark_verifier/src/channel.rs`.
#[derive(Clone, Debug, Default)]
pub struct Poseidon2M31Channel {
    digest: QM31,
    n_draws: u32,
}

impl Poseidon2M31Channel {
    pub const POW_PREFIX: u32 = 0x12345678;

    pub fn digest(&self) -> QM31 {
        self.digest
    }

    fn update_digest(&mut self, new_digest: QM31) {
        self.digest = new_digest;
        self.n_draws = 0;
    }
}

impl Channel for Poseidon2M31Channel {
    const BYTES_PER_HASH: usize = 16;

    /// Absorb a list of QM31 values: one poseidon2 call per value.
    /// Matches `Channel::mix_qm31s` in `stark_verifier/src/channel.rs`.
    fn mix_felts(&mut self, felts: &[QM31]) {
        let mut state = self.digest;
        for &felt in felts {
            state = poseidon2_qm31(state, felt);
        }
        self.update_digest(state);
    }

    fn mix_u32s(&mut self, data: &[u32]) {
        let mut state = self.digest;
        for chunk in data.chunks(4) {
            let a = chunk.first().copied().unwrap_or(0);
            let b = chunk.get(1).copied().unwrap_or(0);
            let c = chunk.get(2).copied().unwrap_or(0);
            let d = chunk.get(3).copied().unwrap_or(0);
            state = poseidon2_qm31(state, qm31_from_u32s(a, b, c, d));
        }
        self.update_digest(state);
    }

    fn mix_u64(&mut self, value: u64) {
        self.mix_u32s(&[value as u32, (value >> 32) as u32]);
    }

    fn draw_u32s(&mut self) -> Vec<u32> {
        let counter = qm31_from_u32s(self.n_draws, 0, 0, 0);
        let result = poseidon2_qm31(self.digest, counter);
        self.n_draws += 1;
        let [a, b, c, d] = result.to_m31_array().map(|m| m.0);
        vec![a, b, c, d]
    }

    fn draw_secure_felt(&mut self) -> QM31 {
        let u32s = self.draw_u32s();
        qm31_from_u32s(u32s[0], u32s[1], u32s[2], u32s[3])
    }

    fn draw_secure_felts(&mut self, n_felts: usize) -> Vec<QM31> {
        (0..n_felts).map(|_| self.draw_secure_felt()).collect()
    }

    /// Verifies that the PoW nonce produces `n_bits` zero LSBs.
    ///
    /// Chain (must match `Channel::pow` in `stark_verifier/src/channel.rs`):
    ///   `s = poseidon2(POW_PREFIX, digest)`,
    ///   `pre = poseidon2(s, n_bits)`,
    ///   `result = poseidon2(pre, nonce)`.
    /// Checks that the `n_bits` LSBs of `result`'s first M31 are zero.
    fn verify_pow_nonce(&self, n_bits: u32, nonce: u64) -> bool {
        let prefix = qm31_from_u32s(Self::POW_PREFIX, 0, 0, 0);
        let s = poseidon2_qm31(prefix, self.digest);
        let n_bits_q = qm31_from_u32s(n_bits, 0, 0, 0);
        let pre = poseidon2_qm31(s, n_bits_q);
        let nonce_q = qm31_from_u32s(nonce as u32, (nonce >> 32) as u32, 0, 0);
        let result = poseidon2_qm31(pre, nonce_q);
        let mask = if n_bits < 32 { (1u32 << n_bits) - 1 } else { u32::MAX };
        (result.to_m31_array()[0].0 & mask) == 0
    }
}

// ---------------------------------------------------------------------------
// MerkleChannel glue
// ---------------------------------------------------------------------------

/// Glue between `Poseidon2M31Channel` and `Poseidon2M31MerkleHasher`.
///
/// `mix_root` absorbs both halves of the hash — matches `Channel::mix_commitment`
/// in `stark_verifier/src/channel.rs` (two sequential poseidon_gate calls).
#[derive(Default)]
pub struct Poseidon2M31MerkleChannel;

impl MerkleChannel for Poseidon2M31MerkleChannel {
    type C = Poseidon2M31Channel;
    type H = Poseidon2M31MerkleHasher;

    fn mix_root(channel: &mut Self::C, root: Poseidon2M31Hash) {
        channel.mix_felts(&[root.0, root.1]);
    }
}

// ---------------------------------------------------------------------------
// SimdBackend trait impls (only when `prover` feature is active)
// ---------------------------------------------------------------------------

#[cfg(feature = "prover")]
mod simd_backend_impl {
    use stwo::core::fields::m31::BaseField;
    use stwo::core::proof_of_work::GrindOps;
    use stwo::prover::backend::Column;
    use stwo::prover::backend::simd::SimdBackend;
    use stwo::prover::backend::{BackendForChannel, Col, ColumnOps, CpuBackend};
    use stwo::prover::vcs_lifted::ops::MerkleOpsLifted;

    use super::{
        Poseidon2M31Channel, Poseidon2M31Hash, Poseidon2M31MerkleChannel, Poseidon2M31MerkleHasher,
    };

    impl ColumnOps<Poseidon2M31Hash> for SimdBackend {
        type Column = Vec<Poseidon2M31Hash>;

        fn bit_reverse_column(_column: &mut Self::Column) {
            unimplemented!("bit reversal not used for Poseidon2M31Hash columns")
        }
    }

    impl MerkleOpsLifted<Poseidon2M31MerkleHasher> for SimdBackend {
        fn build_leaves(
            columns: &[&Col<Self, BaseField>],
            lifting_log_size: u32,
        ) -> Vec<Poseidon2M31Hash> {
            let cpu_cols: Vec<Vec<BaseField>> = columns.iter().map(|c| c.to_cpu()).collect();
            let cpu_refs: Vec<&Vec<BaseField>> = cpu_cols.iter().collect();
            <CpuBackend as MerkleOpsLifted<Poseidon2M31MerkleHasher>>::build_leaves(
                &cpu_refs,
                lifting_log_size,
            )
        }

        fn build_next_layer(prev_layer: &Vec<Poseidon2M31Hash>) -> Vec<Poseidon2M31Hash> {
            <CpuBackend as MerkleOpsLifted<Poseidon2M31MerkleHasher>>::build_next_layer(prev_layer)
        }
    }

    impl GrindOps<Poseidon2M31Channel> for SimdBackend {
        fn grind(channel: &Poseidon2M31Channel, pow_bits: u32) -> u64 {
            CpuBackend::grind(channel, pow_bits)
        }
    }

    impl BackendForChannel<Poseidon2M31MerkleChannel> for SimdBackend {}
    impl BackendForChannel<Poseidon2M31MerkleChannel> for CpuBackend {}
}
