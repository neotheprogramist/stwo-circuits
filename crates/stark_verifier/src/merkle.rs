use itertools::{Itertools, zip_eq};
use stwo::core::vcs_lifted::verifier::PACKED_LEAF_SIZE;

use crate::oods::EvalDomainSamples;
use crate::proof::N_TRACES;
use crate::sort_queries::{QuerySorter, generate_column_indices};
use circuits::blake::HashValue;
use circuits::context::{Context, Var};
use circuits::ivalue::IValue;
use circuits::ops::{Guess, cond_flip, eq};
use circuits::poseidon2::poseidon_gate;
use circuits::simd::Simd;
use circuits::wrappers::M31Wrapper;

#[cfg(test)]
#[path = "merkle_test.rs"]
pub mod test;

/// Represents an authentication path in a Merkle tree.
#[derive(Clone, Debug, PartialEq)]
pub struct AuthPath<T>(pub Vec<HashValue<T>>);

impl<Value: IValue> Guess<Value> for AuthPath<Value> {
    type Target = AuthPath<Var>;

    fn guess(&self, context: &mut Context<Value>) -> Self::Target {
        AuthPath(self.0.guess(context))
    }
}

/// Represents the collection of authentication paths for a set of trees.
#[derive(Debug, PartialEq)]
pub struct AuthPaths<T> {
    // For each tree, for each query, the authentication path.
    pub data: Vec<Vec<AuthPath<T>>>,
}
impl<T> AuthPaths<T> {
    /// Returns the number of trees represented.
    pub fn n_trees(&self) -> usize {
        self.data.len()
    }

    /// Returns the authentication path for the given tree and query.
    pub fn at(&self, tree_idx: usize, query_idx: usize) -> &AuthPath<T> {
        &self.data[tree_idx][query_idx]
    }
}

impl<Value: IValue> Guess<Value> for AuthPaths<Value> {
    type Target = AuthPaths<Var>;

    fn guess(&self, context: &mut Context<Value>) -> Self::Target {
        AuthPaths { data: self.data.guess(context) }
    }
}

/// Absorbs a sequence of QM31 vars into a Poseidon2 sponge (starting from zero state)
/// and finalizes to a HashValue.
///
/// Matches `Poseidon2M31MerkleHasher::update_leaf` + `finalize` for pre-packed inputs.
fn poseidon_absorb(context: &mut Context<impl IValue>, values: &[Var]) -> HashValue<Var> {
    let zero = context.zero();
    let mut state = zero;
    for &v in values {
        state = poseidon_gate(context, state, v);
    }
    // finalize: h0 = state, h1 = poseidon(state, 0)
    let h0 = state;
    let h1 = poseidon_gate(context, state, zero);
    HashValue(h0, h1)
}

/// Computes the hash of a Merkle leaf. The input is a vector of `M31` values.
fn hash_leaf_m31s(
    context: &mut Context<impl IValue>,
    values: &[M31Wrapper<Var>],
) -> HashValue<Var> {
    let leaf_packed = Simd::pack(context, values);
    poseidon_absorb(context, leaf_packed.get_packed())
}

/// Computes the hash of a Merkle leaf with a single `QM31` value.
pub fn hash_leaf_qm31(context: &mut Context<impl IValue>, value: Var) -> HashValue<Var> {
    poseidon_absorb(context, &[value])
}

/// Computes the hash of a Merkle leaf with 4 `QM31` values.
pub fn hash_packed_leaf_qm31s(
    context: &mut Context<impl IValue>,
    values: [Var; PACKED_LEAF_SIZE],
) -> HashValue<Var> {
    poseidon_absorb(context, &values)
}

/// Computes the hash of an internal node in the Merkle tree.
///
/// Matches `Poseidon2M31MerkleHasher::hash_children`:
///   s  = poseidon(left.0, left.1)
///   s  = poseidon(s, right.0)
///   h1 = poseidon(s, right.1)
///   → HashValue(s, h1)
pub fn hash_node(
    context: &mut Context<impl IValue>,
    left: HashValue<Var>,
    right: HashValue<Var>,
) -> HashValue<Var> {
    let s = poseidon_gate(context, left.0, left.1);
    let s = poseidon_gate(context, s, right.0);
    let h1 = poseidon_gate(context, s, right.1);
    HashValue(s, h1)
}

/// Validates that the leaf at the index given by `bits` has the value `leaf` in a Merkle tree
/// with the given `root`.
///
/// `auth_path` is the authentication path such that `auth_path[0]` is the sibling of `leaf`.
///
/// This is done by computing the root from `leaf` and `auth_path` and comparing it to the given
/// `root`.
pub fn verify_merkle_path<Value: IValue>(
    context: &mut Context<Value>,
    mut leaf: HashValue<Var>,
    bits: &[Var],
    root: HashValue<Var>,
    auth_path: &AuthPath<Var>,
) {
    for (bit, sibling) in zip_eq(bits, &auth_path.0) {
        leaf = merkle_node(context, &leaf, sibling, *bit);
    }
    eq(context, leaf.0, root.0);
    eq(context, leaf.1, root.1);
}

/// Computes a node of a Merkle tree, given one child `node`, its sibling and the
/// bit indicating which child is `node`.
pub fn merkle_node<Value: IValue>(
    context: &mut Context<Value>,
    node: &HashValue<Var>,
    sibling: &HashValue<Var>,
    bit: Var,
) -> HashValue<Var> {
    // Store leaf and sibling in the left and right children.
    let (left0, right0) = cond_flip(context, bit, node.0, sibling.0);
    let (left1, right1) = cond_flip(context, bit, node.1, sibling.1);

    // Compute the next layer's node.
    hash_node(context, HashValue(left0, left1), HashValue(right0, right1))
}

/// Verifies that the queries in `eval_domain_samples` are consistent with the Merkle roots.
///
/// `bits[i][query_idx]` is the `i`-th bit of the bit representation of the query at index
/// `query_idx`.
/// column_log_sizes_by_trace includes the column log sizes for the trace and interaction columns.
pub fn decommit_eval_domain_samples<Value: IValue>(
    context: &mut Context<Value>,
    n_queries: usize,
    column_log_sizes_by_trace: &[Vec<Var>; 2],
    eval_domain_samples: &EvalDomainSamples<Var>,
    auth_paths: &AuthPaths<Var>,
    bits: &[Vec<Var>],
    roots: &[HashValue<Var>; N_TRACES],
) {
    assert_eq!(eval_domain_samples.n_traces(), roots.len());
    assert_eq!(auth_paths.n_trees(), roots.len());

    let max_n_columns_per_trace =
        column_log_sizes_by_trace.iter().map(|log_sizes| log_sizes.len()).max().unwrap_or(0);
    let column_indices = generate_column_indices(context, max_n_columns_per_trace);

    for (trace_idx, root) in roots.iter().enumerate() {
        let data = eval_domain_samples.data_for_trace(trace_idx);

        let mut query_sorter = match trace_idx {
            // Only the trace and interaction columns require sorting.
            1 | 2 => QuerySorter::new(
                context,
                &column_indices,
                &column_log_sizes_by_trace[trace_idx - 1],
            ),
            _ => QuerySorter::skip_sorting(),
        };

        for query_idx in 0..n_queries {
            let query_values =
                data.iter().map(|column_data| column_data[query_idx].clone()).collect_vec();

            let sorted = query_sorter.sort(context, query_values);
            let leaf = hash_leaf_m31s(context, &sorted);
            let auth_path = auth_paths.at(trace_idx, query_idx);
            let bits_for_query = bits.iter().map(|b| b[query_idx]).collect_vec();
            verify_merkle_path(context, leaf, &bits_for_query, *root, auth_path);
        }
    }
}
