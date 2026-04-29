pub use crate::witness::utils::pack_values;
pub use circuit_common::Qm31OpsTraceGenerator;
pub use circuit_common::preprocessed::PreProcessedTrace;
pub use circuit_verifier::circuit_claim::ClaimedSum;
pub use circuit_verifier::circuit_claim::ComponentLogSize;
pub use circuit_verifier::relations;
pub use itertools::Itertools;
pub use itertools::multizip;
pub use num_traits::One;
pub use num_traits::Zero;
pub use rayon::iter::IndexedParallelIterator;
pub use rayon::iter::IntoParallelIterator;
pub use rayon::iter::IntoParallelRefIterator;
pub use rayon::iter::IntoParallelRefMutIterator;
pub use rayon::iter::ParallelIterator;
pub use std::array::from_fn;
pub use std::collections::HashMap;
pub use std::simd::Simd;
pub use std::simd::num::SimdInt;
pub use std::simd::num::SimdUint;
pub use std::simd::u32x16;
pub use std::sync::Arc;
pub use std::sync::atomic::AtomicU32;
pub use std::sync::atomic::Ordering;
pub use stwo::core::fields::m31::M31;
pub use stwo::core::fields::qm31::QM31;
pub use stwo::core::fields::qm31::SecureField;
pub use stwo::core::poly::circle::CanonicCoset;
pub use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
pub use stwo::prover::TreeBuilder;
pub use stwo::prover::backend::Col;
pub use stwo::prover::backend::simd::SimdBackend;
pub use stwo::prover::backend::simd::column::BaseColumn;
pub use stwo::prover::backend::simd::conversion::{Pack, Unpack};
pub use stwo::prover::backend::simd::m31::{LOG_N_LANES, N_LANES, PackedM31};
pub use stwo::prover::backend::simd::qm31::PackedQM31;
pub use stwo::prover::poly::BitReversedOrder;
pub use stwo::prover::poly::circle::CircleEvaluation;
pub use stwo_air_utils::trace::component_trace::ComponentTrace;
pub use stwo_air_utils_derive::{IterMut, ParIterMut, Uninitialized};
pub use stwo_cairo_prover::witness::utils::{AtomicMultiplicityColumn, Enabler};
pub use stwo_constraint_framework::LogupTraceGenerator;
pub use stwo_constraint_framework::Relation;
pub use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

/// Create the input_to_row map used in const-size components.
///
/// `preprocessed_trace` - The preprocessed trace.
/// `column_ids` - PreProcessedColumnId for each input column of the component.
///
/// Returns a mapping from input tuple to its row number. Used to find
/// out which multiplicity value to update for a given input.
pub fn make_input_to_row<const N: usize>(
    preprocessed_trace: &PreProcessedTrace,
    column_ids: [PreProcessedColumnId; N],
) -> HashMap<[M31; N], usize> {
    let mut result: HashMap<[M31; N], usize> = HashMap::new();

    let columns = column_ids.iter().map(|id| preprocessed_trace.get_column(id)).collect_vec();
    let log_size = columns[0].len().ilog2();
    assert!(
        columns.iter().all(|c| c.len().ilog2() == log_size),
        "input_to_row columns of different sizes"
    );

    for packed_row in 0..(1 << (log_size - LOG_N_LANES)) {
        let row_offset = packed_row * N_LANES;
        for i in 0..N_LANES {
            let key: [M31; N] = columns
                .iter()
                .map(|column| M31::from(column[row_offset + i]))
                .collect_vec()
                .try_into()
                .expect("Unexpected number of column values");
            result.insert(key, row_offset + i);
        }
    }

    result
}

pub fn pack_preprocessed_column(column: &[usize]) -> Vec<PackedM31> {
    let values: Vec<M31> = column.par_iter().map(|&v| M31::from(v)).collect();
    pack_values(&values)
}
