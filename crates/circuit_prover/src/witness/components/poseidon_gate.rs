use crate::circuit_air::components::poseidon_gate::N_TRACE_COLUMNS;
use crate::witness::components::prelude::*;
use circuits::poseidon2::{Poseidon2Backend, poseidon2_permutation, qm31_inputs_to_state};
use stwo::core::fields::cm31::CM31;

pub type InputType = [M31; 8];
pub type PackedInputType = [PackedM31; 8];

struct WitnessBackend<'a> {
    cols: &'a mut [M31; N_TRACE_COLUMNS],
    col: usize,
}

impl Poseidon2Backend for WitnessBackend<'_> {
    type Elem = M31;

    fn zero(&mut self) -> Self::Elem {
        M31::from_u32_unchecked(0)
    }

    fn constant(&mut self, value: u32) -> Self::Elem {
        M31::from_u32_unchecked(value)
    }

    fn add(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem {
        M31::reduce(a.0 as u64 + b.0 as u64)
    }

    fn mul(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem {
        M31::reduce((a.0 as u64) * (b.0 as u64))
    }

    fn witness(&mut self, value: Self::Elem) -> Self::Elem {
        self.cols[self.col] = value;
        self.col += 1;
        value
    }
}

/// Computes one row of the Poseidon2 witness trace.
/// Returns all N_TRACE_COLUMNS (662) column values for a single row.
///
/// Column layout:
///   0–3   : in0 as QM31 limbs (only limb0 = in0, rest = 0)
///   4–7   : in1 as QM31 limbs
///   8–11  : out as QM31 limbs (filled with final state[0] after the permutation)
///   12–661: intermediate Poseidon2 witnesses (650 values)
fn compute_row(in0: [M31; 4], in1: [M31; 4]) -> [M31; N_TRACE_COLUMNS] {
    let zero = M31::from_u32_unchecked(0);
    let mut cols = [zero; N_TRACE_COLUMNS];

    cols[0] = in0[0];
    cols[1] = in0[1];
    cols[2] = in0[2];
    cols[3] = in0[3];
    cols[4] = in1[0];
    cols[5] = in1[1];
    cols[6] = in1[2];
    cols[7] = in1[3];
    // cols[8..11] written after computation (out QM31 limbs)

    let in0_qm31 = QM31(CM31(in0[0], in0[1]), CM31(in0[2], in0[3]));
    let in1_qm31 = QM31(CM31(in1[0], in1[1]), CM31(in1[2], in1[3]));
    let state = {
        let mut backend = WitnessBackend { cols: &mut cols, col: 12 };
        let state = poseidon2_permutation(&mut backend, qm31_inputs_to_state(in0_qm31, in1_qm31));
        assert_eq!(
            backend.col, N_TRACE_COLUMNS,
            "wrong Poseidon witness column count: {}",
            backend.col
        );
        state
    };

    // out encodes state[0..3] as QM31 limbs
    cols[8] = state[0];
    cols[9] = state[1];
    cols[10] = state[2];
    cols[11] = state[3];

    cols
}

pub fn write_trace(
    context_values: &[QM31],
    preprocessed_trace: &PreProcessedTrace,
) -> (ComponentTrace<N_TRACE_COLUMNS>, u32, LookupData) {
    let in0_address = preprocessed_trace
        .get_column(&PreProcessedColumnId { id: "poseidon_in0_address".to_owned() });
    let in1_address = preprocessed_trace
        .get_column(&PreProcessedColumnId { id: "poseidon_in1_address".to_owned() });
    let out_address = preprocessed_trace
        .get_column(&PreProcessedColumnId { id: "poseidon_out_address".to_owned() });
    let out_mults = preprocessed_trace
        .get_column(&PreProcessedColumnId { id: "poseidon_out_mults".to_owned() });

    let n_rows = in0_address.len();
    assert_ne!(n_rows, 0);
    assert!(n_rows >= N_LANES);
    assert!(n_rows.is_power_of_two());
    let log_size = n_rows.ilog2();

    let inputs: Vec<InputType> = in0_address
        .iter()
        .zip(in1_address.iter())
        .map(|(&a0, &a1)| {
            let v0 = context_values[a0];
            let v1 = context_values[a1];
            [v0.0.0, v0.0.1, v0.1.0, v0.1.1, v1.0.0, v1.0.1, v1.1.0, v1.1.1]
        })
        .collect();
    let packed_inputs = pack_values(&inputs);

    let preprocessed_columns = [in0_address, in1_address, out_address, out_mults]
        .into_iter()
        .map(|col| Col::<SimdBackend, M31>::from_iter(col.iter().map(|&x| M31::from(x))).data)
        .collect_vec();

    let (trace, lookup_data) = write_trace_simd(packed_inputs, preprocessed_columns);
    (trace, log_size, lookup_data)
}

fn write_trace_simd(
    inputs: Vec<PackedInputType>,
    preprocessed_columns: Vec<Vec<PackedM31>>,
) -> (ComponentTrace<N_TRACE_COLUMNS>, LookupData) {
    let [in0_address, in1_address, out_address, out_mults_col]: [_; 4] =
        preprocessed_columns.try_into().unwrap();

    let log_n_packed_rows = inputs.len().ilog2();
    let log_size = log_n_packed_rows + LOG_N_LANES;
    let (mut trace, mut lookup_data) = unsafe {
        (
            ComponentTrace::<N_TRACE_COLUMNS>::uninitialized(log_size),
            LookupData::uninitialized(log_n_packed_rows),
        )
    };

    let gate_relation_id = PackedM31::broadcast(M31::from(378353459));

    (trace.par_iter_mut(), lookup_data.par_iter_mut(), inputs.into_par_iter())
        .into_par_iter()
        .enumerate()
        .for_each(|(row_index, (row, lookup_data, input))| {
            let [in0_l0, in0_l1, in0_l2, in0_l3, in1_l0, in1_l1, in1_l2, in1_l3] = input;
            let in0_addr = in0_address[row_index];
            let in1_addr = in1_address[row_index];
            let out_addr = out_address[row_index];
            let mults = out_mults_col[row_index];

            let in0_l0_arr: [M31; N_LANES] = in0_l0.to_array();
            let in0_l1_arr: [M31; N_LANES] = in0_l1.to_array();
            let in0_l2_arr: [M31; N_LANES] = in0_l2.to_array();
            let in0_l3_arr: [M31; N_LANES] = in0_l3.to_array();
            let in1_l0_arr: [M31; N_LANES] = in1_l0.to_array();
            let in1_l1_arr: [M31; N_LANES] = in1_l1.to_array();
            let in1_l2_arr: [M31; N_LANES] = in1_l2.to_array();
            let in1_l3_arr: [M31; N_LANES] = in1_l3.to_array();

            let rows: [[M31; N_TRACE_COLUMNS]; N_LANES] = std::array::from_fn(|lane| {
                compute_row(
                    [in0_l0_arr[lane], in0_l1_arr[lane], in0_l2_arr[lane], in0_l3_arr[lane]],
                    [in1_l0_arr[lane], in1_l1_arr[lane], in1_l2_arr[lane], in1_l3_arr[lane]],
                )
            });

            for col in 0..N_TRACE_COLUMNS {
                *row[col] = PackedM31::from_array(std::array::from_fn::<M31, N_LANES, _>(|lane| {
                    rows[lane][col]
                }));
            }

            let in0_col1 = *row[1];
            let in0_col2 = *row[2];
            let in0_col3 = *row[3];
            let in1_col1 = *row[5];
            let in1_col2 = *row[6];
            let in1_col3 = *row[7];
            let out_col0 = *row[8];
            let out_col1 = *row[9];
            let out_col2 = *row[10];
            let out_col3 = *row[11];

            *lookup_data.in_0 = [gate_relation_id, in0_addr, in0_l0, in0_col1, in0_col2, in0_col3];
            *lookup_data.in_1 = [gate_relation_id, in1_addr, in1_l0, in1_col1, in1_col2, in1_col3];
            *lookup_data.out = [gate_relation_id, out_addr, out_col0, out_col1, out_col2, out_col3];
            *lookup_data.out_mults = mults;
        });

    (trace, lookup_data)
}

#[derive(Uninitialized, IterMut, ParIterMut)]
pub struct LookupData {
    in_0: Vec<[PackedM31; 6]>,
    in_1: Vec<[PackedM31; 6]>,
    out: Vec<[PackedM31; 6]>,
    out_mults: Vec<PackedM31>,
}

pub fn write_interaction_trace(
    log_size: u32,
    lookup_data: LookupData,
    common_lookup_elements: &relations::CommonLookupElements,
) -> (Vec<CircleEvaluation<SimdBackend, M31, BitReversedOrder>>, SecureField) {
    let mut logup_gen = unsafe { LogupTraceGenerator::uninitialized(log_size) };

    // Pair 1: use(in0) + use(in1)
    let mut col_gen = logup_gen.new_col();
    (col_gen.par_iter_mut(), &lookup_data.in_0, &lookup_data.in_1).into_par_iter().for_each(
        |(writer, values0, values1)| {
            let denom0: PackedQM31 = common_lookup_elements.combine(values0);
            let denom1: PackedQM31 = common_lookup_elements.combine(values1);
            writer.write_frac(denom0 + denom1, denom0 * denom1);
        },
    );
    col_gen.finalize_col();

    // Pair 2 (single): −out_mults / combine(out)
    let mut col_gen = logup_gen.new_col();
    (col_gen.par_iter_mut(), &lookup_data.out, &lookup_data.out_mults).into_par_iter().for_each(
        |(writer, out_values, &mults)| {
            let denom: PackedQM31 = common_lookup_elements.combine(out_values);
            let neg_mults = -PackedQM31::from(mults);
            writer.write_frac(neg_mults, denom);
        },
    );
    col_gen.finalize_col();

    let (trace, claimed_sum) = logup_gen.finalize_last();
    (trace, claimed_sum)
}

#[cfg(test)]
mod tests {
    use super::*;
    use circuits::ivalue::qm31_from_u32s;
    use circuits::poseidon2::poseidon2_value_qm31;

    #[test]
    fn test_compute_row_output_matches_native_poseidon() {
        let in0 = [
            M31::from_u32_unchecked(5),
            M31::from_u32_unchecked(99),
            M31::from_u32_unchecked(123),
            M31::from_u32_unchecked(456),
        ];
        let in1 = [
            M31::from_u32_unchecked(42),
            M31::from_u32_unchecked(7),
            M31::from_u32_unchecked(8),
            M31::from_u32_unchecked(9),
        ];
        let row = compute_row(in0, in1);

        let a = qm31_from_u32s(in0[0].0, in0[1].0, in0[2].0, in0[3].0);
        let b = qm31_from_u32s(in1[0].0, in1[1].0, in1[2].0, in1[3].0);
        let expected = poseidon2_value_qm31(a, b);

        assert_eq!(row[8], expected[0]);
        assert_eq!(row[9], expected[1]);
        assert_eq!(row[10], expected[2]);
        assert_eq!(row[11], expected[3]);
    }
}
