use crate::CircuitParams;
use crate::N_LANES;
use crate::Qm31OpsTraceGenerator;
use crate::finalize::finalize_context;
use circuits::circuit::M31ToU32;
use circuits::circuit::Poseidon;
use circuits::circuit::{Circuit, Permutation};
use circuits::circuit::{Eq, Gate};
use circuits::context::Context;
use circuits::ivalue::IValue;
use itertools::{Itertools, zip_eq};
use std::collections::HashMap;
use std::sync::Arc;
#[cfg(feature = "prover")]
use stwo::core::fields::m31::BaseField;
#[cfg(feature = "prover")]
use stwo::core::poly::circle::CanonicCoset;
#[cfg(feature = "prover")]
use stwo::prover::backend::simd::m31::PackedM31;
#[cfg(feature = "prover")]
use stwo::prover::backend::{Backend, Col, Column};
#[cfg(feature = "prover")]
use stwo::prover::poly::BitReversedOrder;
#[cfg(feature = "prover")]
use stwo::prover::poly::circle::CircleEvaluation;
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

#[cfg(feature = "prover")]
#[cfg(test)]
#[path = "preprocessed_test.rs"]
pub mod test;

const N_QM31_OPS_PP_COLUMNS: usize = 8;
const N_EQ_PP_COLUMNS: usize = 2;
const N_OP_CODES: usize = 4;

#[derive(Copy, Clone)]
enum OpCode {
    Add,
    Sub,
    Mul,
    PointwiseMul,
}

/// Adds the binary operation gates to the qm31 ops preprocessed trace.
fn fill_binary_op_columns<G: Gate>(
    gates: &[G],
    op_code: OpCode,
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_QM31_OPS_PP_COLUMNS],
) {
    let op_code_idx = op_code as usize;
    for gate in gates.iter() {
        let [in0, in1] = gate.uses()[..] else { panic!("Expected 2 uses for gate") };
        let [out] = gate.yields()[..] else { panic!("Expected 1 yield for gate") };
        (0..N_OP_CODES).for_each(|i| {
            columns[i].push(if i == op_code_idx { 1 } else { 0 });
        });
        columns[4].push(in0);
        columns[5].push(in1);
        columns[6].push(out);
        // TODO(Gali): Consider negating the multiplicities.
        columns[7].push(multiplicities[out]);
    }
}

/// Implements a permutation gate with n inputs and n outputs using 2n Add gates.
///
/// Process:
/// 1. First n gates: Write inputs to permutation wire
///    - `permutation_wire = Add(0, input_i)` for each input i
/// 2. Next n gates: Read outputs from permutation wire
///    - `output_i = Add(0, permutation_wire)` for each output i
///
/// Using the same wire address for all the inputs with multiplicity 1 ensures that the outputs
/// are a permutation of the inputs.
fn fill_permutation_columns(
    gates: &[Permutation],
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_QM31_OPS_PP_COLUMNS],
    first_unused_address: usize,
) {
    let add_op_code_idx = OpCode::Add as usize;
    let mut permutation_address = first_unused_address;
    for gate in gates.iter() {
        let inputs = gate.uses();
        let outputs = gate.yields();

        // Set flag to Add opcode.
        (0..N_OP_CODES).for_each(|i| {
            columns[i].extend(std::iter::repeat_n(
                (i == add_op_code_idx) as usize,
                inputs.len() + outputs.len(),
            ));
        });

        // TODO(alonf): Parallelize, and insert the above loop inside.
        for (input, output) in zip_eq(inputs, outputs) {
            // Input row.
            columns[4].push(0);
            columns[5].push(input);
            columns[6].push(permutation_address);
            columns[7].push(1);

            // Output row.
            columns[4].push(0);
            columns[5].push(permutation_address);
            columns[6].push(output);
            columns[7].push(multiplicities[output]);
        }

        permutation_address += 1;
    }
}

/// Adds the eq gates to the eq preprocessed trace.
fn fill_eq_columns(eq_gates: &[Eq], columns: &mut [Vec<usize>; N_EQ_PP_COLUMNS]) {
    for gate in eq_gates.iter() {
        let [in0, in1] = gate.uses()[..] else { panic!("Expected 2 uses for gate") };
        assert!(gate.yields().is_empty(), "Expected no yields for Eq gate");
        columns[0].push(in0);
        columns[1].push(in1);
    }
}

/// Adds the preprocessed columns of qm31_ops component to the preprocessed trace. If the component
/// is empty, no columns are added. Preprocessed columns are in the following format:
/// | add_flag | sub_flag | mul_flag | pointwise_mul_flag | in0_address | in1_address | out_address | mults |
fn add_qm31_ops_to_preprocessed_trace(
    circuit: &Circuit,
    multiplicities: &[usize],
    pp_trace: &mut PreProcessedTrace,
) -> Qm31OpsTraceGenerator {
    let Circuit {
        n_vars,
        add,
        sub,
        mul,
        pointwise_mul,
        eq: _,
        blake: _,
        poseidon: _,
        m31_to_u32: _,
        permutation,
        output: _,
    } = circuit;
    let mut qm31_ops_columns: [_; N_QM31_OPS_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_binary_op_columns(add, OpCode::Add, multiplicities, &mut qm31_ops_columns);
    fill_binary_op_columns(sub, OpCode::Sub, multiplicities, &mut qm31_ops_columns);
    fill_binary_op_columns(mul, OpCode::Mul, multiplicities, &mut qm31_ops_columns);
    fill_binary_op_columns(
        pointwise_mul,
        OpCode::PointwiseMul,
        multiplicities,
        &mut qm31_ops_columns,
    );
    let qm31_ops_trace_generator =
        Qm31OpsTraceGenerator { first_permutation_row: qm31_ops_columns[0].len() };

    fill_permutation_columns(permutation, multiplicities, &mut qm31_ops_columns, *n_vars);

    let ids = [
        "qm31_ops_add_flag",
        "qm31_ops_sub_flag",
        "qm31_ops_mul_flag",
        "qm31_ops_pointwise_mul_flag",
        "qm31_ops_in0_address",
        "qm31_ops_in1_address",
        "qm31_ops_out_address",
        "qm31_ops_mults",
    ];
    for (id, column) in zip_eq(ids, qm31_ops_columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }
    qm31_ops_trace_generator
}

/// Adds the preprocessed columns of eq component to the preprocessed trace. If the component
/// is empty, no columns are added. Preprocessed columns are in the following format:
/// | in0_address | in1_address |
fn add_eq_to_preprocessed_trace(circuit: &Circuit, pp_trace: &mut PreProcessedTrace) {
    let Circuit {
        n_vars: _,
        add: _,
        sub: _,
        mul: _,
        pointwise_mul: _,
        eq,
        blake: _,
        poseidon: _,
        m31_to_u32: _,
        permutation: _,
        output: _,
    } = circuit;
    let mut eq_columns: [_; N_EQ_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_eq_columns(eq, &mut eq_columns);

    let ids = ["eq_in0_address", "eq_in1_address"];
    for (id, column) in zip_eq(ids, eq_columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }
}

const N_POSEIDON_PP_COLUMNS: usize = 4;

fn fill_poseidon_columns(
    gates: &[Poseidon],
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_POSEIDON_PP_COLUMNS],
) {
    for gate in gates.iter() {
        columns[0].push(gate.in0);
        columns[1].push(gate.in1);
        columns[2].push(gate.out);
        columns[3].push(multiplicities[gate.out]);
    }
}

fn add_poseidon_to_preprocessed_trace(
    circuit: &Circuit,
    multiplicities: &[usize],
    pp_trace: &mut PreProcessedTrace,
) {
    let Circuit {
        n_vars: _,
        add: _,
        sub: _,
        mul: _,
        pointwise_mul: _,
        eq: _,
        blake: _,
        poseidon,
        m31_to_u32: _,
        permutation: _,
        output: _,
    } = circuit;
    if poseidon.is_empty() {
        return;
    }
    let mut poseidon_columns: [_; N_POSEIDON_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_poseidon_columns(poseidon, multiplicities, &mut poseidon_columns);

    let ids = [
        "poseidon_in0_address",
        "poseidon_in1_address",
        "poseidon_out_address",
        "poseidon_out_mults",
    ];
    for (id, column) in zip_eq(ids, poseidon_columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }
}

const N_M31_TO_U32_PP_COLUMNS: usize = 3;

/// Adds M31ToU32 gates to preprocessed trace columns.
/// | input_address | output_address | multiplicity |
fn fill_m31_to_u32_columns(
    gates: &[M31ToU32],
    multiplicities: &[usize],
    columns: &mut [Vec<usize>; N_M31_TO_U32_PP_COLUMNS],
) {
    for gate in gates.iter() {
        let [input] = gate.uses()[..] else { panic!("Expected 1 use for M31ToU32") };
        let [out] = gate.yields()[..] else { panic!("Expected 1 yield for M31ToU32") };
        columns[0].push(input);
        columns[1].push(out);
        columns[2].push(multiplicities[out]);
    }
}

fn add_m31_to_u32_to_preprocessed_trace(
    circuit: &Circuit,
    multiplicities: &[usize],
    pp_trace: &mut PreProcessedTrace,
) {
    let mut columns: [_; N_M31_TO_U32_PP_COLUMNS] = std::array::from_fn(|_| vec![]);
    fill_m31_to_u32_columns(&circuit.m31_to_u32, multiplicities, &mut columns);

    let ids = ["m31_to_u32_input_addr", "m31_to_u32_output_addr", "m31_to_u32_multiplicity"];
    for (id, column) in zip_eq(ids, columns) {
        pp_trace.push_column(PreProcessedColumnId { id: id.to_owned() }, column);
    }
}

/// A collection of preprocessed columns, whose values are publicly acknowledged, and independent of
/// the proof.
#[derive(Clone, Debug, PartialEq)]
pub struct PreProcessedTrace {
    pub columns: Vec<Vec<usize>>,
    column_ids: Vec<PreProcessedColumnId>,
    column_indices: HashMap<PreProcessedColumnId, usize>,
}

impl PreProcessedTrace {
    fn push_column(&mut self, id: PreProcessedColumnId, column: Vec<usize>) {
        let idx = self.columns.len();
        assert!(
            self.column_indices.insert(id.clone(), idx).is_none(),
            "Duplicate preprocessed column id: {id:?}"
        );
        self.column_ids.push(id);
        self.columns.push(column);
    }

    /// Sorts preprocessed columns by size (ascending), preserving original order for ties.
    fn sort_by_size(&mut self) {
        let mut entries = std::mem::take(&mut self.columns)
            .into_iter()
            .zip(std::mem::take(&mut self.column_ids))
            .collect_vec();
        // Stable sort keeps original insertion order for equal-length columns.
        entries.sort_by_key(|(column, _)| column.len());

        self.columns = entries.iter_mut().map(|(column, _)| std::mem::take(column)).collect();
        self.column_ids = entries.into_iter().map(|(_, id)| id).collect();
        self.column_indices =
            self.column_ids.iter().cloned().enumerate().map(|(idx, id)| (id, idx)).collect();
    }
    fn add_non_circuit_preprocessed_columns(
        pp_trace: &mut PreProcessedTrace,
        log_seq_sizes: &[u32],
    ) {
        for &log_size in log_seq_sizes {
            let seq_column: Vec<usize> = (0..1_usize << log_size).collect();
            pp_trace
                .push_column(PreProcessedColumnId { id: format!("seq_{log_size}") }, seq_column);
        }
    }

    pub fn log_sizes(&self) -> Vec<u32> {
        self.columns.iter().map(|c| c.len().ilog2()).collect()
    }

    pub fn ids(&self) -> Vec<PreProcessedColumnId> {
        self.column_ids.clone()
    }

    #[cfg(feature = "prover")]
    pub fn get_trace<B: Backend>(&self) -> Vec<CircleEvaluation<B, BaseField, BitReversedOrder>> {
        let to_evaluation = |vec: &[usize]| {
            let col = Col::<B, BaseField>::from_iter(vec.iter().cloned().map(BaseField::from));
            CircleEvaluation::new(CanonicCoset::new(col.len().ilog2()).circle_domain(), col)
        };

        self.columns.iter().map(|c| to_evaluation(c)).collect()
    }

    pub fn get_column(&self, id: &PreProcessedColumnId) -> &Vec<usize> {
        &self.columns[*self
            .column_indices
            .get(id)
            .unwrap_or_else(|| panic!("Missing preprocessed column {id:?}"))]
    }

    #[cfg(feature = "prover")]
    pub fn get_packed_column(&self, id: &PreProcessedColumnId) -> Vec<PackedM31> {
        let column = self.get_column(id);
        column
            .chunks_exact(N_LANES)
            .map(|c| PackedM31::from_array(std::array::from_fn(|i| BaseField::from(c[i]))))
            .collect::<Vec<_>>()
    }
}

#[derive(Debug, PartialEq)]
pub struct PreprocessedCircuit {
    pub preprocessed_trace: Arc<PreProcessedTrace>,
    pub params: CircuitParams,
}

impl PreprocessedCircuit {
    /// Finalizes the context, then builds the preprocessed circuit.
    pub fn preprocess_circuit(context: &mut Context<impl IValue>) -> Self {
        finalize_context(context);
        Self::from_finalized_circuit(&context.circuit)
    }

    /// Builds the preprocessed circuit data (trace + params) from a finalized circuit.
    pub fn from_finalized_circuit(circuit: &Circuit) -> Self {
        let mut pp_trace = PreProcessedTrace {
            columns: vec![],
            column_ids: vec![],
            column_indices: HashMap::new(),
        };

        // Adjust multiplicities to account for the use of the constant 0 in the permutation gate
        // implementation. See `fill_permutation_columns` for details.
        let mut multiplicities = circuit.compute_multiplicities().0;
        let additional_zero_multiplicity: usize =
            circuit.permutation.iter().map(|gate| gate.inputs.len() + gate.outputs.len()).sum();
        multiplicities[0] += additional_zero_multiplicity;

        // Add Eq columns.
        add_eq_to_preprocessed_trace(circuit, &mut pp_trace);
        // Add QM31 operations columns.
        let qm31_ops_trace_generator =
            add_qm31_ops_to_preprocessed_trace(circuit, &multiplicities, &mut pp_trace);
        // Add Poseidon columns.
        add_poseidon_to_preprocessed_trace(circuit, &multiplicities, &mut pp_trace);
        // Add M31ToU32 columns.
        add_m31_to_u32_to_preprocessed_trace(circuit, &multiplicities, &mut pp_trace);

        // Generate the seq columns required by the current circuit-verifier components.
        // At the moment the prover path always needs seq_16 for range_check_16.
        let mut log_seq_sizes = vec![16];
        log_seq_sizes.sort();
        log_seq_sizes.dedup();

        PreProcessedTrace::add_non_circuit_preprocessed_columns(&mut pp_trace, &log_seq_sizes);
        pp_trace.sort_by_size();

        let trace_log_size = pp_trace.log_sizes().into_iter().max().unwrap();

        let params = CircuitParams {
            trace_log_size,
            first_permutation_row: qm31_ops_trace_generator.first_permutation_row,
            output_addresses: circuit.output.iter().map(|out| out.in0).collect(),
        };

        Self { preprocessed_trace: Arc::new(pp_trace), params }
    }
}
