use std::collections::HashMap;

use itertools::chain;
use stwo::core::fields::qm31::QM31;

use crate::blake::blake_qm31;
use crate::ivalue::IValue;
use crate::poseidon2::poseidon2_value_qm31;

#[cfg(test)]
#[path = "circuit_test.rs"]
pub mod test;

fn check_eq(a: QM31, b: QM31) -> Result<(), String> {
    if a != b {
        return Err(format!("{a} != {b}"));
    }
    Ok(())
}

pub trait Gate: std::fmt::Debug {
    fn check(&self, values: &[QM31]) -> Result<(), String>;

    /// Returns the variables that are "used" by the gate (in the context of lookup terms).
    fn uses(&self) -> Vec<usize>;

    /// Returns the variables that are "yielded" by the gate (in the context of lookup terms).
    fn yields(&self) -> Vec<usize>;
}

/// Represents an addition gate in the circuit: `[in0] + [in1] = [out]`.
#[derive(PartialEq, Eq)]
pub struct Add {
    pub in0: usize,
    pub in1: usize,
    pub out: usize,
}
impl Gate for Add {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        check_eq(values[self.in0] + values[self.in1], values[self.out])
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0, self.in1]
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out]
    }
}

impl std::fmt::Debug for Add {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = [{}] + [{}]", self.out, self.in0, self.in1)
    }
}

/// Represents a subtraction gate in the circuit: `[in0] - [in1] = [out]`.
#[derive(PartialEq, Eq)]
pub struct Sub {
    pub in0: usize,
    pub in1: usize,
    pub out: usize,
}
impl Gate for Sub {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        check_eq(values[self.in0] - values[self.in1], values[self.out])
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0, self.in1]
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out]
    }
}

impl std::fmt::Debug for Sub {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = [{}] - [{}]", self.out, self.in0, self.in1)
    }
}

/// Represents a multiplication gate in the circuit: `[in0] * [in1] = [out]`.
#[derive(PartialEq, Eq)]
pub struct Mul {
    pub in0: usize,
    pub in1: usize,
    pub out: usize,
}
impl Gate for Mul {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        check_eq(values[self.in0] * values[self.in1], values[self.out])
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0, self.in1]
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out]
    }
}

impl std::fmt::Debug for Mul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = [{}] * [{}]", self.out, self.in0, self.in1)
    }
}

/// Represents a pointwise multiplication gate in the circuit.
/// See [IValue::pointwise_mul] for more details.
#[derive(PartialEq, Eq)]
pub struct PointwiseMul {
    pub in0: usize,
    pub in1: usize,
    pub out: usize,
}
impl Gate for PointwiseMul {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        check_eq(QM31::pointwise_mul(values[self.in0], values[self.in1]), values[self.out])
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0, self.in1]
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out]
    }
}

impl std::fmt::Debug for PointwiseMul {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = [{}] x [{}]", self.out, self.in0, self.in1)
    }
}

/// Represents an equality gate in the circuit: `[in0] = [in1]`.
#[derive(PartialEq, Eq)]
pub struct Eq {
    pub in0: usize,
    pub in1: usize,
}
impl Gate for Eq {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        check_eq(values[self.in0], values[self.in1])
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0, self.in1]
    }

    fn yields(&self) -> Vec<usize> {
        vec![]
    }
}

impl std::fmt::Debug for Eq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = [{}]", self.in0, self.in1)
    }
}

/// Represents a blake hash gate in the circuit: `([out0], [out1]) = blake([input]; n_bytes)`.
#[derive(PartialEq, Eq)]
pub struct Blake {
    pub input: Vec<[usize; 4]>,
    pub n_bytes: usize,
    pub out0: usize,
    pub out1: usize,
}
impl Gate for Blake {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        let input = self.input.iter().flatten().map(|idx| values[*idx]).collect::<Vec<_>>();
        let n_effective_vars = self.n_bytes.div_ceil(16);
        let main_part = &input[..n_effective_vars];
        let remaining_part = &input[n_effective_vars..];

        let expected_output = blake_qm31(main_part, self.n_bytes);
        check_eq(values[self.out0], expected_output.0)?;
        check_eq(values[self.out1], expected_output.1)?;

        // Sanity check: Check that the remaining input is zero.
        for val in remaining_part {
            check_eq(*val, 0.into())?;
        }

        Ok(())
    }

    fn uses(&self) -> Vec<usize> {
        self.input.iter().flatten().copied().collect()
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out0, self.out1]
    }
}

impl std::fmt::Debug for Blake {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "([{}], [{}]) = blake({:?}; {})", self.out0, self.out1, self.input, self.n_bytes)
    }
}

/// Represents an M31ToU32 gate in the circuit: `(x & 0xFFFF, x >> 16, 0, 0) = M31ToU32(x, 0, 0,
/// 0)`.
#[derive(PartialEq, Eq)]
pub struct M31ToU32 {
    pub input: usize,
    pub out: usize,
}
impl Gate for M31ToU32 {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        let input = values[self.input];

        // Assert that the input is M31.
        let [_, b, c, d] = input.to_m31_array().map(|m| m.0);
        if b != 0 || c != 0 || d != 0 {
            return Err(format!("M31ToU32: input is not M31, got {input}"));
        }
        let expected_output = input.m31_to_u32();
        check_eq(values[self.out], expected_output)
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.input]
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out]
    }
}

impl std::fmt::Debug for M31ToU32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = m31_to_u32([{}])", self.out, self.input)
    }
}

/// Represents a Poseidon2 hash gate: `[out] = poseidon2([in0], [in1])`.
/// Both inputs are full QM31 values; all 8 M31 limbs feed the permutation state.
#[derive(PartialEq, Eq)]
pub struct Poseidon {
    pub in0: usize,
    pub in1: usize,
    pub out: usize,
}
impl Gate for Poseidon {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        use crate::ivalue::qm31_from_u32s;
        let [s0, s1, s2, s3] = poseidon2_value_qm31(values[self.in0], values[self.in1]);
        check_eq(values[self.out], qm31_from_u32s(s0.0, s1.0, s2.0, s3.0))
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0, self.in1]
    }

    fn yields(&self) -> Vec<usize> {
        vec![self.out]
    }
}
impl std::fmt::Debug for Poseidon {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}] = poseidon2([{}], [{}])", self.out, self.in0, self.in1)
    }
}

/// Represents a permutation gate in the circuit.
/// The gate enforces that the input values as a multi-set are equal to the output values
/// as a multi-set.
#[derive(PartialEq, Eq)]
pub struct Permutation {
    pub inputs: Vec<usize>,
    pub outputs: Vec<usize>,
}
impl Gate for Permutation {
    fn check(&self, values: &[QM31]) -> Result<(), String> {
        let mut multi_set = HashMap::new();

        for input in &self.inputs {
            *multi_set.entry(values[*input]).or_insert(0) += 1;
        }

        for output in &self.outputs {
            *multi_set.entry(values[*output]).or_insert(0) -= 1;
        }

        for count in multi_set.values() {
            if *count != 0 {
                return Err("Permutation is not valid".to_string());
            }
        }

        Ok(())
    }

    fn uses(&self) -> Vec<usize> {
        self.inputs.to_vec()
    }

    fn yields(&self) -> Vec<usize> {
        self.outputs.to_vec()
    }
}

impl std::fmt::Debug for Permutation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({:?}) = ({:?})", self.outputs, self.inputs)
    }
}

/// Represents a gate that receives an input wire and "marks" it as output.
#[derive(PartialEq, Eq)]
pub struct Output {
    pub in0: usize,
}
impl Gate for Output {
    fn check(&self, _values: &[QM31]) -> Result<(), String> {
        Ok(())
    }

    fn uses(&self) -> Vec<usize> {
        vec![self.in0]
    }

    fn yields(&self) -> Vec<usize> {
        vec![]
    }
}

impl std::fmt::Debug for Output {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "output [{}]", self.in0)
    }
}

/// Represents a circuit.
#[derive(Default, PartialEq, Eq)]
pub struct Circuit {
    pub n_vars: usize,
    pub add: Vec<Add>,
    pub sub: Vec<Sub>,
    pub mul: Vec<Mul>,
    pub pointwise_mul: Vec<PointwiseMul>,
    pub eq: Vec<Eq>,
    pub blake: Vec<Blake>,
    pub poseidon: Vec<Poseidon>,
    pub m31_to_u32: Vec<M31ToU32>,
    pub permutation: Vec<Permutation>,
    pub output: Vec<Output>,
}

impl Circuit {
    /// Returns an iterator over all the gates in the circuit.
    pub fn all_gates(&self) -> impl Iterator<Item = &dyn Gate> {
        let Circuit {
            n_vars: _,
            add,
            sub,
            mul,
            pointwise_mul,
            eq,
            blake,
            poseidon,
            m31_to_u32,
            permutation,
            output,
        } = self;
        chain!(
            add.iter().map(|g| g as &dyn Gate),
            sub.iter().map(|g| g as &dyn Gate),
            mul.iter().map(|g| g as &dyn Gate),
            pointwise_mul.iter().map(|g| g as &dyn Gate),
            eq.iter().map(|g| g as &dyn Gate),
            blake.iter().map(|g| g as &dyn Gate),
            poseidon.iter().map(|g| g as &dyn Gate),
            m31_to_u32.iter().map(|g| g as &dyn Gate),
            permutation.iter().map(|g| g as &dyn Gate),
            output.iter().map(|g| g as &dyn Gate),
        )
    }

    /// Checks if the circuit is satisfied by the given values.
    pub fn check(&self, values: &[QM31]) -> Result<(), String> {
        for gate in self.all_gates() {
            gate.check(values)?;
        }
        Ok(())
    }

    /// Returns the number of uses and number of yields for each variable (in the context of lookup
    /// terms).
    pub fn compute_multiplicities(&self) -> (Vec<usize>, Vec<usize>) {
        let mut n_uses = vec![0; self.n_vars];
        let mut n_yields = vec![0; self.n_vars];

        for gate in self.all_gates() {
            for use_var in gate.uses() {
                n_uses[use_var] += 1;
            }
            for yield_var in gate.yields() {
                n_yields[yield_var] += 1;
            }
        }

        (n_uses, n_yields)
    }

    /// Verifies that each variable appears exactly once as a yield.
    pub fn check_yields(&self) {
        for (idx, n_yields) in self.compute_multiplicities().1.iter().enumerate() {
            assert!(*n_yields == 1, "Variable {idx} appears {n_yields} times as a yield");
        }
    }
}

impl std::fmt::Debug for Circuit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for gate in self.all_gates() {
            writeln!(f, "{gate:?}")?;
        }
        Ok(())
    }
}
