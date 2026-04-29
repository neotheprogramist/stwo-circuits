use itertools::Itertools;
use num_traits::Zero;
use stwo::core::fields::qm31::QM31;
use stwo::core::fields::{cm31::CM31, m31::M31};

use crate::blake::{HashValue, blake_qm31};
use crate::poseidon2::poseidon2_value_qm31;

#[cfg(test)]
#[path = "ivalue_test.rs"]
pub mod test;

pub fn qm31_from_u32s(a: u32, b: u32, c: u32, d: u32) -> QM31 {
    QM31(CM31(a.into(), b.into()), CM31(c.into(), d.into()))
}

/// Represents a value that can be used in a [`Circuit`](crate::circuit::Circuit).
///
/// We use [QM31] for a circuit with concrete values and [NoValue] for a circuit with no
/// concrete values.
pub trait IValue:
    Sized
    + Copy
    + Clone
    + std::fmt::Debug
    + std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Div<Output = Self>
    + PartialEq
{
    fn from_qm31(value: QM31) -> Self;

    /// Computes pointwise multiplication of two [QM31] values.
    ///
    /// If `a = x0 + x1 * i + x2 * u + x3 * iu`, and `b = y0 + y1 * i + y2 * u + y3 * iu`,
    /// then the pointwise multiplication is
    /// `(x0 * y0) + (x1 * y1) * i + (x2 * y2) * u + (x3 * y3) * iu`.
    fn pointwise_mul(a: Self, b: Self) -> Self;

    /// For each of the four [M31] coordinates, returns `1/x` if `x != 0` and `0` if `x = 0`.
    fn pointwise_inv_or_zero(&self) -> Self;

    /// Returns a [QM31] value that consists of the LSB of each of the four [M31] coordinates.
    fn pointwise_lsb(&self) -> Self;

    fn blake(input: &[Self], n_bytes: usize) -> HashValue<Self>;

    fn poseidon2(a: Self, b: Self) -> Self;

    /// Sorts the input by the u coordinate.
    fn sort_by_u_coordinate(input: &[Self]) -> Vec<Self>;

    /// Converts an M31 value `(x, 0, 0, 0)` into limb representation `(low_u16, high_u15, 0, 0)`.
    fn m31_to_u32(&self) -> Self;
}

impl IValue for QM31 {
    /// Constructs an [IValue] from the given [QM31].
    fn from_qm31(value: QM31) -> Self {
        value
    }

    fn pointwise_mul(x: Self, y: Self) -> Self {
        QM31(CM31(x.0.0 * y.0.0, x.0.1 * y.0.1), CM31(x.1.0 * y.1.0, x.1.1 * y.1.1))
    }

    fn pointwise_inv_or_zero(&self) -> Self {
        QM31(
            CM31(inv_or_zero(self.0.0), inv_or_zero(self.0.1)),
            CM31(inv_or_zero(self.1.0), inv_or_zero(self.1.1)),
        )
    }

    fn pointwise_lsb(&self) -> Self {
        qm31_from_u32s(self.0.0.0 % 2, self.0.1.0 % 2, self.1.0.0 % 2, self.1.1.0 % 2)
    }

    fn blake(input: &[Self], n_bytes: usize) -> HashValue<Self> {
        blake_qm31(input, n_bytes)
    }

    fn poseidon2(a: Self, b: Self) -> Self {
        let [s0, s1, s2, s3] = poseidon2_value_qm31(a, b);
        qm31_from_u32s(s0.0, s1.0, s2.0, s3.0)
    }

    fn sort_by_u_coordinate(input: &[Self]) -> Vec<Self> {
        input.iter().cloned().sorted_by_key(|val| val.1.0).collect_vec()
    }

    fn m31_to_u32(&self) -> Self {
        let x = self.0.0.0;
        qm31_from_u32s(x & 0xFFFF, x >> 16, 0, 0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Ord, PartialOrd)]
pub struct NoValue;

impl IValue for NoValue {
    fn from_qm31(_: QM31) -> Self {
        Self
    }

    fn pointwise_mul(_: Self, _: Self) -> Self {
        Self
    }

    fn pointwise_inv_or_zero(&self) -> Self {
        Self
    }

    fn pointwise_lsb(&self) -> Self {
        Self
    }

    fn m31_to_u32(&self) -> Self {
        Self
    }

    fn blake(_: &[Self], _: usize) -> HashValue<Self> {
        HashValue(Self, Self)
    }

    fn poseidon2(_: Self, _: Self) -> Self {
        Self
    }

    fn sort_by_u_coordinate(input: &[Self]) -> Vec<Self> {
        input.to_vec()
    }
}

impl std::ops::Add for NoValue {
    type Output = NoValue;
    fn add(self, _: NoValue) -> NoValue {
        Self
    }
}
impl std::ops::Sub for NoValue {
    type Output = NoValue;
    fn sub(self, _: NoValue) -> NoValue {
        Self
    }
}
impl std::ops::Mul for NoValue {
    type Output = NoValue;
    fn mul(self, _: NoValue) -> NoValue {
        Self
    }
}
impl std::ops::Div for NoValue {
    type Output = NoValue;
    fn div(self, _: NoValue) -> NoValue {
        Self
    }
}

/// Computes the inverse of a value. Returns zero if the value is zero.
fn inv_or_zero(value: M31) -> M31 {
    if value.is_zero() { M31::zero() } else { value.inverse() }
}
