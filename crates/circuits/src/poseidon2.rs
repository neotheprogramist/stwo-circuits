use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;

use crate::circuit::Poseidon;
use crate::context::{Context, Var};
use crate::eval;
use crate::ivalue::{IValue, qm31_from_u32s};

pub const N_STATE: usize = 16;
pub const RATE: usize = 8;
pub const N_PARTIAL_ROUNDS: usize = 14;
pub const N_HALF_FULL_ROUNDS: usize = 4;

pub const RC_EXTERNAL: [[u32; N_STATE]; 8] = [
    [
        0x768bab52, 0x70e0ab7d, 0x3d266c8a, 0x6da42045, 0x600fef22, 0x41dace6b, 0x64f9bdd4,
        0x5d42d4fe, 0x76b1516d, 0x6fc9a717, 0x70ac4fb6, 0x00194ef6, 0x22b644e2, 0x1f7916d5,
        0x47581be2, 0x2710a123,
    ],
    [
        0x6284e867, 0x018d3afe, 0x5df99ef3, 0x4c1e467b, 0x566f6abc, 0x2994e427, 0x538a6d42,
        0x5d7bf2cf, 0x7fda2dab, 0x0fd854c4, 0x46922fca, 0x3d7763a1, 0x19fd05ca, 0x0a4bbb43,
        0x15075851, 0x3d903d76,
    ],
    [
        0x2d290ff7, 0x40809fa0, 0x59dac6ec, 0x127927a2, 0x6bbf0ea0, 0x0294140f, 0x24742976,
        0x6e84c081, 0x22484f4a, 0x354cae59, 0x0453ffe1, 0x3f47a3cc, 0x0088204e, 0x6066e109,
        0x3b7c4b80, 0x6b55665d,
    ],
    [
        0x3bc4b897, 0x735bf378, 0x508daf42, 0x1884fc2b, 0x7214f24c, 0x7498be0a, 0x1a60e640,
        0x3303f928, 0x29b46376, 0x5c96bb68, 0x65d097a5, 0x1d358e9f, 0x4a9a9017, 0x4724cf76,
        0x347af70f, 0x1e77e59a,
    ],
    [
        0x57090613, 0x1fa42108, 0x17bbef50, 0x1ff7e11c, 0x047b24ca, 0x4e140275, 0x4fa086f5,
        0x079b309c, 0x1159bd47, 0x6d37e4e5, 0x075d8dce, 0x12121ca0, 0x7f6a7c40, 0x68e182ba,
        0x5493201b, 0x0444a80e,
    ],
    [
        0x0064f4c6, 0x6467abe6, 0x66975762, 0x2af68f9b, 0x345b33be, 0x1b70d47f, 0x053db717,
        0x381189cb, 0x43b915f8, 0x20df3694, 0x0f459d26, 0x77a0e97b, 0x2f73e739, 0x1876c2f9,
        0x65a0e29a, 0x4cabefbe,
    ],
    [
        0x5abd1268, 0x4d34a760, 0x12771799, 0x69a0c9ac, 0x39091e55, 0x7f611cd0, 0x3af055da,
        0x7ac0bbdf, 0x6e0f3a24, 0x41e3b6f7, 0x49b3756d, 0x568bc538, 0x20c079d8, 0x1701c72c,
        0x7670dc6c, 0x5a439035,
    ],
    [
        0x7c93e00e, 0x561fbb4d, 0x1178907b, 0x02737406, 0x32fb24f1, 0x6323b60a, 0x6ab12418,
        0x42c99cea, 0x155a0b97, 0x53d1c6aa, 0x2bd20347, 0x279b3d73, 0x4f5f3c70, 0x0245af6c,
        0x238359d3, 0x49966a59,
    ],
];
pub const RC_INTERNAL: [u32; N_PARTIAL_ROUNDS] = [
    0x7f7ec4bf, 0x0421926f, 0x5198e669, 0x34db3148, 0x4368bafd, 0x66685c7f, 0x78d3249a, 0x60187881,
    0x76dad67a, 0x0690b437, 0x1ea95311, 0x40e5369a, 0x38f103fc, 0x1d226a21,
];
pub const INTERNAL_DIAG: [u32; N_STATE] = [
    0x07b80ac4, 0x6bd9cb33, 0x48ee3f9f, 0x4f63dd19, 0x18c546b3, 0x5af89e8b, 0x4ff23de8, 0x4f78aaf6,
    0x53bdc6d4, 0x5c59823e, 0x2a471c72, 0x4c975e79, 0x58dc64d4, 0x06e9315d, 0x2cf32286, 0x2fb6755d,
];

pub trait Poseidon2Backend {
    type Elem: Clone;

    fn zero(&mut self) -> Self::Elem;
    fn constant(&mut self, value: u32) -> Self::Elem;
    fn add(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem;
    fn mul(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem;

    fn witness(&mut self, value: Self::Elem) -> Self::Elem {
        value
    }

    fn witness_state(&mut self, state: &mut [Self::Elem; N_STATE]) {
        for value in state.iter_mut() {
            *value = self.witness(value.clone());
        }
    }
}

fn add3<B: Poseidon2Backend>(
    backend: &mut B,
    a: B::Elem,
    b: B::Elem,
    c: B::Elem,
) -> B::Elem {
    let t = backend.add(a, b);
    backend.add(t, c)
}

fn add4<B: Poseidon2Backend>(
    backend: &mut B,
    a: B::Elem,
    b: B::Elem,
    c: B::Elem,
    d: B::Elem,
) -> B::Elem {
    let t = add3(backend, a, b, c);
    backend.add(t, d)
}

pub fn apply_m4<B: Poseidon2Backend>(backend: &mut B, x: [B::Elem; 4]) -> [B::Elem; 4] {
    let t0 = backend.add(x[0].clone(), x[1].clone());
    let t02 = backend.add(t0.clone(), t0.clone());
    let t1 = backend.add(x[2].clone(), x[3].clone());
    let t12 = backend.add(t1.clone(), t1.clone());
    let t2 = add3(backend, x[1].clone(), x[1].clone(), t1);
    let t3 = add3(backend, x[3].clone(), x[3].clone(), t0);
    let t4 = add3(backend, t12.clone(), t12, t3.clone());
    let t5 = add3(backend, t02.clone(), t02, t2.clone());
    let t6 = backend.add(t3, t5.clone());
    let t7 = backend.add(t2, t4.clone());
    [t6, t5, t7, t4]
}

pub fn apply_external_round_matrix<B: Poseidon2Backend>(
    backend: &mut B,
    state: &mut [B::Elem; N_STATE],
) {
    for i in 0..4 {
        let base = 4 * i;
        let [a, b, c, d] = apply_m4(
            backend,
            [
                state[base].clone(),
                state[base + 1].clone(),
                state[base + 2].clone(),
                state[base + 3].clone(),
            ],
        );
        state[base] = a;
        state[base + 1] = b;
        state[base + 2] = c;
        state[base + 3] = d;
    }
    for j in 0..4 {
        let s = add4(
            backend,
            state[j].clone(),
            state[j + 4].clone(),
            state[j + 8].clone(),
            state[j + 12].clone(),
        );
        for i in 0..4 {
            state[4 * i + j] = backend.add(state[4 * i + j].clone(), s.clone());
        }
    }
}

pub fn apply_internal_round_matrix<B: Poseidon2Backend>(
    backend: &mut B,
    state: &mut [B::Elem; N_STATE],
) {
    let mut sum = state[0].clone();
    for x in state.iter().skip(1) {
        sum = backend.add(sum, x.clone());
    }
    for (x, &diag) in state.iter_mut().zip(INTERNAL_DIAG.iter()) {
        let diag = backend.constant(diag);
        let prod = backend.mul(x.clone(), diag);
        *x = backend.add(prod, sum.clone());
    }
}

pub fn poseidon2_permutation<B: Poseidon2Backend>(
    backend: &mut B,
    mut state: [B::Elem; N_STATE],
) -> [B::Elem; N_STATE] {
    apply_external_round_matrix(backend, &mut state);

    for rc_row in &RC_EXTERNAL[..N_HALF_FULL_ROUNDS] {
        for (x, &rc) in state.iter_mut().zip(rc_row.iter()) {
            let rc = backend.constant(rc);
            *x = backend.add(x.clone(), rc);
        }
        let before = state.clone();

        for x in state.iter_mut() {
            *x = backend.mul(x.clone(), x.clone());
            *x = backend.witness(x.clone());
        }
        for x in state.iter_mut() {
            *x = backend.mul(x.clone(), x.clone());
            *x = backend.witness(x.clone());
        }
        for (x, bx) in state.iter_mut().zip(before.iter()) {
            *x = backend.mul(x.clone(), bx.clone());
        }
        apply_external_round_matrix(backend, &mut state);
        backend.witness_state(&mut state);
    }

    for &rc in RC_INTERNAL.iter() {
        let rc = backend.constant(rc);
        state[0] = backend.add(state[0].clone(), rc);
        let before = state[0].clone();

        state[0] = backend.mul(state[0].clone(), state[0].clone());
        state[0] = backend.witness(state[0].clone());
        state[0] = backend.mul(state[0].clone(), state[0].clone());
        state[0] = backend.witness(state[0].clone());
        state[0] = backend.mul(state[0].clone(), before);
        state[0] = backend.witness(state[0].clone());

        apply_internal_round_matrix(backend, &mut state);
        backend.witness_state(&mut state);
    }

    for rc_row in &RC_EXTERNAL[N_HALF_FULL_ROUNDS..] {
        for (x, &rc) in state.iter_mut().zip(rc_row.iter()) {
            let rc = backend.constant(rc);
            *x = backend.add(x.clone(), rc);
        }
        let before = state.clone();

        for x in state.iter_mut() {
            *x = backend.mul(x.clone(), x.clone());
            *x = backend.witness(x.clone());
        }
        for x in state.iter_mut() {
            *x = backend.mul(x.clone(), x.clone());
            *x = backend.witness(x.clone());
        }
        for (x, bx) in state.iter_mut().zip(before.iter()) {
            *x = backend.mul(x.clone(), bx.clone());
        }
        apply_external_round_matrix(backend, &mut state);
        backend.witness_state(&mut state);
    }

    state
}

pub fn qm31_inputs_to_state(a: QM31, b: QM31) -> [M31; N_STATE] {
    let zero = M31::from_u32_unchecked(0);
    let mut state = [zero; N_STATE];
    state[0] = a.0.0;
    state[1] = b.0.0;
    state[2] = a.0.1;
    state[3] = a.1.0;
    state[4] = a.1.1;
    state[5] = b.0.1;
    state[6] = b.1.0;
    state[7] = b.1.1;
    state
}

#[derive(Default)]
pub struct M31Backend;

impl Poseidon2Backend for M31Backend {
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
}

pub struct CircuitBackend<'a, Value: IValue> {
    ctx: &'a mut Context<Value>,
}

impl<'a, Value: IValue> CircuitBackend<'a, Value> {
    pub fn new(ctx: &'a mut Context<Value>) -> Self {
        Self { ctx }
    }
}

impl<Value: IValue> Poseidon2Backend for CircuitBackend<'_, Value> {
    type Elem = Var;

    fn zero(&mut self) -> Self::Elem {
        self.ctx.zero()
    }

    fn constant(&mut self, value: u32) -> Self::Elem {
        self.ctx.constant(qm31_from_u32s(value, 0, 0, 0))
    }

    fn add(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem {
        eval!(self.ctx, (a) + (b))
    }

    fn mul(&mut self, a: Self::Elem, b: Self::Elem) -> Self::Elem {
        eval!(self.ctx, (a) * (b))
    }
}

/// Applies the full Poseidon2 permutation to an arbitrary 16-element circuit state.
pub fn poseidon2_permutation_circuit<Value: IValue>(
    ctx: &mut Context<Value>,
    state: [Var; N_STATE],
) -> [Var; N_STATE] {
    poseidon2_permutation(&mut CircuitBackend::new(ctx), state)
}

/// Poseidon2 hash for two field elements (state[0]=a, state[1]=b).
/// Matches `Poseidon2.sol` parameters for M31.
pub fn poseidon2_hash_two<Value: IValue>(ctx: &mut Context<Value>, a: Var, b: Var) -> Var {
    let zero = ctx.zero();
    let mut state = [zero; N_STATE];
    state[0] = a;
    state[1] = b;
    poseidon2_permutation_circuit(ctx, state)[0]
}

/// Runs Poseidon2 permutation on an arbitrary 16-element u32 state and returns all 16 outputs.
pub fn poseidon2_value_from_state(state: [u32; N_STATE]) -> [u32; N_STATE] {
    poseidon2_permutation(&mut M31Backend, state.map(M31::from_u32_unchecked)).map(|x| x.0)
}

/// Computes Poseidon2 for two QM31 inputs using all 8 M31 limbs.
/// State layout preserves Kakarot compatibility for pure M31 inputs:
///   state = [a.l0, b.l0, a.l1, a.l2, a.l3, b.l1, b.l2, b.l3, 0, ..., 0]
/// When a.l1==a.l2==a.l3==b.l1==b.l2==b.l3==0, this equals poseidon2_value_full(a.l0, b.l0).
pub fn poseidon2_value_qm31(a: QM31, b: QM31) -> [M31; 4] {
    let state = poseidon2_permutation(&mut M31Backend, qm31_inputs_to_state(a, b));
    [state[0], state[1], state[2], state[3]]
}

/// Absorbs one block of RATE M31 values into the sponge state and applies the permutation.
pub fn poseidon2_absorb_circuit<Value: IValue>(
    ctx: &mut Context<Value>,
    mut state: [Var; N_STATE],
    block: [Var; RATE],
) -> [Var; N_STATE] {
    let mut backend = CircuitBackend::new(ctx);
    for i in 0..RATE {
        state[i] = backend.add(state[i], block[i]);
    }
    poseidon2_permutation(&mut backend, state)
}

/// Poseidon2 sponge over a fixed-length sequence of blocks.
///
/// Each block is RATE M31 values. The number of blocks is fixed at circuit-build time
/// (pad with zero blocks to reach the desired maximum). Returns the first 4 state
/// elements after absorbing all blocks — the digest.
pub fn poseidon2_sponge_circuit<Value: IValue>(
    ctx: &mut Context<Value>,
    blocks: &[[Var; RATE]],
) -> [Var; N_STATE] {
    let zero = ctx.zero();
    let mut state = [zero; N_STATE];
    for &block in blocks {
        state = poseidon2_absorb_circuit(ctx, state, block);
    }
    state
}

/// Adds a single Poseidon2 gate to the circuit: out = poseidon2(in0.m31, in1.m31).
pub fn poseidon_gate<Value: IValue>(ctx: &mut Context<Value>, a: Var, b: Var) -> Var {
    let a_val = ctx.get(a);
    let b_val = ctx.get(b);
    let out_val = Value::poseidon2(a_val, b_val);
    let out_var = ctx.new_var(out_val);
    ctx.circuit.poseidon.push(Poseidon { in0: a.idx, in1: b.idx, out: out_var.idx });
    out_var
}

#[cfg(test)]
#[path = "poseidon2_test.rs"]
mod test;
