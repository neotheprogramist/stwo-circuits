use crate::circuit_air::components::prelude::*;
use crate::circuit_air::poseidon::poseidon_hash::{
    N_HALF_FULL_ROUNDS, N_PARTIAL_ROUNDS, N_STATE,
    EXTERNAL_ROUND_CONSTS, INTERNAL_ROUND_CONSTS,
    apply_external_round_matrix, apply_internal_round_matrix,
};
use circuits_stark_verifier::constraint_eval::RelationUse;

// 12 columns for in0/in1/out (4 M31 limbs each as QM31)
// 650 intermediate witness columns for the full Poseidon2 computation:
//   - 4 full rounds × 3 steps × 16 state elements = 192
//   - 14 partial rounds × (3 + 16) = 266
//   - 4 full rounds × 3 steps × 16 state elements = 192
pub const N_TRACE_COLUMNS: usize = 662;
// 3 logup terms (use in0, use in1, yield out) → 2 pairs → 2 × SECURE_EXTENSION_DEGREE = 8
pub const N_INTERACTION_COLUMNS: usize = 8;
pub const RELATION_USES_PER_ROW: [RelationUse; 1] = [RelationUse { relation_id: "gate", uses: 3 }];

pub struct Eval {
    pub claim: Claim,
    pub common_lookup_elements: relations::CommonLookupElements,
}

#[derive(Copy, Clone, Serialize, Deserialize)]
pub struct Claim {
    pub log_size: u32,
}
impl Claim {
    pub fn log_sizes(&self) -> TreeVec<Vec<u32>> {
        let trace_log_sizes = vec![self.log_size; N_TRACE_COLUMNS];
        let interaction_log_sizes = vec![self.log_size; N_INTERACTION_COLUMNS];
        TreeVec::new(vec![vec![], trace_log_sizes, interaction_log_sizes])
    }

    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_u64(self.log_size as u64);
    }
}

#[derive(Copy, Clone, Serialize, Deserialize)]
pub struct InteractionClaim {
    pub claimed_sum: SecureField,
}
impl InteractionClaim {
    pub fn mix_into(&self, channel: &mut impl Channel) {
        channel.mix_felts(&[self.claimed_sum]);
    }
}

pub type Component = FrameworkComponent<Eval>;

impl FrameworkEval for Eval {
    fn log_size(&self) -> u32 {
        self.claim.log_size
    }

    fn max_constraint_log_degree_bound(&self) -> u32 {
        self.log_size() + 1
    }

    fn evaluate<E: EvalAtRow>(&self, mut eval: E) -> E {
        let gate_relation_id = E::F::from(M31::from(378353459));

        // Preprocessed columns: addresses and output multiplicity
        let in0_address = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_in0_address".to_owned(),
        });
        let in1_address = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_in1_address".to_owned(),
        });
        let out_address = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_out_address".to_owned(),
        });
        let out_mults = eval.get_preprocessed_column(PreProcessedColumnId {
            id: "poseidon_out_mults".to_owned(),
        });

        // in0/in1: full QM31 inputs (all 4 limbs participate in the lookup).
        // Only limb0 feeds the Poseidon permutation; limbs 1..3 are passed through.
        let in0_limb0 = eval.next_trace_mask();
        let in0_limb1 = eval.next_trace_mask();
        let in0_limb2 = eval.next_trace_mask();
        let in0_limb3 = eval.next_trace_mask();
        // in1: same structure
        let in1_limb0 = eval.next_trace_mask();
        let in1_limb1 = eval.next_trace_mask();
        let in1_limb2 = eval.next_trace_mask();
        let in1_limb3 = eval.next_trace_mask();
        // out: same structure
        let out_limb0 = eval.next_trace_mask();
        let out_limb1 = eval.next_trace_mask();
        let out_limb2 = eval.next_trace_mask();
        let out_limb3 = eval.next_trace_mask();

        // Initial state layout (Kakarot-compatible for pure M31 inputs):
        //   [in0.l0, in1.l0, in0.l1, in0.l2, in0.l3, in1.l1, in1.l2, in1.l3, 0, ...]
        let zero = E::F::from(M31::from(0u32));
        let mut state: [E::F; N_STATE] = std::array::from_fn(|i| match i {
            0 => in0_limb0.clone(),
            1 => in1_limb0.clone(),
            2 => in0_limb1.clone(),
            3 => in0_limb2.clone(),
            4 => in0_limb3.clone(),
            5 => in1_limb1.clone(),
            6 => in1_limb2.clone(),
            7 => in1_limb3.clone(),
            _ => zero.clone(),
        });

        // Initial external round matrix (linear, no new witness columns)
        apply_external_round_matrix(&mut state);

        // First 4 full rounds
        for round in 0..N_HALF_FULL_ROUNDS {
            for i in 0..N_STATE {
                state[i] = state[i].clone() + E::F::from(EXTERNAL_ROUND_CONSTS[round][i]);
            }
            let before_sbox = state.clone();

            // x^2: constrain and store witness
            state = std::array::from_fn(|i| state[i].clone() * state[i].clone());
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }

            // x^4: constrain and store witness
            state = std::array::from_fn(|i| state[i].clone() * state[i].clone());
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }

            // x^5 = x^4 * x_original, then external matrix
            state = std::array::from_fn(|i| state[i].clone() * before_sbox[i].clone());
            apply_external_round_matrix(&mut state);
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }
        }

        // 14 partial rounds (S-box only on state[0])
        for r in 0..N_PARTIAL_ROUNDS {
            state[0] = state[0].clone() + E::F::from(INTERNAL_ROUND_CONSTS[r]);
            let before_sbox_0 = state[0].clone();

            // state[0]^2
            state[0] = state[0].clone() * state[0].clone();
            let w = eval.next_trace_mask();
            eval.add_constraint(state[0].clone() - w.clone());
            state[0] = w;

            // state[0]^4
            state[0] = state[0].clone() * state[0].clone();
            let w = eval.next_trace_mask();
            eval.add_constraint(state[0].clone() - w.clone());
            state[0] = w;

            // state[0]^5
            state[0] = state[0].clone() * before_sbox_0;
            let w = eval.next_trace_mask();
            eval.add_constraint(state[0].clone() - w.clone());
            state[0] = w;

            // Internal round matrix, store all 16 state elements
            apply_internal_round_matrix(&mut state);
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }
        }

        // Last 4 full rounds
        for round in 0..N_HALF_FULL_ROUNDS {
            for i in 0..N_STATE {
                state[i] = state[i].clone()
                    + E::F::from(EXTERNAL_ROUND_CONSTS[round + N_HALF_FULL_ROUNDS][i]);
            }
            let before_sbox = state.clone();

            state = std::array::from_fn(|i| state[i].clone() * state[i].clone());
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }

            state = std::array::from_fn(|i| state[i].clone() * state[i].clone());
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }

            state = std::array::from_fn(|i| state[i].clone() * before_sbox[i].clone());
            apply_external_round_matrix(&mut state);
            for i in 0..N_STATE {
                let w = eval.next_trace_mask();
                eval.add_constraint(state[i].clone() - w.clone());
                state[i] = w;
            }
        }

        // Final constraints: out encodes state[0..3] as QM31 limbs
        eval.add_constraint(out_limb0.clone() - state[0].clone());
        eval.add_constraint(out_limb1.clone() - state[1].clone());
        eval.add_constraint(out_limb2.clone() - state[2].clone());
        eval.add_constraint(out_limb3.clone() - state[3].clone());

        // Logup: use in0, use in1, yield out
        eval.add_to_relation(RelationEntry::new(
            &self.common_lookup_elements,
            E::EF::one(),
            &[gate_relation_id.clone(), in0_address, in0_limb0, in0_limb1, in0_limb2, in0_limb3],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.common_lookup_elements,
            E::EF::one(),
            &[gate_relation_id.clone(), in1_address, in1_limb0, in1_limb1, in1_limb2, in1_limb3],
        ));
        eval.add_to_relation(RelationEntry::new(
            &self.common_lookup_elements,
            -E::EF::from(out_mults),
            &[gate_relation_id, out_address, out_limb0, out_limb1, out_limb2, out_limb3],
        ));

        eval.finalize_logup_in_pairs();
        eval
    }
}