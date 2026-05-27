use std::array;
use std::collections::HashSet;
use std::fs::File;
use std::sync::Arc;

use cairo_air::CairoProof;
use cairo_air::flat_claims::FlatClaim;
use cairo_air::utils::binary_deserialize_from_file;
use cairo_air::verifier::INTERACTION_POW_BITS;
use circuits::context::Context;
use circuits::ivalue::NoValue;
use circuits::ops::Guess;
use circuits::poseidon2_hasher::Poseidon2M31MerkleHasher;
use circuits_stark_verifier::constraint_eval::CircuitEval;
use circuits_stark_verifier::proof::{ProofConfig, empty_proof};
use circuits_stark_verifier::verify::verify;
use itertools::Itertools;
use itertools::zip_eq;
use num_traits::Zero;
use stwo::core::fields::m31::M31;
use stwo::core::fields::qm31::QM31;
use stwo::core::pcs::PcsConfig;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTraceVariant;

use crate::all_components::all_components;
use crate::preprocessed_columns::MAX_SEQUENCE_LOG_SIZE;
use crate::statement::{CairoStatement, MEMORY_VALUES_LIMBS, PUBLIC_DATA_LEN};
use crate::utils::get_proof_file_path;
use crate::verify::{
    CairoVerifierConfig, enabled_components, get_preprocessed_root,
    prepare_cairo_proof_for_circuit_verifier, verify_fixed_cairo_circuit,
};

/// Circuit Verifies a [CairoProof].
pub fn verify_cairo(proof: &CairoProof<Poseidon2M31MerkleHasher>) -> Result<Context<QM31>, String> {
    let FlatClaim { component_enable_bits, component_log_sizes: _, public_data: _ } =
        proof.claim.flatten_claim();

    let components: HashSet<&str> =
        enabled_components::<QM31>(&component_enable_bits).into_keys().collect();

    verify_cairo_with_component_set(proof, components)
}

/// Verifies a [CairoProof] with a given set of components.
pub fn verify_cairo_with_component_set(
    cairo_proof: &CairoProof<Poseidon2M31MerkleHasher>,
    component_set: HashSet<&str>,
) -> Result<Context<QM31>, String> {
    let FlatClaim { component_enable_bits, component_log_sizes: _, public_data: _ } =
        cairo_proof.claim.flatten_claim();
    let components: indexmap::IndexMap<&'static str, Box<dyn CircuitEval<QM31>>> =
        zip_eq(all_components::<QM31>().into_iter(), &component_enable_bits)
            .filter_map(|((component_name, component), &enable_bit)| {
                let component_in_set = component_set.contains(component_name);
                if component_in_set != enable_bit {
                    return Some(Err(format!(
                        "Proof was produced with the wrong components set: expected the component '{}' to be {} according to the component set, but it is {} in the proof.",
                        component_name,
                        if component_in_set { "enabled" } else { "disabled" },
                        if enable_bit { "enabled" } else { "disabled" }
                    )));
                }
                if enable_bit { Some(Ok((component_name, component))) } else { None }
            })
            .try_collect()?;

    let proof_config = ProofConfig::from_components(
        &components,
        component_enable_bits,
        cairo_proof.preprocessed_trace_variant.to_preprocessed_trace().log_sizes(),
        &cairo_proof.extended_stark_proof.proof.config,
        INTERACTION_POW_BITS,
    );

    let (proof, public_data) = prepare_cairo_proof_for_circuit_verifier(cairo_proof, &proof_config);
    let (public_claim, outputs, program) = public_data.pack_into_u32s();
    let outputs = outputs
        .chunks_exact(MEMORY_VALUES_LIMBS)
        .map(|chunk| array::from_fn(|i| M31::from_u32_unchecked(chunk[i])))
        .collect_vec();
    let program = program
        .chunks_exact(MEMORY_VALUES_LIMBS)
        .map(|chunk| array::from_fn(|i| M31::from_u32_unchecked(chunk[i])))
        .collect();

    let ppt_root = cairo_proof.extended_stark_proof.proof.commitments[0];
    let verifier_config = CairoVerifierConfig {
        preprocessed_root: ppt_root.into(),
        proof_config,
        program,
        n_outputs: cairo_proof.claim.public_data.public_memory.output.len(),
        preprocessed_trace_variant: cairo_proof.preprocessed_trace_variant,
    };

    verify_fixed_cairo_circuit(&verifier_config, proof, public_claim, outputs)
}

#[test]
fn test_verify() {
    let mut pcs_config = PcsConfig::default();
    pcs_config.fri_config.fold_step = 4;
    pcs_config.lifting_log_size =
        Some(MAX_SEQUENCE_LOG_SIZE as u32 + pcs_config.fri_config.log_blowup_factor);

    let mut novalue_context = Context::<NoValue>::default();
    let output_len = 1;
    let program_len = 128;
    let flat_claim = vec![M31::zero(); PUBLIC_DATA_LEN + output_len + program_len];
    let outputs = vec![[M31::zero(); MEMORY_VALUES_LIMBS]; output_len];
    let program: Arc<[[M31; MEMORY_VALUES_LIMBS]]> =
        std::iter::repeat_n([M31::zero(); MEMORY_VALUES_LIMBS], program_len).collect();
    let components = all_components();
    let mut statement = CairoStatement::new(
        &mut novalue_context,
        flat_claim,
        outputs,
        program,
        components,
        get_preprocessed_root(20 + pcs_config.fri_config.log_blowup_factor),
        PreProcessedTraceVariant::CanonicalSmall,
    );
    // Remove the pedersen points table component since it requires long preprocessed columns, which
    // are not supported.
    let pedersen_points_index =
        all_components::<NoValue>().get_full("pedersen_points_table_window_bits_18").unwrap().0;
    statement.components.shift_remove("pedersen_points_table_window_bits_18");

    let mut enabled_bits = vec![true; all_components::<NoValue>().len()];
    enabled_bits[pedersen_points_index] = false;
    let config =
        ProofConfig::from_statement(&statement, enabled_bits, &pcs_config, INTERACTION_POW_BITS);

    let empty_proof = empty_proof(&config);

    let proof_vars = empty_proof.guess(&mut novalue_context);
    verify(&mut novalue_context, &proof_vars, &config, &statement);
    novalue_context.finalize_guessed_vars();
    novalue_context.check_vars_used();
    novalue_context.circuit.check_yields();

    println!("Stats: {:?}", novalue_context.stats);
}

#[test]
#[ignore = "proof file was generated with Blake2s; regenerate with Poseidon2M31MerkleChannel once supported"]
fn test_verify_all_opcodes() {
    let proof_path = get_proof_file_path("all_opcode_components");

    let proof_file = File::open(proof_path).unwrap();
    let cairo_proof = binary_deserialize_from_file(&proof_file).unwrap();

    let context = verify_cairo(&cairo_proof).unwrap();
    println!("Stats: {:?}", context.stats);
}
