use circuits::poseidon2_hasher::{Poseidon2M31Channel, Poseidon2M31MerkleChannel};
use stwo::core::air::Component;
use stwo::core::channel::Channel;
use stwo::core::pcs::{CommitmentSchemeVerifier, TreeVec};
use stwo::core::verifier::verify;

use crate::simple_air::{INTERACTION_POW_BITS, LOG_SIZE_LONG, LOG_SIZE_SHORT, create_proof};
use crate::simple_statement::COMPONENT_ENABLE_BITS;
use circuits::ivalue::qm31_from_u32s;
use circuits_stark_verifier::proof::Claim;
use circuits_stark_verifier::proof_from_stark_proof::pack_enable_bits;

#[test]
fn verify_simple_proof() {
    let (
        components,
        Claim { packed_component_log_sizes, claimed_sums },
        config,
        proof,
        interaction_pow_nonce,
        channel_salt,
    ) = create_proof();

    // Verify.
    let verifier_channel = &mut Poseidon2M31Channel::default();
    verifier_channel.mix_felts(&[channel_salt.into()]);
    config.mix_into(verifier_channel);
    let commitment_scheme = &mut CommitmentSchemeVerifier::<Poseidon2M31MerkleChannel>::new(config);

    // Retrieve the expected column sizes in each commitment interaction, from the AIR.
    let sizes = TreeVec::concat_cols(components.iter().map(|c| c.trace_log_degree_bounds()));
    let preprocessed_column_sizes = vec![LOG_SIZE_SHORT, LOG_SIZE_LONG];

    commitment_scheme.commit(
        proof.proof.commitments[0],
        &preprocessed_column_sizes,
        verifier_channel,
    );

    verifier_channel.mix_felts(&[qm31_from_u32s(COMPONENT_ENABLE_BITS.len() as u32, 0, 0, 0)]);
    verifier_channel.mix_felts(&pack_enable_bits(&COMPONENT_ENABLE_BITS));
    verifier_channel.mix_felts(&packed_component_log_sizes);
    verifier_channel.mix_felts(&[]);
    commitment_scheme.commit(proof.proof.commitments[1], &sizes[1], verifier_channel);
    verifier_channel.verify_pow_nonce(INTERACTION_POW_BITS, interaction_pow_nonce);
    verifier_channel.mix_u64(interaction_pow_nonce);
    verifier_channel.mix_felts(&claimed_sums);
    commitment_scheme.commit(proof.proof.commitments[2], &sizes[2], verifier_channel);
    verify(
        &components.iter().map(|c| c.as_ref()).collect::<Vec<&dyn Component>>(),
        verifier_channel,
        commitment_scheme,
        proof.proof,
    )
    .unwrap();
}
