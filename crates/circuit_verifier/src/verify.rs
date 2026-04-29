use circuits::{blake::HashValue, context::Context, ivalue::IValue, ops::Guess};
use circuits_stark_verifier::{
    proof::{Proof, ProofConfig},
    statement::Statement,
    verify::verify,
};
use stwo::core::{fields::qm31::QM31, pcs::PcsConfig};
use stwo_constraint_framework::preprocessed_columns::PreProcessedColumnId;

use crate::statement::{CircuitStatement, INTERACTION_POW_BITS};

pub struct CircuitPublicData {
    pub output_values: Vec<QM31>,
}

#[derive(Debug, PartialEq)]
pub struct CircuitConfig {
    pub config: PcsConfig,
    pub output_addresses: Vec<usize>,
    pub preprocessed_column_ids: Vec<PreProcessedColumnId>,
    pub preprocessed_column_log_sizes: Vec<u32>,
    pub preprocessed_root: HashValue<QM31>,
}

pub fn build_verification_circuit<Value: IValue>(
    circuit_config: CircuitConfig,
    proof: Proof<Value>,
    public_data: CircuitPublicData,
) -> Result<Context<Value>, String> {
    let mut context = Context::default();
    let statement = CircuitStatement::new(
        &mut context,
        &circuit_config.output_addresses,
        &public_data.output_values,
        circuit_config.preprocessed_column_ids.clone(),
        circuit_config.preprocessed_column_log_sizes.clone(),
        circuit_config.preprocessed_root,
    );

    let proof_config = ProofConfig::from_statement(
        &statement,
        vec![true; statement.get_components().len()],
        &circuit_config.config,
        INTERACTION_POW_BITS,
    );
    let proof_vars = proof.guess(&mut context);

    verify(&mut context, &proof_vars, &proof_config, &statement);
    context.finalize_guessed_vars();
    #[cfg(test)]
    context.circuit.check_yields();

    Ok(context)
}

pub fn verify_circuit(
    circuit_config: CircuitConfig,
    proof: Proof<QM31>,
    public_data: CircuitPublicData,
) -> Result<Context<QM31>, String> {
    let context = build_verification_circuit(circuit_config, proof, public_data)?;
    #[cfg(test)]
    context.check_vars_used();

    if !context.is_circuit_valid() {
        return Err("Verification failed".to_string());
    }
    Ok(context)
}
