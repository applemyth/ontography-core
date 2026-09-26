//! Admitted monotone extension of a definition's closed vocabulary.
//!
//! An extension adds schema node types, object types, authority tags, or
//! exact contracts while leaving the graph, its annotations, and every
//! existing contract unchanged. Every schema and contract check in the
//! kernel is a membership test, so an extension cannot invalidate any
//! accepted state, and the frontier is untouched.

use std::sync::Arc;

use thiserror::Error;

use super::definition::Kernel;
use super::occurrence::State;
use super::rewrite::RewriteError;

/// Failure to admit a vocabulary extension. Rejection leaves the state unchanged.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum ExtensionError {
    /// Shared state admission failed: only `StateMismatch` and
    /// `RevisionExhausted` occur here.
    #[error(transparent)]
    Admission(#[from] RewriteError),
    /// The predecessor revision used by preparation is no longer current.
    #[error("prepared extension is stale")]
    Stale,
    /// The replacement names a different workflow definition.
    #[error("extension changes the definition identity")]
    DefinitionId,
    /// The replacement changes the graph or its annotations.
    #[error("extension changes the graph, annotations, transitions, or roots")]
    Structure,
    /// The replacement drops schema vocabulary.
    #[error("extension removes schema vocabulary")]
    SchemaNarrowed,
    /// An existing contract is absent from the replacement.
    #[error("extension removes contract {0}")]
    ContractRemoved(Arc<str>),
    /// An existing contract changes its object type or validator.
    #[error("extension changes contract {0}")]
    ContractChanged(Arc<str>),
    /// The replacement adds nothing.
    #[error("extension adds no vocabulary")]
    Unchanged,
}

/// One admitted extension bound to its predecessor revision.
#[derive(Clone, Debug)]
pub struct PreparedExtension {
    base_revision: u64,
    next_kernel: Arc<Kernel>,
}

impl PreparedExtension {
    /// Returns the extended definition that would be installed.
    #[must_use]
    pub const fn next_kernel(&self) -> &Arc<Kernel> {
        &self.next_kernel
    }

    /// Returns the predecessor revision used by preparation.
    #[must_use]
    pub const fn base_revision(&self) -> u64 {
        self.base_revision
    }
}

impl Kernel {
    /// Checks that `next` extends this definition's vocabulary and nothing else.
    pub(crate) fn evaluate_extension(&self, next: &Self) -> Result<(), ExtensionError> {
        if self.id() != next.id() {
            return Err(ExtensionError::DefinitionId);
        }
        if self.graph() != next.graph()
            || self.node_definitions() != next.node_definitions()
            || self.edge_definitions() != next.edge_definitions()
            || self.authority_transitions() != next.authority_transitions()
            || self.roots() != next.roots()
        {
            return Err(ExtensionError::Structure);
        }
        if !self.schema().is_subset_of(next.schema()) {
            return Err(ExtensionError::SchemaNarrowed);
        }
        for contract in self.contracts() {
            let Some(replacement) = next.contract(contract.id()) else {
                return Err(ExtensionError::ContractRemoved(Arc::from(contract.id())));
            };
            if replacement.object_type() != contract.object_type()
                || !contract.shares_validator_with(replacement)
            {
                return Err(ExtensionError::ContractChanged(Arc::from(contract.id())));
            }
        }
        if self.fingerprint() == next.fingerprint() {
            return Err(ExtensionError::Unchanged);
        }
        Ok(())
    }

    /// Admits `next` as a vocabulary extension of this definition.
    ///
    /// Existing contracts must be the same values, sharing their validators,
    /// so that every contract identity keeps its meaning.
    ///
    /// # Errors
    ///
    /// Rejects a state bound to another definition, an exhausted revision, or a
    /// replacement that is not a strict monotone extension, without mutation.
    pub fn prepare_extension(
        &self,
        state: &State,
        next: Arc<Self>,
    ) -> Result<PreparedExtension, ExtensionError> {
        self.check_rewrite_state(state)?;
        self.evaluate_extension(&next)?;
        Ok(PreparedExtension {
            base_revision: state.revision,
            next_kernel: next,
        })
    }

    /// Installs a prepared extension if its predecessor revision is current.
    ///
    /// The extension is re-proved against this kernel, so a plan prepared
    /// against another kernel version cannot install a narrower vocabulary.
    /// The frontier and history are unchanged; only the definition binding and
    /// revision advance. The owner must install the returned kernel in the
    /// same externally serialized operation.
    ///
    /// # Errors
    ///
    /// Rejects a mismatched definition, a plan that does not extend this
    /// kernel, or a stale revision without mutation.
    pub fn commit_extension(
        &self,
        state: &mut State,
        prepared: PreparedExtension,
    ) -> Result<Arc<Self>, ExtensionError> {
        self.check_rewrite_state(state)?;
        self.evaluate_extension(&prepared.next_kernel)?;
        if state.revision != prepared.base_revision {
            return Err(ExtensionError::Stale);
        }
        let revision = state
            .revision
            .checked_add(1)
            .ok_or(RewriteError::RevisionExhausted)?;
        state.definition_fingerprint = *prepared.next_kernel.fingerprint();
        state.revision = revision;
        Ok(prepared.next_kernel)
    }
}
