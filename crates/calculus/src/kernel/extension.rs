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
use super::transition::{ApplyError, PackageView, Transition, TransitionKind};

/// Failure to admit a vocabulary extension. Rejection leaves the state unchanged.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum ExtensionError {
    /// Shared state admission failed: only `StateMismatch` and
    /// `RevisionExhausted` occur here.
    #[error(transparent)]
    Admission(#[from] RewriteError),
    /// The exact state used by preparation is no longer current.
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

impl From<ApplyError> for ExtensionError {
    fn from(error: ApplyError) -> Self {
        match error {
            ApplyError::BindingMismatch => Self::Stale,
            other => Self::Admission(RewriteError::from(other)),
        }
    }
}

/// One admitted extension bound to its exact predecessor.
#[derive(Clone, Debug)]
pub struct PreparedExtension {
    transition: Transition,
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
        self.transition.base.revision
    }

    /// Returns the evaluated transition, for an adapter to apply.
    #[must_use]
    pub const fn transition(&self) -> &Transition {
        &self.transition
    }
}

impl Kernel {
    /// Checks that `next` extends this definition's vocabulary and nothing else.
    ///
    /// # Errors
    ///
    /// Returns the first violated premise.
    pub fn evaluate_extension(&self, next: &Self) -> Result<(), ExtensionError> {
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

    /// Evaluates an extension against a view, producing the transition that
    /// installs `next`'s fingerprint.
    ///
    /// # Errors
    ///
    /// Rejects a view bound to another definition, an exhausted revision, or a
    /// replacement that is not a strict monotone extension.
    pub fn evaluate_extension_transition(
        &self,
        view: &dyn PackageView,
        next: &Self,
    ) -> Result<Transition, ExtensionError> {
        let binding = view.binding();
        self.check_binding(&binding)?;
        self.evaluate_extension(next)?;
        Ok(Transition {
            base: binding,
            kind: TransitionKind::Extension {
                next_fingerprint: *next.fingerprint(),
            },
        })
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
        let transition = self.evaluate_extension_transition(state, &next)?;
        Ok(PreparedExtension {
            transition,
            next_kernel: next,
        })
    }

    /// Installs a prepared extension if its exact predecessor is current.
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
    /// kernel, or a stale predecessor without mutation.
    pub fn commit_extension(
        &self,
        state: &mut State,
        prepared: PreparedExtension,
    ) -> Result<Arc<Self>, ExtensionError> {
        self.check_binding(&state.binding())?;
        self.evaluate_extension(&prepared.next_kernel)?;
        state.apply(self, &prepared.transition)?;
        Ok(prepared.next_kernel)
    }
}
