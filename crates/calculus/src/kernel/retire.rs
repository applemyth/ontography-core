//! Admitted explicit retirement of live packages.
//!
//! Retirement is a frontier mutation like transfer: it removes one live
//! package from the frontier, records why, and leaves accepted history and
//! every immutable package fact unchanged. It never manufactures consumption.

use thiserror::Error;

use super::definition::Kernel;
use super::frontier::{Retirement, RetirementReason};
use super::occurrence::{ActivationId, PackageId, PackageRecord, State};
use super::rewrite::{RewriteError, invalid_state};
use super::transition::{PackageView, Transition, TransitionKind};

/// Failure to admit an explicit retirement. Rejection leaves the state unchanged.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum RetireError {
    /// Shared state admission failed: only `StateMismatch`, `RevisionExhausted`,
    /// `Stale`, and `InvalidState` occur here.
    #[error(transparent)]
    Admission(#[from] RewriteError),
    /// The package is absent from the live frontier.
    #[error("package is not live: {0}")]
    NotLive(PackageId),
    /// The cited evidence is not an accepted activation of this state.
    #[error("retirement evidence is not an accepted activation: {0}")]
    UnknownEvidence(ActivationId),
}

impl Kernel {
    /// Evaluates one explicit retirement against a view without mutating anything.
    ///
    /// # Errors
    ///
    /// Rejects a view bound to another definition, an exhausted revision, a
    /// package that is not live, or unknown evidence.
    pub fn evaluate_retire(
        &self,
        view: &dyn PackageView,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Transition, RetireError> {
        let binding = view.binding();
        let successor = self.check_binding(&binding)?;
        let record = view
            .record(package_id)
            .filter(PackageRecord::is_live)
            .ok_or(RetireError::NotLive(package_id))?;
        if self.graph().node(record.holder()).is_none() {
            return Err(invalid_state("live package holder is absent from the graph").into());
        }
        if let Some(evidence) = evidence
            && !view.activation_known(evidence)
        {
            return Err(RetireError::UnknownEvidence(evidence));
        }
        let retirement = Retirement::new(RetirementReason::Explicit, successor, evidence);
        Ok(Transition {
            base: binding,
            kind: TransitionKind::Retire {
                package: package_id,
                retirement,
            },
        })
    }

    /// Retires one live package atomically, citing optional evidence.
    ///
    /// The evidence must be an accepted activation of `state`, such as a timer
    /// or operator activation explaining the retirement. Only its existence is
    /// checked: activations carry no revision, so the kernel cannot verify
    /// that the evidence was accepted before the retirement.
    ///
    /// # Errors
    ///
    /// Rejects a state bound to another definition, an exhausted revision, a
    /// package that is not live, or unknown evidence, without mutation.
    ///
    /// # Panics
    ///
    /// Panics if the evaluated transition does not apply to the state it was
    /// evaluated against, which cannot happen.
    pub fn retire(
        &self,
        state: &mut State,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Retirement, RetireError> {
        let transition = self.evaluate_retire(state, package_id, evidence)?;
        state
            .apply(self, &transition)
            .expect("a transition evaluated against a state applies to it");
        let TransitionKind::Retire { retirement, .. } = transition.kind else {
            unreachable!("a retire transition retires exactly one package");
        };
        Ok(retirement)
    }
}
