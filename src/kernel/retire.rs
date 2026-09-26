//! Admitted explicit retirement of live packages.
//!
//! Retirement is a frontier mutation like transfer: it removes one live
//! package from the frontier, records why, and leaves accepted history and
//! every immutable package fact unchanged. It never manufactures consumption.

use std::sync::Arc;

use thiserror::Error;

use super::definition::Kernel;
use super::frontier::{Phase, Position, Retirement, RetirementReason};
use super::occurrence::{ActivationId, PackageId, State};
use super::rewrite::{RewriteError, invalid_state};

/// Failure to admit an explicit retirement. Rejection leaves the state unchanged.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum RetireError {
    /// Shared state admission failed: only `StateMismatch`, `RevisionExhausted`,
    /// and `InvalidState` occur here.
    #[error(transparent)]
    Admission(#[from] RewriteError),
    /// The package is absent from the live frontier.
    #[error("package is not live: {0}")]
    NotLive(PackageId),
    /// The cited evidence is not an accepted activation of this state.
    #[error("retirement evidence is not an accepted activation: {0}")]
    UnknownEvidence(ActivationId),
}

/// Selected canonical facts about one package and its cited evidence.
pub(crate) struct RetireObservation<'a> {
    pub(crate) position: Option<&'a Position>,
    pub(crate) consumed: bool,
    pub(crate) evidence_known: bool,
}

impl Kernel {
    /// Proves one explicit retirement from selected canonical facts.
    ///
    /// The caller binds the current graph and revision and keeps the
    /// observation stable until commit. Returns the holder and phase to record.
    pub(crate) fn evaluate_retire(
        &self,
        package_id: PackageId,
        evidence: Option<ActivationId>,
        observation: RetireObservation<'_>,
    ) -> Result<(Arc<str>, Phase), RetireError> {
        let position = observation
            .position
            .filter(|_| !observation.consumed)
            .ok_or(RetireError::NotLive(package_id))?;
        if self.graph().node(position.holder()).is_none() {
            return Err(invalid_state("live package holder is absent from the graph").into());
        }
        if let Some(evidence) = evidence
            && !observation.evidence_known
        {
            return Err(RetireError::UnknownEvidence(evidence));
        }
        Ok((Arc::clone(&position.holder), position.phase))
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
    pub fn retire(
        &self,
        state: &mut State,
        package_id: PackageId,
        evidence: Option<ActivationId>,
    ) -> Result<Retirement, RetireError> {
        self.check_rewrite_state(state)?;
        let (holder, phase) = self.evaluate_retire(
            package_id,
            evidence,
            RetireObservation {
                position: state.position(package_id),
                consumed: state.package_consumer(package_id).is_some(),
                evidence_known: evidence.is_none_or(|id| state.activation(id).is_some()),
            },
        )?;
        let revision = state
            .revision
            .checked_add(1)
            .ok_or(RewriteError::RevisionExhausted)?;
        let retirement = Retirement {
            reason: RetirementReason::Explicit,
            holder,
            phase,
            revision,
            evidence,
        };
        if state.retirements.contains_key(&package_id) {
            return Err(invalid_state("live package already has a retirement").into());
        }
        state.positions.remove(&package_id);
        state.retirements.insert(package_id, retirement.clone());
        state.revision = revision;
        Ok(retirement)
    }
}
