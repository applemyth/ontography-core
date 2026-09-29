//! Authorization of graph edits.
//!
//! The kernel decides whether an edit is *structurally* admissible; a policy
//! decides whether the principal asking for it is *allowed* to make it. The
//! policy is a trusted parameter of the rewrite rule, just as contract
//! validators are trusted parameters of activation.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::Arc;

use super::definition::Kernel;
use super::frontier::RetirementReason;
use super::occurrence::PackageId;
use super::rewrite::GraphEdit;

/// Who asks for a graph edit.
///
/// The host names principals. The kernel passes the name to the policy and
/// never interprets or authenticates it.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Principal(Arc<str>);

impl Principal {
    /// Names a principal.
    #[must_use]
    pub fn new(name: impl Into<Arc<str>>) -> Self {
        Self(name.into())
    }

    /// Returns the principal's name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Principal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

/// Everything a policy may consult about one proposed edit.
///
/// `after` is already admitted and `retirements` are exactly the live
/// packages the edit would retire, so a policy never has to repeat the
/// kernel's structural or cleanup reasoning.
#[derive(Clone, Copy, Debug)]
pub struct EditContext<'a> {
    /// The principal asking for the edit.
    pub principal: &'a Principal,
    /// The current definition.
    pub before: &'a Kernel,
    /// The proposed edit.
    pub edit: &'a GraphEdit,
    /// The admitted definition the edit would install.
    pub after: &'a Kernel,
    /// The live packages the edit would retire, with their reasons.
    pub retirements: &'a BTreeMap<PackageId, RetirementReason>,
}

/// A policy's reason for refusing an edit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PolicyDenial(Arc<str>);

impl PolicyDenial {
    /// Records why an edit is refused.
    #[must_use]
    pub fn new(reason: impl Into<Arc<str>>) -> Self {
        Self(reason.into())
    }

    /// Returns the reason.
    #[must_use]
    pub fn reason(&self) -> &str {
        &self.0
    }
}

/// Decides which graph edits a workflow accepts.
///
/// A policy is trusted: it must be deterministic and must not depend on
/// mutable external state, so that preparing the same edit against the same
/// state always reaches the same decision. It runs after structural admission
/// and frontier cleanup and before anything is written, so a denial leaves
/// the state unchanged. A panicking policy rejects the edit with
/// [`RewriteError::PolicyPanicked`](super::RewriteError::PolicyPanicked).
pub trait EditPolicy: Send + Sync {
    /// Accepts the edit, or explains why it is refused.
    ///
    /// # Errors
    /// Returns the denial when the principal may not make this edit.
    fn permits(&self, context: &EditContext<'_>) -> Result<(), PolicyDenial>;
}

impl<F> EditPolicy for F
where
    F: Fn(&EditContext<'_>) -> Result<(), PolicyDenial> + Send + Sync,
{
    fn permits(&self, context: &EditContext<'_>) -> Result<(), PolicyDenial> {
        self(context)
    }
}

/// Accepts every structurally admissible edit.
#[derive(Clone, Copy, Debug, Default)]
pub struct PermitAll;

impl EditPolicy for PermitAll {
    fn permits(&self, _: &EditContext<'_>) -> Result<(), PolicyDenial> {
        Ok(())
    }
}

/// Refuses every edit: the graph is fixed. This is the default wherever a
/// policy is not configured.
#[derive(Clone, Copy, Debug, Default)]
pub struct DenyAll;

impl EditPolicy for DenyAll {
    fn permits(&self, _: &EditContext<'_>) -> Result<(), PolicyDenial> {
        Err(PolicyDenial::new("this workflow accepts no graph edits"))
    }
}
