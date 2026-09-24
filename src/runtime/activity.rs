//! Optional execution telemetry, independent of graph admission and durable state.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use crate::PackageId;

/// One executable's self-reported invocation that is currently in progress.
///
/// This is operational telemetry, not an admitted activation, package
/// reservation, or proof that external work is running. Inputs are the exact
/// identities supplied by the executable and are not checked by the kernel.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InvocationActivity {
    id: u64,
    inputs: Arc<[PackageId]>,
    description: Arc<str>,
}

impl InvocationActivity {
    /// Returns an identity local to this execution instance.
    #[must_use]
    pub const fn id(&self) -> u64 {
        self.id
    }

    /// Returns the exact reported input package identities, in supplied order.
    ///
    /// Spontaneous or entry-input work may report no package inputs.
    #[must_use]
    pub fn inputs(&self) -> &[PackageId] {
        &self.inputs
    }

    /// Returns the executable's current description of this work.
    #[must_use]
    pub fn description(&self) -> &str {
        &self.description
    }
}

/// An in-memory observation of one execution's reported work.
///
/// This snapshot is internally coherent but is not atomic with the graph
/// frontier or execution status. It is reset when an execution is relaunched.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ActivitySnapshot {
    reported: bool,
    invocations: Vec<InvocationActivity>,
}

impl ActivitySnapshot {
    /// Reports whether the executable opted into activity reporting.
    ///
    /// When false, an empty invocation list means unknown activity. When true,
    /// it means the executable currently reports no active invocations.
    #[must_use]
    pub const fn reported(&self) -> bool {
        self.reported
    }

    /// Returns active reports ordered by execution-local invocation identity.
    #[must_use]
    pub fn invocations(&self) -> &[InvocationActivity] {
        &self.invocations
    }
}

/// Cloneable reporting capability for one executable's operational activity.
///
/// Obtaining this from an execution context enables reporting. Multiple clones
/// may report concurrent invocations independently. Reports never reserve or
/// consume packages and do not change graph semantics or the durable ledger.
#[derive(Clone, Debug)]
pub struct ActivityReporter {
    tracker: Arc<ActivityTracker>,
}

impl ActivityReporter {
    /// Reports work until the returned guard is dropped.
    ///
    /// `inputs` should contain the package identities actually used by this
    /// invocation, or be empty for work without a package trigger. A stopped
    /// execution returns an inert guard; detached reporters cannot revive it.
    ///
    /// # Panics
    /// Panics if this execution exhausts its `u64` invocation identity space.
    pub fn begin<I>(&self, inputs: I, description: impl Into<Arc<str>>) -> InvocationGuard
    where
        I: IntoIterator<Item = PackageId>,
    {
        // Run caller-supplied conversion/iteration outside the state lock.
        let inputs = inputs.into_iter().collect::<Arc<[_]>>();
        let description = description.into();
        let mut state = self
            .tracker
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let id = if state.open {
            let id = state.next_id;
            state.next_id = id
                .checked_add(1)
                .expect("execution invocation identity space is exhausted");
            state.invocations.insert(
                id,
                InvocationActivity {
                    id,
                    inputs,
                    description,
                },
            );
            Some(id)
        } else {
            None
        };
        InvocationGuard {
            tracker: Arc::clone(&self.tracker),
            id,
        }
    }
}

/// Lifetime guard for one self-reported invocation.
///
/// Dropping the guard removes only its report, including during error return,
/// cancellation, or unwinding. The host also clears all reports on terminal
/// execution, forced abort, or host destruction, even if a guard was detached.
#[derive(Debug)]
#[must_use = "dropping the guard immediately finishes the activity report"]
pub struct InvocationGuard {
    tracker: Arc<ActivityTracker>,
    id: Option<u64>,
}

impl InvocationGuard {
    /// Updates the description if this invocation and execution are still live.
    pub fn set_description(&self, description: impl Into<Arc<str>>) {
        let description = description.into();
        if let Some(id) = self.id {
            let mut state = self
                .tracker
                .state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if let Some(invocation) = state.invocations.get_mut(&id) {
                invocation.description = description;
            }
        }
    }
}

impl Drop for InvocationGuard {
    fn drop(&mut self) {
        if let Some(id) = self.id {
            self.tracker
                .state
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner)
                .invocations
                .remove(&id);
        }
    }
}

#[derive(Debug)]
struct ActivityState {
    open: bool,
    reported: bool,
    next_id: u64,
    invocations: BTreeMap<u64, InvocationActivity>,
}

#[derive(Debug)]
pub(crate) struct ActivityTracker {
    state: Mutex<ActivityState>,
}

impl ActivityTracker {
    pub(crate) fn new() -> Self {
        Self {
            state: Mutex::new(ActivityState {
                open: true,
                reported: false,
                next_id: 1,
                invocations: BTreeMap::new(),
            }),
        }
    }

    pub(crate) fn reporter(self: &Arc<Self>) -> ActivityReporter {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        if state.open {
            state.reported = true;
        }
        ActivityReporter {
            tracker: Arc::clone(self),
        }
    }

    pub(crate) fn snapshot(&self) -> ActivitySnapshot {
        let state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        ActivitySnapshot {
            reported: state.reported,
            invocations: state.invocations.values().cloned().collect(),
        }
    }

    pub(crate) fn close(&self) {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        state.open = false;
        state.invocations.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ActivationId;

    #[test]
    fn simultaneous_invocations_keep_exact_inputs_and_finish_independently() {
        let tracker = Arc::new(ActivityTracker::new());
        assert!(!tracker.snapshot().reported());
        let reporter = tracker.reporter();
        assert!(tracker.snapshot().reported());
        let first = PackageId::from_parts(ActivationId::from_u128(10), 1);
        let second = PackageId::from_parts(ActivationId::from_u128(10), 2);
        let joining = reporter.begin([second, first], "prepare join");
        let spontaneous = reporter.clone().begin([], "root work");
        let snapshot = tracker.snapshot();
        assert_eq!(snapshot.invocations().len(), 2);
        assert_eq!(snapshot.invocations()[0].inputs(), [second, first]);
        assert!(snapshot.invocations()[1].inputs().is_empty());
        assert_ne!(
            snapshot.invocations()[0].id(),
            snapshot.invocations()[1].id()
        );
        joining.set_description("submit join");
        drop(spontaneous);
        let snapshot = tracker.snapshot();
        assert_eq!(snapshot.invocations().len(), 1);
        assert_eq!(snapshot.invocations()[0].description(), "submit join");
        drop(joining);
        assert!(tracker.snapshot().invocations().is_empty());
    }

    #[tokio::test]
    async fn cancelling_one_reported_task_keeps_concurrent_work() {
        let tracker = Arc::new(ActivityTracker::new());
        let reporter = tracker.reporter();
        let retained = reporter.begin([], "retained");
        let (ready, started) = tokio::sync::oneshot::channel();
        let task = tokio::spawn(async move {
            let _guard = reporter.begin([], "cancelled");
            ready.send(()).expect("test observes readiness");
            std::future::pending::<()>().await;
        });
        started.await.expect("task reports work");
        assert_eq!(tracker.snapshot().invocations().len(), 2);
        task.abort();
        assert!(task.await.expect_err("task aborted").is_cancelled());
        assert_eq!(tracker.snapshot().invocations().len(), 1);
        assert_eq!(
            tracker.snapshot().invocations()[0].description(),
            "retained"
        );
        drop(retained);
    }
}
