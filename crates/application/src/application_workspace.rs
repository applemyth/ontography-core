//! Shared baselines and private per-invocation filesystem views.

use std::path::Path;

use ontography_calculus::{Emission, OutputAuthority};
use ontography_content::package::{PackageEnvelope, ResolvedPackage};
use ontography_content::{ContentId, ContentStore};
use ontography_runtime::InvocationHandle;
use ontography_workspace::{Checkout, WorkspaceError, WorkspaceStore};

use super::ApplicationContext;

/// A private checkout and its explicit publication policy.
///
/// The adapter must stop writers before capture. Read-only permissions are
/// advisory: a hostile same-user process requires an operating-system sandbox.
pub struct PreparedWorkspace {
    store: WorkspaceStore,
    content: ContentStore,
    checkout: Checkout,
    base: ContentId,
    invocation: InvocationHandle,
}

impl PreparedWorkspace {
    /// Directory used consistently by terminal, read and edit tools.
    #[must_use]
    pub fn path(&self) -> &Path {
        self.checkout.path()
    }

    /// Whether the invocation may publish filesystem changes.
    #[must_use]
    pub fn writable(&self) -> bool {
        self.invocation
            .policy()
            .workspace
            .as_ref()
            .is_some_and(|policy| policy.writable)
    }

    /// Validate the final directory and return its optional output with retention closure.
    ///
    /// A capture that is then rejected, by policy or by a failed receipt, is
    /// released: its fresh imports become collectable, while content that
    /// committed ledger history retains, such as the base's members, keeps
    /// its ledger tag.
    ///
    /// # Errors
    /// Reports capture, policy, and receipt failures. Call only after writers stop.
    pub async fn finish(&self) -> Result<(Option<Emission>, Vec<ContentId>), WorkspaceError> {
        let package = self.store.capture(self.path(), self.base).await?;
        match self.publish(&package).await {
            Ok(finished) => Ok(finished),
            Err(error) if package.root() == self.base => Err(error),
            Err(error) => {
                for id in package.dependencies() {
                    if let Err(cleanup) = self.content.release(id).await {
                        return Err(WorkspaceError::Invalid(format!(
                            "{error}; releasing the capture also failed: {cleanup}"
                        )));
                    }
                }
                Err(error)
            }
        }
    }

    async fn publish(
        &self,
        package: &ResolvedPackage,
    ) -> Result<(Option<Emission>, Vec<ContentId>), WorkspaceError> {
        if !self.writable() && package.root() != self.base {
            return Err(WorkspaceError::Invalid(
                "read-only workspace was modified".into(),
            ));
        }
        let payload = PackageEnvelope::new(package.root())
            .to_payload()
            .map_err(invalid)?;
        let emission = self
            .invocation
            .policy()
            .workspace
            .as_ref()
            .and_then(|policy| policy.output_edge.as_ref())
            .map(|edge| Emission::new(edge.as_str(), OutputAuthority::Carry, payload.clone()));
        let contents = if emission.is_some() {
            package.dependencies()
        } else {
            Vec::new()
        };
        // Capture is a host observation. It does not establish delivery to a
        // worker or acknowledgement by one, so this receipt remains prepared.
        self.invocation
            .record_tool_response("workspace_capture", payload)
            .await
            .map_err(invalid)?;
        Ok((emission, contents))
    }

    /// Remove the private directory once all worker processes have stopped.
    ///
    /// # Errors
    /// Reports filesystem cleanup failures.
    pub async fn remove(self) -> Result<(), WorkspaceError> {
        self.checkout.remove().await
    }
}

impl ApplicationContext {
    /// Return the run-owned immutable file cache shared by every invocation.
    #[must_use]
    pub const fn workspace_store(&self) -> &WorkspaceStore {
        &self.workspace
    }

    /// Resolve a delivered collection and expose a private copy-on-write directory.
    ///
    /// Every dependency must be retained by the producer. Shared cache ownership
    /// preserves one immutable baseline across invocations of this run.
    ///
    /// # Errors
    /// Rejects ambiguous inputs, missing dependencies, or invalid publication policy.
    pub async fn prepare_workspace(
        &self,
        invocation: &InvocationHandle,
    ) -> Result<Option<PreparedWorkspace>, WorkspaceError> {
        if !self.execution.owns_invocation(invocation) {
            return Err(WorkspaceError::Invalid(
                "invocation belongs to another execution".into(),
            ));
        }
        let Some(policy) = &invocation.policy().workspace else {
            return Ok(None);
        };
        if let Some(edge) = &policy.output_edge
            && !self
                .outgoing_edges()
                .await
                .map_err(invalid)?
                .iter()
                .any(|item| item.id() == edge)
        {
            return Err(WorkspaceError::Invalid(
                "workspace output_edge is not outgoing from this node".into(),
            ));
        }
        let (_, base) = invocation.workspace_package().await.map_err(invalid)?;
        let content = self.execution.content_store().await.map_err(invalid)?;
        let store = self.workspace_store().clone();
        let parent = store.checkouts_dir().to_owned();
        tokio::fs::create_dir_all(&parent).await?;
        let checkout = store
            .checkout(&base, parent.join(invocation.id().to_string()))
            .await?;
        let prepared = async {
            if !policy.writable {
                checkout.set_read_only().await?;
            }
            invocation
                .record_workspace_exposure(base.root())
                .await
                .map_err(invalid)?;
            Ok::<(), WorkspaceError>(())
        }
        .await;
        if let Err(error) = prepared {
            return Err(match checkout.remove().await {
                Ok(()) => error,
                Err(cleanup) => WorkspaceError::Invalid(format!(
                    "{error}; checkout cleanup also failed: {cleanup}"
                )),
            });
        }
        Ok(Some(PreparedWorkspace {
            store,
            content,
            checkout,
            base: base.root(),
            invocation: invocation.clone(),
        }))
    }
}

fn invalid(error: impl std::fmt::Display) -> WorkspaceError {
    WorkspaceError::Invalid(error.to_string())
}
