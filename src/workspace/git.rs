use std::path::{Path, PathBuf};
use std::process::{Output, Stdio};
use std::time::Duration;
use tokio::process::Command;

use tokio::io::AsyncReadExt;

use super::{Checkout, Result, WorkspaceError, WorkspaceStore, entry_map, tree_difference};

use crate::package::{ResolvedEntryKind as EntryKind, ResolvedPackage, descendants};

/// A path that needs human or application conflict resolution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GitConflict {
    /// Canonical relative path.
    pub path: String,
    /// Textual, binary, deletion or filesystem-type conflict.
    pub reason: String,
}

/// Three-way merge output. A conflicted checkout is never captured implicitly.
#[derive(Debug)]
pub struct GitMergeResult {
    /// Host-owned writable result directory, including conflict markers if any.
    pub checkout: Checkout,
    /// Immutable merged version only when the merge has no conflicts.
    pub package: Option<ResolvedPackage>,
    /// Unresolved paths. Resolve them in the checkout and capture explicitly.
    pub conflicts: Vec<GitConflict>,
}

struct Scratch(PathBuf);
impl Scratch {
    fn new() -> Result<Self> {
        Self::new_in(&std::env::temp_dir())
    }
    fn new_in(parent: &Path) -> Result<Self> {
        std::fs::create_dir_all(parent)?;
        let path = parent.join(format!("ontography-git-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&path)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700))?;
        }
        Ok(Self(path))
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn command(cwd: &Path) -> Command {
    let mut command = Command::new("git");
    // Merge/diff must never inherit repository redirection, injected config,
    // credential helpers, external diff drivers or hooks from the host.
    command
        .env_clear()
        .env("PATH", std::env::var_os("PATH").unwrap_or_default())
        .env("HOME", cwd)
        .env("XDG_CONFIG_HOME", cwd.join(".no-config"))
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_SYSTEM", "/dev/null")
        .env("GIT_TERMINAL_PROMPT", "0")
        .env("LC_ALL", "C")
        .env("GIT_CEILING_DIRECTORIES", cwd.parent().unwrap_or(cwd))
        .current_dir(cwd)
        .args([
            "-c",
            "core.hooksPath=/dev/null",
            "-c",
            "core.attributesFile=/dev/null",
            "-c",
            "core.pager=cat",
        ]);
    command
}

/// Run without unbounded output allocation or an unbounded child lifetime.
async fn run_git(command: &mut Command, stdout_limit: u64) -> Result<Output> {
    async fn read_limited(pipe: impl tokio::io::AsyncRead + Unpin, limit: u64) -> Result<Vec<u8>> {
        let mut bytes = Vec::new();
        pipe.take(limit.saturating_add(1))
            .read_to_end(&mut bytes)
            .await?;
        if bytes.len() as u64 > limit {
            return Err(WorkspaceError::Limit("Git output".into()));
        }
        Ok(bytes)
    }
    let mut child = command
        .kill_on_drop(true)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let stdout = child.stdout.take().expect("piped stdout");
    let stderr = child.stderr.take().expect("piped stderr");
    let result = tokio::time::timeout(Duration::from_mins(1), async {
        tokio::try_join!(
            read_limited(stdout, stdout_limit),
            read_limited(stderr, 64 * 1024),
            async { child.wait().await.map_err(WorkspaceError::from) }
        )
    })
    .await;
    match result {
        Ok(Ok((stdout, stderr, status))) => Ok(Output {
            status,
            stdout,
            stderr,
        }),
        failed => {
            let _ = child.kill().await;
            let _ = child.wait().await;
            match failed {
                Ok(Err(error)) => Err(error),
                _ => Err(WorkspaceError::Git("operation exceeded 60 seconds".into())),
            }
        }
    }
}

/// Rebuild a local staging index without changing any working files.
pub(super) async fn rebuild_index(path: &Path) -> Result<()> {
    let tree = run_git(
        command(path).args(["rev-parse", "--verify", "--quiet", "HEAD^{tree}"]),
        64 * 1024,
    )
    .await?;
    let output = if tree.status.success() {
        run_git(command(path).args(["read-tree", "HEAD"]), 64 * 1024).await?
    } else {
        let branch = run_git(
            command(path).args(["symbolic-ref", "--quiet", "HEAD"]),
            64 * 1024,
        )
        .await?;
        if !branch.status.success() {
            return Err(WorkspaceError::Git(
                "package repository has no valid HEAD".into(),
            ));
        }
        let branch = std::str::from_utf8(&branch.stdout)
            .map_err(|_| WorkspaceError::Git("invalid HEAD reference".into()))?
            .trim();
        if !branch.starts_with("refs/") {
            return Err(WorkspaceError::Git("invalid HEAD reference".into()));
        }
        let exists = run_git(
            command(path).args(["show-ref", "--verify", "--quiet", "--", branch]),
            64 * 1024,
        )
        .await?;
        if exists.status.code() != Some(1) {
            return Err(WorkspaceError::Git(
                "HEAD references a missing or invalid object".into(),
            ));
        }
        run_git(command(path).args(["read-tree", "--empty"]), 64 * 1024).await?
    };
    if !output.status.success() {
        return Err(WorkspaceError::Git(
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ));
    }
    Ok(())
}

impl WorkspaceStore {
    /// Git's textual diff between two private COW directory checkouts.
    ///
    /// Repository administration data is excluded. No source repository config,
    /// hooks, filters or external diff drivers are used. Git must be installed.
    ///
    /// # Errors
    /// Reports invalid packages, clone failure, unavailable Git or oversized diff output.
    pub async fn git_diff(&self, base: &ResolvedPackage, new: &ResolvedPackage) -> Result<String> {
        let scratch = Scratch::new_in(self.cache.root().parent().unwrap_or(Path::new(".")))?;
        let old = self.checkout(base, scratch.0.join("before")).await?;
        let new = self.checkout(new, scratch.0.join("after")).await?;
        for path in [old.path(), new.path()] {
            let git = path.join(".git");
            if git.exists() {
                tokio::fs::remove_dir_all(git).await?;
            }
        }
        let output = run_git(
            command(&scratch.0).args([
                "diff",
                "--no-index",
                "--no-ext-diff",
                "--no-textconv",
                "--no-color",
                "--find-renames",
                "--",
                "before",
                "after",
            ]),
            16 * 1024 * 1024,
        )
        .await?;
        if !matches!(output.status.code(), Some(0 | 1)) {
            return Err(WorkspaceError::Git(
                String::from_utf8_lossy(&output.stderr).into_owned(),
            ));
        }
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    }

    /// Three-way file merge in an isolated destination, using Git's merge engine.
    ///
    /// Git metadata follows `ours`; the result is a Changes package based on
    /// `ours`. Operation inputs belong in invocation records, not a second lineage. Renames are represented as additions/deletions and ambiguous
    /// renames therefore remain explicit conflicts. Binary/type/delete conflicts
    /// preserve our entry and report the path. Successful text merges use Git's
    /// `merge-file`; conflicted text contains ordinary conflict markers.
    ///
    /// # Errors
    /// Reports invalid packages or combined paths, content/clone failure or unavailable Git.
    /// Ordinary merge conflicts are returned in the result, rather than as errors.
    pub async fn git_merge(
        &self,
        base: &ResolvedPackage,
        ours: &ResolvedPackage,
        theirs: &ResolvedPackage,
        destination: impl AsRef<Path>,
    ) -> Result<GitMergeResult> {
        for package in [base, ours, theirs] {
            self.validate_view(package)?;
        }
        let before = entry_map(base);
        let right = entry_map(theirs);
        let mut merged = entry_map(ours);
        let mut conflicts = Vec::new();
        let mut conflicted_directories = BTreeSet::new();
        for change in tree_difference(&before, &right) {
            let path = change.path;
            if path
                .match_indices('/')
                .any(|(index, _)| conflicted_directories.contains(&path[..index]))
            {
                continue;
            }
            let b = change.before.as_ref();
            let l = merged.get(&path);
            let r = change.after.as_ref();
            if path == ".git" || path.starts_with(".git/") || l == r {
                continue;
            }
            if b == Some(&EntryKind::Directory)
                && l == b
                && r != b
                && descendants(&before, &path).ne(descendants(&merged, &path))
            {
                conflicts.push(GitConflict {
                    path: path.clone(),
                    reason: "directory removal or type change conflicts with our descendant edits"
                        .into(),
                });
                conflicted_directories.insert(path);
                continue;
            }
            let chosen = if l == b {
                r.cloned()
            } else if let (
                Some(EntryKind::File { content: bc, .. }),
                Some(EntryKind::File {
                    content: lc,
                    executable: le,
                }),
                Some(EntryKind::File {
                    content: rc,
                    executable: re,
                }),
            ) = (b, l, r)
            {
                let bytes = [
                    self.content.read_range(*lc, 0..lc.size()).await?.to_vec(),
                    self.content.read_range(*bc, 0..bc.size()).await?.to_vec(),
                    self.content.read_range(*rc, 0..rc.size()).await?.to_vec(),
                ];
                if bytes.iter().any(|v| v.contains(&0)) {
                    conflicts.push(GitConflict {
                        path: path.clone(),
                        reason: "binary content changed on both sides".into(),
                    });
                    l.cloned()
                } else {
                    let (bytes, conflict) = merge_file(bytes, self.limits.max_file_bytes).await?;
                    if conflict {
                        conflicts.push(GitConflict {
                            path: path.clone(),
                            reason: "overlapping text changes".into(),
                        });
                    }
                    let executable = match b {
                        Some(EntryKind::File { executable: be, .. }) if le == be => *re,
                        _ => *le,
                    };
                    Some(EntryKind::File {
                        content: self.content.import_bytes(bytes).await?,
                        executable,
                    })
                }
            } else {
                conflicts.push(GitConflict {
                    path: path.clone(),
                    reason: "incompatible additions, deletion, symlink or type changes".into(),
                });
                l.cloned()
            };
            if let Some(kind) = chosen {
                merged.insert(path, kind);
            } else {
                merged.remove(&path);
            }
        }
        // A directory changed into a file on one side cannot contain additions
        // from the other side. Keep the chosen parent and report hidden children.
        let invalid = merged
            .keys()
            .filter(|path| {
                path.rsplit_once('/')
                    .is_some_and(|(parent, _)| merged.get(parent) != Some(&EntryKind::Directory))
            })
            .cloned()
            .collect::<Vec<_>>();
        for path in invalid {
            conflicts.push(GitConflict {
                path: path.clone(),
                reason: "parent is missing or changed type".into(),
            });
            crate::package::remove_tree(&mut merged, &path);
        }
        let tree = self.store_changes(ours, merged).await?;
        let checkout = self.checkout(&tree, destination).await?;
        let package = conflicts.is_empty().then_some(tree);
        Ok(GitMergeResult {
            checkout,
            package,
            conflicts,
        })
    }
}

async fn merge_file(bytes: [Vec<u8>; 3], max_bytes: u64) -> Result<(Vec<u8>, bool)> {
    let scratch = Scratch::new()?;
    for (name, bytes) in ["ours", "base", "theirs"].into_iter().zip(bytes) {
        tokio::fs::write(scratch.0.join(name), bytes).await?;
    }
    let output = run_git(
        command(&scratch.0).args([
            "merge-file",
            "-p",
            "-L",
            "ours",
            "-L",
            "base",
            "-L",
            "theirs",
            "--",
            "ours",
            "base",
            "theirs",
        ]),
        max_bytes,
    )
    .await?;
    match output.status.code() {
        Some(0) => Ok((output.stdout, false)),
        Some(1..=127) => Ok((output.stdout, true)),
        _ => Err(WorkspaceError::Git(
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )),
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;

    #[tokio::test]
    async fn excessive_stdout_and_stderr_are_stopped_before_process_exit() {
        for redirect in ["", " >&2"] {
            let mut command = Command::new("sh");
            command.args([
                "-c",
                &format!("while :; do printf 'unbounded output\n'{redirect}; done"),
            ]);
            let result = tokio::time::timeout(Duration::from_secs(5), run_git(&mut command, 1024))
                .await
                .unwrap();
            assert!(matches!(result, Err(WorkspaceError::Limit(_))));
        }
    }
}
use std::collections::BTreeSet;
