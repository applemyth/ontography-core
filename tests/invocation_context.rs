//! Characterizes the worker-facing invocation context: what a worker sees and
//! may do once a composed content package is delivered to its node.
//!
//! Handles are discovered only from `tool_descriptors()` and tool responses,
//! and package identities are the ones these tests build, so the assertions
//! describe behavior rather than how grants and handles are represented.

use ontography::{
    ActivationProposal, ContentDigest, ContentId, ContentStore, ContextError, ContextMode,
    ContextPolicy, Emission, InvocationHandle, InvocationTrigger, OutputAuthority, PackageDocument,
    PackageEnvelope, PackageId, PackageStore, Payload, ProposalDecision, ProposalRuntime,
    SessionHandle,
};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::sync::Arc;

#[allow(dead_code)]
mod support;

const SPEC: &str = "openapi";
const GUIDE: &str = "a guide to the tree";
const RUN: &str = "#!/bin/sh\necho run\n";

/// Every visible path of `Fixture::tree`, in path order.
const TREE_PATHS: [&str; 7] = [
    "",
    "docs",
    "docs/api",
    "docs/api/spec.txt",
    "docs/guide.md",
    "latest",
    "run.sh",
];

/// A session whose producer delivers content packages to its consumer.
struct Fixture {
    session: SessionHandle,
    content: ContentStore,
    packages: PackageStore,
}

impl Fixture {
    async fn new() -> Self {
        let kernel = support::kernel(
            &["producer", "consumer"],
            &[("flow", "producer", "consumer", "result")],
        );
        let session = ProposalRuntime::new(Arc::new(kernel)).open().unwrap();
        let content = session.content_store().await.unwrap();
        let packages = PackageStore::new(content.clone());
        Self {
            session,
            content,
            packages,
        }
    }

    async fn put(&self, document: PackageDocument) -> ContentId {
        self.packages.put(&document).await.unwrap()
    }

    async fn file(&self, text: &str, executable: bool) -> ContentId {
        let content = self
            .content
            .import_bytes(text.as_bytes().to_vec())
            .await
            .unwrap();
        self.put(PackageDocument::File {
            content,
            executable,
        })
        .await
    }

    async fn folder<const N: usize>(&self, entries: [(&str, ContentId); N]) -> ContentId {
        let entries = entries
            .into_iter()
            .map(|(name, id)| (name.to_owned(), id))
            .collect();
        self.put(PackageDocument::Collection { entries }).await
    }

    async fn changes<const N: usize>(
        &self,
        base: ContentId,
        changes: [(&str, ContentId); N],
    ) -> ContentId {
        let changes = changes
            .into_iter()
            .map(|(path, id)| (path.to_owned(), Some(id)))
            .collect();
        self.put(PackageDocument::Changes { base, changes }).await
    }

    /// `docs/{api/spec.txt, guide.md}`, `latest -> docs/guide.md`, and an
    /// executable `run.sh`.
    async fn tree(&self) -> ContentId {
        let api = self
            .folder([("spec.txt", self.file(SPEC, false).await)])
            .await;
        let guide = self.file(GUIDE, false).await;
        let docs = self.folder([("api", api), ("guide.md", guide)]).await;
        let latest = self
            .put(PackageDocument::Symlink {
                target: "docs/guide.md".into(),
            })
            .await;
        let run = self.file(RUN, true).await;
        self.folder([("docs", docs), ("latest", latest), ("run.sh", run)])
            .await
    }

    /// Delivers `root` to the consumer, declaring its whole closure.
    async fn deliver(&self, root: ContentId) -> PackageId {
        let mut proposal =
            ActivationProposal::root("producer", support::authority(), support::payload());
        proposal.emit(Emission::new(
            "flow",
            OutputAuthority::Carry,
            envelope(root),
        ));
        let closure = self.packages.dependencies(root).await.unwrap();
        match self
            .session
            .submit_with_content(proposal, closure)
            .await
            .unwrap()
        {
            ProposalDecision::Committed(activation) => PackageId::from_parts(activation, 0),
            ProposalDecision::Rejected(reject) => panic!("delivery was rejected: {reject}"),
        }
    }

    async fn begin(
        &self,
        package: PackageId,
        policy: ContextPolicy,
    ) -> Result<InvocationHandle, ContextError> {
        self.session
            .begin_invocation(
                "consumer",
                InvocationTrigger::Packages(vec![package]),
                policy,
            )
            .await
    }

    /// Delivers `root` and begins an invocation on it at the consumer.
    async fn invoke(&self, root: ContentId, policy: ContextPolicy) -> InvocationHandle {
        let package = self.deliver(root).await;
        self.begin(package, policy).await.unwrap()
    }
}

fn policy(mode: ContextMode) -> ContextPolicy {
    ContextPolicy {
        mode,
        ..ContextPolicy::default()
    }
}

fn envelope(id: ContentId) -> Payload {
    PackageEnvelope::new(id).to_payload().unwrap()
}

/// The facts of `Fixture::tree` a worker sees, in path order.
fn tree_view() -> Vec<Value> {
    vec![
        json!({"path": "", "kind": "collection"}),
        json!({"path": "docs", "kind": "collection"}),
        json!({"path": "docs/api", "kind": "collection"}),
        json!({"path": "docs/api/spec.txt", "kind": "file", "size": SPEC.len(), "executable": false}),
        json!({"path": "docs/guide.md", "kind": "file", "size": GUIDE.len(), "executable": false}),
        json!({"path": "latest", "kind": "symlink", "target": "docs/guide.md"}),
        json!({"path": "run.sh", "kind": "file", "size": RUN.len(), "executable": true}),
    ]
}

/// A member descriptor's visible facts, without its handles.
fn facts(member: &Value) -> Value {
    let mut facts = json!({});
    for field in ["path", "kind", "size", "executable", "target"] {
        if let Some(value) = member.get(field) {
            facts[field] = value.clone();
        }
    }
    facts
}

/// The facts of member descriptors, in path order.
fn view(members: &Value) -> Vec<Value> {
    let mut view: Vec<Value> = members.as_array().unwrap().iter().map(facts).collect();
    view.sort_by_cached_key(|member| member["path"].as_str().map(str::to_owned));
    view
}

/// The paths of member descriptors, sorted, keeping duplicates.
fn paths(members: &Value) -> Vec<&str> {
    let mut paths: Vec<&str> = members
        .as_array()
        .unwrap()
        .iter()
        .map(|member| member["path"].as_str().unwrap())
        .collect();
    paths.sort_unstable();
    paths
}

/// The handle advertised for `path` among member descriptors.
fn handle(members: &Value, path: &str) -> String {
    members
        .as_array()
        .unwrap()
        .iter()
        .find(|member| member["path"] == path)
        .and_then(|member| member["handle"].as_str())
        .unwrap_or_else(|| panic!("no member at {path:?}"))
        .to_owned()
}

/// Calls a context tool on one handle and returns the response body.
async fn tool(
    invocation: &InvocationHandle,
    operation: &str,
    handle: &str,
) -> Result<Value, ContextError> {
    let response = invocation
        .call(operation, json!({ "handle": handle }))
        .await?;
    Ok(response.value)
}

/// Every member descriptor, discovered as a worker would: each view's root
/// from the tool descriptors, then `package.list` down every folder.
async fn members(invocation: &InvocationHandle) -> Value {
    let mut found = invocation.tool_descriptors()["views"]
        .as_array()
        .unwrap()
        .clone();
    let mut folders: Vec<String> = found
        .iter()
        .filter(|member| member["kind"] == "collection")
        .map(|member| member["handle"].as_str().unwrap().to_owned())
        .collect();
    while let Some(folder) = folders.pop() {
        let listing = tool(invocation, "package.list", &folder).await.unwrap();
        for member in listing["members"].as_array().unwrap() {
            if member["kind"] == "collection" {
                folders.push(member["handle"].as_str().unwrap().to_owned());
            }
            found.push(member.clone());
        }
    }
    Value::Array(found)
}

/// Dependencies in one canonical order; their order is not part of the contract.
fn sorted(mut ids: Vec<ContentId>) -> Vec<ContentId> {
    ids.sort_by_key(|id| id.hash());
    ids
}

#[tokio::test]
async fn descriptors_list_each_view_by_its_root_and_size() {
    let fixture = Fixture::new().await;
    let invocation = fixture
        .invoke(fixture.tree().await, ContextPolicy::default())
        .await;
    let descriptors = invocation.tool_descriptors();
    let views = descriptors["views"].as_array().unwrap();
    assert_eq!(views.len(), 1);
    assert_eq!(facts(&views[0]), tree_view()[0]);
    assert_eq!(views[0]["entries"], TREE_PATHS.len());
}

#[tokio::test]
async fn listing_discovers_every_entry_with_its_own_handle() {
    let fixture = Fixture::new().await;
    let invocation = fixture
        .invoke(fixture.tree().await, policy(ContextMode::Explorable))
        .await;
    let members = members(&invocation).await;
    assert_eq!(view(&members), tree_view());

    // One delivered view has one owner, and each member its own handle.
    let members = members.as_array().unwrap();
    let owners: BTreeSet<&str> = members
        .iter()
        .map(|m| m["owner"].as_str().unwrap())
        .collect();
    let handles: BTreeSet<&str> = members
        .iter()
        .map(|m| m["handle"].as_str().unwrap())
        .collect();
    assert_eq!(owners.len(), 1);
    assert_eq!(handles.len(), TREE_PATHS.len());
}

#[tokio::test]
async fn describe_reports_the_root_and_nested_entries() {
    let fixture = Fixture::new().await;
    let invocation = fixture
        .invoke(fixture.tree().await, policy(ContextMode::Explorable))
        .await;
    let members = members(&invocation).await;
    let mut described = Vec::new();
    for path in TREE_PATHS {
        let handle = handle(&members, path);
        described.push(
            tool(&invocation, "package.describe", &handle)
                .await
                .unwrap(),
        );
    }
    assert_eq!(view(&Value::Array(described)), tree_view());
}

#[tokio::test]
async fn list_returns_exactly_the_immediate_children_of_a_folder() {
    let fixture = Fixture::new().await;
    let invocation = fixture
        .invoke(fixture.tree().await, policy(ContextMode::Explorable))
        .await;
    let every = members(&invocation).await;

    // Walk down the tree, taking each folder's handle from the listing above it.
    let mut members = invocation.tool_descriptors()["views"].clone();
    for (folder, children) in [
        ("", vec!["docs", "latest", "run.sh"]),
        ("docs", vec!["docs/api", "docs/guide.md"]),
        ("docs/api", vec!["docs/api/spec.txt"]),
    ] {
        let listing = tool(&invocation, "package.list", &handle(&members, folder))
            .await
            .unwrap();
        members = listing["members"].clone();
        assert_eq!(paths(&members), children);
    }

    // Only a folder has members.
    for leaf in ["run.sh", "latest"] {
        let leaf = handle(&every, leaf);
        assert!(matches!(
            tool(&invocation, "package.list", &leaf).await,
            Err(ContextError::Denied(_))
        ));
    }
}

#[tokio::test]
async fn read_returns_file_bytes_and_denies_folders() {
    let fixture = Fixture::new().await;
    let invocation = fixture
        .invoke(fixture.tree().await, policy(ContextMode::Explorable))
        .await;
    let members = &members(&invocation).await;
    let guide = handle(members, "docs/guide.md");

    let whole = tool(&invocation, "package.read", &guide).await.unwrap();
    assert_eq!(whole["text"], GUIDE);
    let range = invocation
        .call(
            "package.read",
            json!({"handle": guide, "start": 2, "end": 7}),
        )
        .await
        .unwrap();
    assert_eq!(range.value["text"], &GUIDE[2..7]);

    for folder in ["", "docs"] {
        assert!(matches!(
            tool(&invocation, "package.read", &handle(members, folder)).await,
            Err(ContextError::Denied(_))
        ));
    }
}

#[tokio::test]
async fn unknown_handles_are_not_found() {
    let fixture = Fixture::new().await;
    let package = fixture.deliver(fixture.tree().await).await;
    let invocation = fixture
        .begin(package, policy(ContextMode::Explorable))
        .await
        .unwrap();
    // Handles are invocation-local: another invocation's handle is unknown here.
    let other = fixture
        .begin(package, policy(ContextMode::Explorable))
        .await
        .unwrap();
    let foreign = handle(&members(&other).await, "run.sh");
    // Malformed paths under a real root name nothing either.
    let root = handle(&invocation.tool_descriptors()["views"], "");
    let crafted = ["/", "//run.sh", "/../run.sh", "/docs/../run.sh", "/docs/"]
        .map(|suffix| format!("{root}{suffix}"));

    for unknown in ["no-such-handle", foreign.as_str()]
        .into_iter()
        .chain(crafted.iter().map(String::as_str))
    {
        for operation in ["package.describe", "package.list", "package.read"] {
            assert!(matches!(
                tool(&invocation, operation, unknown).await,
                Err(ContextError::NotFound)
            ));
        }
    }
}

#[tokio::test]
async fn prepared_mode_denies_the_tools() {
    let fixture = Fixture::new().await;
    let invocation = fixture
        .invoke(fixture.tree().await, policy(ContextMode::Prepared))
        .await;
    let root = handle(&invocation.tool_descriptors()["views"], "");
    for operation in ["package.describe", "package.list", "package.read"] {
        assert!(matches!(
            tool(&invocation, operation, &root).await,
            Err(ContextError::Denied(_))
        ));
    }
}

#[tokio::test]
async fn prepared_context_lists_a_delivered_folder_view() {
    let fixture = Fixture::new().await;
    let package = fixture.deliver(fixture.tree().await).await;
    let invocation = fixture
        .begin(package, ContextPolicy::default())
        .await
        .unwrap();
    let prepared = invocation.prepare_context().await.unwrap();
    assert_eq!(prepared.len(), 1);
    assert_eq!(prepared[0].package_id, Some(package));
    let listing: Value = serde_json::from_slice(&prepared[0].content).unwrap();
    assert_eq!(paths(&listing["view"]), TREE_PATHS);
}

#[tokio::test]
async fn prepared_context_supplies_a_delivered_file_as_its_bytes() {
    let fixture = Fixture::new().await;
    let file = fixture.file(GUIDE, false).await;
    let invocation = fixture.invoke(file, ContextPolicy::default()).await;
    let prepared = invocation.prepare_context().await.unwrap();
    assert_eq!(prepared.len(), 1);
    assert_eq!(&*prepared[0].content, GUIDE.as_bytes());
    assert_eq!(
        prepared[0].content_digest,
        ContentDigest::compute(GUIDE.as_bytes())
    );
}

#[tokio::test]
async fn member_budget_counts_every_visible_entry_including_the_root() {
    let fixture = Fixture::new().await;
    let package = fixture.deliver(fixture.tree().await).await;
    let budget = |max_members| ContextPolicy {
        max_members,
        ..ContextPolicy::default()
    };
    assert!(matches!(
        fixture.begin(package, budget(TREE_PATHS.len() - 1)).await,
        Err(ContextError::Budget(_))
    ));
    fixture
        .begin(package, budget(TREE_PATHS.len()))
        .await
        .unwrap();
}

#[tokio::test]
async fn worker_output_may_republish_only_packages_in_the_granted_view() {
    let fixture = Fixture::new().await;
    let keep = fixture.file("keep", false).await;
    let replaced = fixture.file("old notes", false).await;
    let base = fixture
        .folder([("keep.txt", keep), ("notes.txt", replaced)])
        .await;
    let notes = fixture.file("new notes", false).await;
    let root = fixture.changes(base, [("notes.txt", notes)]).await;
    let stray = fixture.file("never delivered", false).await;
    let invocation = fixture.invoke(root, ContextPolicy::default()).await;

    // A granted package republishes with its own retention closure.
    for granted in [root, keep] {
        let dependencies = invocation
            .validate_worker_output(&envelope(granted))
            .await
            .unwrap();
        let closure = fixture.packages.dependencies(granted).await.unwrap();
        assert_eq!(sorted(dependencies), sorted(closure));
    }
    // The base retains the replaced file, but retention does not grant it.
    for outside in [replaced, stray] {
        assert!(matches!(
            invocation.validate_worker_output(&envelope(outside)).await,
            Err(ContextError::Denied(_))
        ));
    }
    // Ordinary bytes name no package, so they need no dependencies.
    let plain = invocation
        .validate_worker_output(&support::payload())
        .await
        .unwrap();
    assert!(plain.is_empty());
}

#[tokio::test]
async fn republishing_a_save_labelled_folder_must_not_expose_hidden_files() {
    let fixture = Fixture::new().await;
    // B0 = { c: { f }, d: { secret } }
    let old_f = fixture.file("old f", false).await;
    let secret = fixture.file("secret", false).await;
    let c = fixture.folder([("f", old_f)]).await;
    let d = fixture.folder([("secret", secret)]).await;
    let b0 = fixture.folder([("c", c), ("d", d)]).await;
    // B saves a new c/f over B0; R replaces d with { public }.
    let new_f = fixture.file("new f", false).await;
    let b = fixture.changes(b0, [("c/f", new_f)]).await;
    let public = fixture.file("public", false).await;
    let public = fixture.folder([("public", public)]).await;
    let r = fixture.changes(b, [("d", public)]).await;
    let invocation = fixture.invoke(r, ContextPolicy::default()).await;

    // R hides d/secret. Its folder "c" is labelled with the save B, whose own
    // view still shows d/secret, so republishing B would expose it.
    let prepared = invocation.prepare_context().await.unwrap();
    let listing: Value = serde_json::from_slice(&prepared[0].content).unwrap();
    assert_eq!(paths(&listing["view"]), ["", "c", "c/f", "d", "d/public"]);
    let b_view = fixture.packages.resolve(b).await.unwrap();
    assert!(b_view.entries().iter().any(|e| e.path == "d/secret"));

    let outcome = invocation.validate_worker_output(&envelope(b)).await;
    assert!(
        matches!(outcome, Err(ContextError::Denied(_))),
        "republishing B was accepted: {outcome:?}"
    );
}

#[tokio::test]
async fn submission_requires_the_full_closure_of_an_emitted_package() {
    let fixture = Fixture::new().await;
    let root = fixture.tree().await;
    let package = fixture.deliver(root).await;
    // The worker's output changes the delivered tree.
    let added = fixture.file("added", false).await;
    let output = fixture.changes(root, [("added.txt", added)]).await;
    let emission = Emission::outbound("t", OutputAuthority::Carry, envelope(output));
    // A denied submission fails its invocation, so each attempt begins a new one.
    let submit = async |contents: Vec<ContentId>| {
        let invocation = fixture
            .begin(package, ContextPolicy::default())
            .await
            .unwrap();
        invocation
            .submit(support::payload(), vec![emission.clone()], contents)
            .await
    };

    // Declaring nothing, or the output and its new file without the base
    // it changes, leaves the closure undeclared.
    let own = fixture.packages.dependencies(added).await.unwrap();
    for contents in [Vec::new(), [vec![output], own].concat()] {
        assert!(matches!(
            submit(contents).await,
            Err(ContextError::Denied(_))
        ));
    }
    let closure = fixture.packages.dependencies(output).await.unwrap();
    assert!(matches!(
        submit(closure).await,
        Ok(ProposalDecision::Committed(_))
    ));
}
