//! Persistent-session probes: rewrite retirements, explicit retirement, and
//! vocabulary extension survive a reopen with exact records.

use std::collections::BTreeMap;
use std::sync::Arc;

use ontography::{
    ActivationId, ActivationProposal, Authority, AuthorityTag, Contract, DefinitionId, Edge,
    EdgeDefinition, Emission, ExtensionError, Graph, IngressMode, Kernel, Node, NodeDefinition,
    OutputAuthority, PackageId, Phase, ProposalDecision, ProposalRuntime, Reject, RetireError,
    RetirementReason, RewriteError, RewriteFragment, RewriteGrammar, RewriteMatch,
    RewriteProduction, RewriteRequest, RootRule, Schema, SessionHandle, SessionTransitionError,
};

fn bytes(value: &'static [u8]) -> Arc<[u8]> {
    Arc::from(value)
}

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}

/// Shared contracts so every kernel version keeps the same validator identities.
struct Contracts {
    result: Contract,
    item: Contract,
}

impl Contracts {
    fn new() -> Self {
        Self {
            result: Contract::new("result", "Result", |_| Ok(())).unwrap(),
            item: Contract::new("item", "Item", |_| Ok(())).unwrap(),
        }
    }
}

/// `edges`: (identity, authority tag). Every edge runs a→b with the item contract.
fn admit(contracts: &Contracts, tags: &[&str], edges: &[(&str, &str)]) -> Kernel {
    Kernel::admit(
        DefinitionId::new("persistent-frontier").unwrap(),
        Schema::new(["Node"], ["Result", "Item"], tags.iter().map(|id| tag(id))).unwrap(),
        Graph::new(
            ["a", "b"].map(|node| Node::new(node).unwrap()),
            edges
                .iter()
                .map(|(edge, _)| Edge::new(*edge, "a", "b").unwrap()),
        )
        .unwrap(),
        [contracts.result.clone(), contracts.item.clone()],
        [
            NodeDefinition::new("a", ["Node"], "result").unwrap(),
            NodeDefinition::new("b", ["Node"], "result")
                .unwrap()
                .with_ingress_mode(IngressMode::All),
        ],
        edges.iter().map(|(edge, edge_tag)| {
            EdgeDefinition::new(*edge, ["Flow"], ["Node"], ["Node"], "item", [tag(edge_tag)])
                .unwrap()
        }),
        [],
        [RootRule::new("a", Authority::new([tag("route")])).unwrap()],
    )
    .unwrap()
}

fn production(
    id: &str,
    left: &Kernel,
    right: &Kernel,
    interface_edges: &[&str],
) -> RewriteProduction {
    RewriteProduction::new(
        id,
        RewriteFragment::from_kernel(left),
        [Arc::from("a"), Arc::from("b")].into(),
        interface_edges
            .iter()
            .map(|edge| Arc::from(*edge))
            .collect(),
        RewriteFragment::from_kernel(right),
    )
    .unwrap()
}

fn request(id: &str, edges: &[&str], fresh_edges: &[&str]) -> RewriteRequest {
    let same = |values: &[&str]| -> BTreeMap<Arc<str>, Arc<str>> {
        values
            .iter()
            .map(|value| (Arc::from(*value), Arc::from(*value)))
            .collect()
    };
    RewriteRequest::new(
        id,
        RewriteMatch::new(
            same(&["a", "b"]),
            same(edges),
            BTreeMap::new(),
            same(fresh_edges),
        ),
    )
}

async fn root(session: &SessionHandle, emission: Option<Emission>) -> ActivationId {
    let mut proposal =
        ActivationProposal::root("a", Authority::new([tag("route")]), bytes(b"result"));
    if let Some(emission) = emission {
        proposal.emit(emission);
    }
    match session.submit(proposal).await.unwrap() {
        ProposalDecision::Committed(id) => id,
        ProposalDecision::Rejected(reject) => panic!("root rejected: {reject}"),
    }
}

fn outbound() -> Emission {
    Emission::outbound("Item", OutputAuthority::Carry, bytes(b"item"))
}

fn delivered(edge: &str) -> Emission {
    Emission::new(edge, OutputAuthority::Carry, bytes(b"item"))
}

async fn emit(session: &SessionHandle, emission: Emission) -> PackageId {
    PackageId::from_parts(root(session, Some(emission)).await, 0)
}

#[tokio::test]
async fn retirements_and_extension_survive_reopen() {
    let temp = tempfile::tempdir().unwrap();
    let run = temp.path().join("run");
    let contracts = Contracts::new();
    let with_e1 = Arc::new(admit(&contracts, &["route"], &[("e1", "route")]));
    let with_e2 = admit(&contracts, &["route"], &[("e2", "route")]);
    let extended = Arc::new(admit(&contracts, &["route", "extra"], &[("e2", "route")]));
    let extended_with_e3 = admit(
        &contracts,
        &["route", "extra"],
        &[("e2", "route"), ("e3", "extra")],
    );
    let grammar = RewriteGrammar::new([
        production("replace", &with_e1, &with_e2, &[]),
        production("tagged", &with_e2, &extended_with_e3, &["e2"]),
    ])
    .unwrap();
    let replace = request("replace", &["e1"], &["e2"]);
    let tagged = request("tagged", &["e2"], &["e3"]);

    let runtime = ProposalRuntime::with_grammar(Arc::clone(&with_e1), grammar.clone());
    let session = runtime.create_persistent(&run).unwrap();

    // A receipt on e1 at the All receiver, then e1 is replaced: RouteRemoved.
    let stranded = emit(&session, outbound()).await;
    session.transfer(stranded, "e1").await.unwrap();
    let plan = session.prepare_rewrite(&replace).await.unwrap();
    assert_eq!(
        plan.retirements().get(&stranded),
        Some(&RetirementReason::RouteRemoved)
    );
    let outcome = session.commit_rewrite(plan).await.unwrap();
    assert_eq!(outcome.revision(), 3);
    assert!(session.pending_at("b").await.unwrap().packages().is_empty());

    // An outbound package retired explicitly with evidence.
    let unrouted = emit(&session, outbound()).await;
    let evidence = root(&session, None).await;
    let retirement = session.retire(unrouted, Some(evidence)).await.unwrap();
    assert_eq!(retirement.reason(), RetirementReason::Explicit);
    assert_eq!(retirement.holder(), "a");
    assert_eq!(retirement.phase(), Phase::Out);
    assert_eq!(retirement.revision(), 6);
    assert_eq!(retirement.evidence(), Some(evidence));
    assert!(session.outbound().await.unwrap().packages().is_empty());
    assert!(matches!(
        session.retire(unrouted, None).await,
        Err(SessionTransitionError::Retire(RetireError::NotLive(id))) if id == unrouted
    ));
    assert!(matches!(
        session
            .retire(stranded, Some(ActivationId::from_u128(5)))
            .await,
        Err(SessionTransitionError::Retire(RetireError::NotLive(_)))
    ));

    // A received package retired explicitly must leave the readiness index.
    let received = emit(&session, delivered("e2")).await;
    assert_eq!(
        session.next_trigger_at("b").await.unwrap().packages().len(),
        1
    );
    let retirement = session.retire(received, None).await.unwrap();
    assert_eq!(retirement.phase(), Phase::In);
    assert_eq!(retirement.holder(), "b");
    assert_eq!(retirement.revision(), 8);
    assert!(
        session
            .next_trigger_at("b")
            .await
            .unwrap()
            .packages()
            .is_empty()
    );
    assert!(session.pending_at("b").await.unwrap().packages().is_empty());

    // Unknown evidence on a live package is a typed rejection; the session stays open.
    let live = emit(&session, outbound()).await;
    assert!(matches!(
        session.retire(live, Some(ActivationId::from_u128(5))).await,
        Err(SessionTransitionError::Retire(
            RetireError::UnknownEvidence(_)
        ))
    ));
    assert_eq!(session.retire(live, None).await.unwrap().revision(), 10);

    // A consumed package is not live.
    let consumed = emit(&session, delivered("e2")).await;
    assert!(matches!(
        session
            .submit(ActivationProposal::package(consumed, bytes(b"result")))
            .await
            .unwrap(),
        ProposalDecision::Committed(_)
    ));
    assert!(matches!(
        session.retire(consumed, None).await,
        Err(SessionTransitionError::Retire(RetireError::NotLive(id))) if id == consumed
    ));

    // The extension must keep the current graph; the pre-rewrite graph is rejected.
    assert!(matches!(
        session.extend(Arc::clone(&with_e1)).await,
        Err(SessionTransitionError::Extension(ExtensionError::Structure))
    ));
    assert!(matches!(
        session.prepare_rewrite(&tagged).await,
        Err(SessionTransitionError::Rewrite(RewriteError::Definition(_)))
    ));
    let revision = session.extend(Arc::clone(&extended)).await.unwrap();
    assert_eq!(revision, 13);
    let snapshot = session.snapshot().await;
    assert_eq!(snapshot.revision(), 13);
    assert_eq!(snapshot.kernel().fingerprint(), extended.fingerprint());
    let state = snapshot.state().clone();
    assert_eq!(state.retirements().len(), 4);
    assert_eq!(
        state.retirement(stranded).unwrap().reason(),
        RetirementReason::RouteRemoved
    );
    assert_eq!(state.retirement(stranded).unwrap().revision(), 3);
    assert!(state.is_quiescent());
    drop(session);
    drop(runtime);

    // Reopening requires the extended binding, and restores the exact records.
    assert!(
        ProposalRuntime::with_grammar(Arc::clone(&with_e1), grammar.clone())
            .open_persistent(&run)
            .is_err()
    );
    let runtime = ProposalRuntime::with_grammar(Arc::clone(&extended), grammar);
    let session = runtime.open_persistent(&run).unwrap();
    let reopened = session.snapshot().await;
    assert_eq!(reopened.state(), &state);
    assert_eq!(reopened.revision(), 13);

    // The new tag is now usable by a rewrite.
    let plan = session.prepare_rewrite(&tagged).await.unwrap();
    assert!(plan.retirements().is_empty());
    let outcome = session.commit_rewrite(plan).await.unwrap();
    assert_eq!(outcome.revision(), 14);
    let installed = session.snapshot().await;
    assert!(installed.kernel().graph().edge("e3").is_some());
    assert!(
        installed
            .kernel()
            .edge_authority_tags("e3")
            .unwrap()
            .contains(&tag("extra"))
    );
    // The root still carries only `route`, so e3 refuses its packages while e2 accepts them.
    let mut refused =
        ActivationProposal::root("a", Authority::new([tag("route")]), bytes(b"result"));
    refused.emit(delivered("e3"));
    assert!(matches!(
        session.submit(refused).await.unwrap(),
        ProposalDecision::Rejected(Reject::EdgeAuthorityMismatch { .. })
    ));
    let received = emit(&session, delivered("e2")).await;
    assert_eq!(
        session.pending_at("b").await.unwrap().packages()[0].0,
        received
    );
}
