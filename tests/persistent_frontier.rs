//! Persistent-session probes: rewrite retirements, explicit retirement, and
//! vocabulary extension survive a reopen with exact records.

use std::collections::BTreeSet;
use std::sync::Arc;

use ontography::{
    ActivationId, ActivationProposal, Authority, AuthorityTag, Contract, DefinitionId, Edge,
    EdgeDefinition, EditPolicy, Emission, ExtensionError, Graph, GraphEdit, GraphFragment,
    IngressMode, Kernel, Node, NodeDefinition, OutputAuthority, PackageId, PermitAll, Phase,
    Principal, ProposalDecision, ProposalRuntime, Reject, RetireError, RetirementReason,
    RewriteError, RewriteRequest, RootRule, Schema, SessionHandle,
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

/// Removes the edges `removed` and adds the edges `added`, annotated as
/// `source` defines them; `a` and `b` survive.
fn swap_edges(removed: &[&str], source: &Kernel, added: &[&str]) -> RewriteRequest {
    let added_edge = |id: &str| added.contains(&id);
    RewriteRequest::new(
        Principal::new("test"),
        GraphEdit::new(
            BTreeSet::new(),
            removed.iter().map(|edge| Arc::from(*edge)).collect(),
            GraphFragment::new(
                vec![],
                source
                    .graph()
                    .edges()
                    .iter()
                    .filter(|edge| added_edge(edge.id()))
                    .cloned()
                    .collect(),
                vec![],
                source
                    .edge_definitions()
                    .iter()
                    .filter(|definition| added_edge(definition.edge_id()))
                    .cloned()
                    .collect(),
                vec![],
                vec![],
            ),
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
    let policy: Arc<dyn EditPolicy> = Arc::new(PermitAll);
    let replace = swap_edges(&["e1"], &with_e2, &["e2"]);
    let tagged = swap_edges(&[], &extended_with_e3, &["e3"]);

    let runtime = ProposalRuntime::with_policy(Arc::clone(&with_e1), Arc::clone(&policy));
    let session = runtime.create_persistent(&run).unwrap();

    // A receipt on e1 at the All receiver, then e1 is replaced: RouteRemoved.
    let stranded = emit(&session, outbound()).await;
    session.transfer(stranded, "e1").await.unwrap().unwrap();
    let plan = session.prepare_rewrite(&replace).await.unwrap().unwrap();
    assert_eq!(
        plan.retirements().get(&stranded),
        Some(&RetirementReason::RouteRemoved)
    );
    let outcome = session.commit_rewrite(plan).await.unwrap().unwrap();
    assert_eq!(outcome.revision(), 3);
    assert!(session.pending_at("b").await.unwrap().packages().is_empty());

    // An outbound package retired explicitly with evidence.
    let unrouted = emit(&session, outbound()).await;
    let evidence = root(&session, None).await;
    let retirement = session
        .retire(unrouted, Some(evidence))
        .await
        .unwrap()
        .unwrap();
    assert_eq!(retirement.reason(), RetirementReason::Explicit);
    let record = session
        .snapshot()
        .await
        .state()
        .package(unrouted)
        .cloned()
        .unwrap();
    assert_eq!(record.holder(), "a");
    assert_eq!(record.phase(), Phase::Out);
    assert_eq!(retirement.revision(), 6);
    assert_eq!(retirement.evidence(), Some(evidence));
    assert!(
        session
            .outbound_page(None, None, usize::MAX)
            .await
            .unwrap()
            .packages()
            .is_empty()
    );
    assert!(matches!(
        session.retire(unrouted, None).await,
        Ok(Err(RetireError::NotLive(id))) if id == unrouted
    ));
    assert!(matches!(
        session
            .retire(stranded, Some(ActivationId::from_u128(5)))
            .await,
        Ok(Err(RetireError::NotLive(_)))
    ));

    // A received package retired explicitly must leave the readiness index.
    let received = emit(&session, delivered("e2")).await;
    assert_eq!(
        session.next_trigger_at("b").await.unwrap().packages().len(),
        1
    );
    let retirement = session.retire(received, None).await.unwrap().unwrap();
    let record = session
        .snapshot()
        .await
        .state()
        .package(received)
        .cloned()
        .unwrap();
    assert_eq!(record.phase(), Phase::In);
    assert_eq!(record.holder(), "b");
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
        Ok(Err(RetireError::UnknownEvidence(_)))
    ));
    assert_eq!(
        session
            .retire(live, None)
            .await
            .unwrap()
            .unwrap()
            .revision(),
        10
    );

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
        Ok(Err(RetireError::NotLive(id))) if id == consumed
    ));

    // The extension must keep the current graph; the pre-rewrite graph is rejected.
    assert!(matches!(
        session.extend(Arc::clone(&with_e1)).await,
        Ok(Err(ExtensionError::Structure))
    ));
    assert!(matches!(
        session.prepare_rewrite(&tagged).await,
        Ok(Err(RewriteError::Definition(_)))
    ));
    let revision = session
        .extend(Arc::clone(&extended))
        .await
        .unwrap()
        .unwrap();
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
        ProposalRuntime::with_policy(Arc::clone(&with_e1), Arc::clone(&policy))
            .open_persistent(&run)
            .is_err()
    );
    let runtime = ProposalRuntime::with_policy(Arc::clone(&extended), policy);
    let session = runtime.open_persistent(&run).unwrap();
    let reopened = session.snapshot().await;
    assert_eq!(reopened.state(), &state);
    assert_eq!(reopened.revision(), 13);

    // The new tag is now usable by a rewrite.
    let plan = session.prepare_rewrite(&tagged).await.unwrap().unwrap();
    assert!(plan.retirements().is_empty());
    let outcome = session.commit_rewrite(plan).await.unwrap().unwrap();
    assert_eq!(outcome.revision(), 14);
    let installed = session.snapshot().await;
    assert!(installed.kernel().graph().edge("e3").is_some());
    assert!(
        installed
            .kernel()
            .edge_definition("e3")
            .unwrap()
            .authority_tags()
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
