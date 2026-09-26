//! Public API probes for interactions that are easy to miss in isolated rule tests.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{
    ActivationProposal, ApplicationBuilder, ApplicationError, Authority, AuthorityTag, Contract,
    DefinitionError, DefinitionId, Edge, EdgeDefinition, Emission, Graph, IngressMode, Kernel,
    Node, NodeComponent, NodeConfig, NodeDefinition, OutputAuthority, PackageId, Phase, Reject,
    RetirementReason, RewriteFragment, RewriteGrammar, RewriteMatch, RewriteProduction,
    RewriteRequest, RootRule, Schema,
};

fn bytes(value: &'static [u8]) -> Arc<[u8]> {
    Arc::from(value)
}

fn tagged_kernel(edge: Option<&str>, ingress: IngressMode) -> Kernel {
    tagged_kernel_with(edge, ingress, "item")
}

fn tagged_kernel_with(edge: Option<&str>, ingress: IngressMode, edge_contract: &str) -> Kernel {
    let tag = AuthorityTag::new("route").unwrap();
    let graph = Graph::new(
        [Node::new("a").unwrap(), Node::new("b").unwrap()],
        edge.into_iter().map(|id| Edge::new(id, "a", "b").unwrap()),
    )
    .unwrap();
    Kernel::admit(
        DefinitionId::new("hypothesis-rewrite").unwrap(),
        Schema::new(["Node"], ["Result", "Item"], [tag.clone()]).unwrap(),
        graph,
        [
            Contract::new("result", "Result", |_| Ok(())).unwrap(),
            Contract::new("item", "Item", |_| Ok(())).unwrap(),
        ],
        [
            NodeDefinition::new("a", ["Node"], "result").unwrap(),
            NodeDefinition::new("b", ["Node"], "result")
                .unwrap()
                .with_ingress_mode(ingress),
        ],
        edge.into_iter().map(|id| {
            EdgeDefinition::new(
                id,
                ["Flow"],
                ["Node"],
                ["Node"],
                edge_contract,
                [tag.clone()],
            )
            .unwrap()
        }),
        [],
        [RootRule::new("a", Authority::new([tag.clone()])).unwrap()],
    )
    .unwrap()
}

fn root_outbound(kernel: &Kernel, state: &mut ontography::State) -> PackageId {
    let mut proposal = ActivationProposal::root(
        "a",
        Authority::new([AuthorityTag::new("route").unwrap()]),
        bytes(b"result"),
    );
    proposal.emit(Emission::outbound(
        "Item",
        OutputAuthority::Carry,
        bytes(b"item"),
    ));
    PackageId::from_parts(kernel.activate(state, proposal).unwrap(), 0)
}

fn rewrite(
    old: &Kernel,
    new: &Kernel,
    old_edge: Option<&str>,
    new_edge: Option<&str>,
) -> (RewriteGrammar, RewriteRequest) {
    let production = RewriteProduction::new(
        "replace-route",
        RewriteFragment::from_kernel(old),
        BTreeSet::from([Arc::from("a"), Arc::from("b")]),
        BTreeSet::new(),
        RewriteFragment::from_kernel(new),
    )
    .unwrap();
    let grammar = RewriteGrammar::new([production]).unwrap();
    let nodes = BTreeMap::from([
        (Arc::from("a"), Arc::from("a")),
        (Arc::from("b"), Arc::from("b")),
    ]);
    let edges = old_edge
        .into_iter()
        .map(|id| (Arc::from(id), Arc::from(id)))
        .collect();
    let fresh_edges = new_edge
        .into_iter()
        .map(|id| (Arc::from(id), Arc::from(id)))
        .collect();
    let request = RewriteRequest::new(
        "replace-route",
        RewriteMatch::new(nodes, edges, BTreeMap::new(), fresh_edges),
    );
    (grammar, request)
}

#[test]
fn identity_graph_rewrite_retains_unroutable_outbound_work() {
    let kernel = tagged_kernel(None, IngressMode::Any);
    let mut state = kernel.empty_state();
    let package = root_outbound(&kernel, &mut state);
    assert_eq!(state.position(package).unwrap().phase(), Phase::Out);

    let (grammar, request) = rewrite(&kernel, &kernel, None, None);
    let prepared = kernel
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert!(prepared.retirements().is_empty());
    let history = state.activations().clone();
    let next = kernel.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(next.fingerprint(), kernel.fingerprint());
    assert_eq!(state.activations(), &history);
    assert_eq!(state.position(package).unwrap().phase(), Phase::Out);
    assert!(state.retirements().is_empty());
    assert_eq!(state.revision(), 2);
}

#[test]
fn changing_the_holders_outgoing_edges_rechecks_outbound_work() {
    let kernel = tagged_kernel(None, IngressMode::Any);
    let rejecting = tagged_kernel_with(Some("e1"), IngressMode::Any, "result");
    let mut state = kernel.empty_state();
    let package = root_outbound(&kernel, &mut state);

    let (grammar, request) = rewrite(&kernel, &rejecting, None, Some("e1"));
    let prepared = kernel
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert_eq!(
        prepared.retirements().get(&package),
        Some(&RetirementReason::NoAcceptingEdge)
    );
    kernel.commit_rewrite(&mut state, prepared).unwrap();
    assert!(state.position(package).is_none());
    let retirement = state.retirement(package).unwrap();
    assert_eq!(retirement.reason(), RetirementReason::NoAcceptingEdge);
    assert_eq!(state.package(package).unwrap().holder(), "a");
    assert_eq!(state.package(package).unwrap().phase(), Phase::Out);
    assert_eq!(retirement.revision(), 2);
    assert_eq!(retirement.evidence(), None);
}

#[test]
fn replacing_an_all_join_edge_retires_the_stranded_receipt() {
    let old = tagged_kernel(Some("e1"), IngressMode::All);
    let new = tagged_kernel(Some("e2"), IngressMode::All);
    let mut state = old.empty_state();
    let package = root_outbound(&old, &mut state);
    let prepared_transfer = old
        .prepare_transfer(&state, package, "e1", b"item")
        .unwrap();
    old.commit_transfer(&mut state, prepared_transfer).unwrap();

    let (grammar, request) = rewrite(&old, &new, Some("e1"), Some("e2"));
    let evidence = BTreeMap::new();
    let prepared = old
        .prepare_rewrite(&state, &grammar, &request, &evidence)
        .unwrap();
    assert_eq!(
        prepared.retirements().get(&package),
        Some(&RetirementReason::RouteRemoved)
    );
    let next = old.commit_rewrite(&mut state, prepared).unwrap();
    assert!(state.position(package).is_none());
    assert!(state.is_quiescent());
    let retirement = state.retirement(package).unwrap();
    assert_eq!(retirement.reason(), RetirementReason::RouteRemoved);
    assert_eq!(state.package(package).unwrap().holder(), "b");
    assert_eq!(state.package(package).unwrap().phase(), Phase::In);
    assert_eq!(retirement.revision(), 3);
    assert_eq!(state.deliveries().get(&package).unwrap().edge_id(), "e1");

    let before = state.clone();
    assert!(matches!(
        next.activate(
            &mut state,
            ActivationProposal::package(package, bytes(b"result")),
        ),
        Err(Reject::PackageRetired { .. })
    ));
    assert_eq!(state, before);
}

#[test]
fn surviving_any_receiver_keeps_its_receipt_after_route_replacement() {
    let old = tagged_kernel(Some("e1"), IngressMode::Any);
    let new = tagged_kernel(Some("e2"), IngressMode::Any);
    let mut state = old.empty_state();
    let package = root_outbound(&old, &mut state);
    let prepared_transfer = old
        .prepare_transfer(&state, package, "e1", b"item")
        .unwrap();
    old.commit_transfer(&mut state, prepared_transfer).unwrap();

    let (grammar, request) = rewrite(&old, &new, Some("e1"), Some("e2"));
    let prepared = old
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert!(prepared.retirements().is_empty());
    let next = old.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(state.position(package).unwrap().phase(), Phase::In);
    next.activate(
        &mut state,
        ActivationProposal::package(package, bytes(b"result")),
    )
    .unwrap();
    assert!(state.is_quiescent());
}

#[test]
fn transfer_before_route_deletion_changes_work_survival() {
    let old = tagged_kernel(Some("e1"), IngressMode::Any);
    let no_route = tagged_kernel(None, IngressMode::Any);
    let (grammar, request) = rewrite(&old, &no_route, Some("e1"), None);

    let mut delivered_first = old.empty_state();
    let delivered = root_outbound(&old, &mut delivered_first);
    let transfer = old
        .prepare_transfer(&delivered_first, delivered, "e1", b"item")
        .unwrap();
    old.commit_transfer(&mut delivered_first, transfer).unwrap();
    let plan = old
        .prepare_rewrite(&delivered_first, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert!(plan.retirements().is_empty());
    let after_delivery = old.commit_rewrite(&mut delivered_first, plan).unwrap();
    assert_eq!(
        delivered_first.position(delivered).unwrap().phase(),
        Phase::In
    );

    let mut deleted_first = old.empty_state();
    let outbound = root_outbound(&old, &mut deleted_first);
    let plan = old
        .prepare_rewrite(&deleted_first, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert_eq!(
        plan.retirements().get(&outbound),
        Some(&RetirementReason::NoAcceptingEdge)
    );
    let after_deletion = old.commit_rewrite(&mut deleted_first, plan).unwrap();
    assert!(deleted_first.position(outbound).is_none());
    assert!(
        after_deletion
            .prepare_transfer(&deleted_first, outbound, "e1", b"item")
            .is_err()
    );
    assert_eq!(after_delivery.fingerprint(), after_deletion.fingerprint());
}

#[test]
fn application_builder_has_one_root_even_when_two_components_are_rootable() {
    let result = Contract::new("result", "Result", |_| Ok(())).unwrap();
    let direct = Kernel::admit(
        DefinitionId::new("two-roots").unwrap(),
        Schema::new(["Node"], ["Result"], []).unwrap(),
        Graph::new([Node::new("a").unwrap(), Node::new("b").unwrap()], []).unwrap(),
        [result.clone()],
        [
            NodeDefinition::new("a", ["Node"], "result").unwrap(),
            NodeDefinition::new("b", ["Node"], "result").unwrap(),
        ],
        [],
        [],
        [
            RootRule::new("a", Authority::new([])).unwrap(),
            RootRule::new("b", Authority::new([])).unwrap(),
        ],
    )
    .unwrap();
    let mut direct_state = direct.empty_state();
    direct
        .activate(
            &mut direct_state,
            ActivationProposal::root("b", Authority::new([]), bytes(b"result")),
        )
        .unwrap();

    let component = || {
        NodeComponent::new(
            NodeConfig::new(["Node"], result.clone()).unwrap(),
            |_| async { Ok(()) },
        )
        .with_root_authority(Authority::new([]))
    };
    let mut builder = ApplicationBuilder::new("two-roots-app").unwrap();
    builder.entry("a", component()).unwrap();
    builder.node("b", component()).unwrap();
    let app = builder.build().unwrap();
    assert_eq!(app.kernel().roots().len(), 1);
    assert!(app.kernel().root_ceiling("b").is_none());
    let mut app_state = app.kernel().empty_state();
    assert!(
        app.kernel()
            .activate(
                &mut app_state,
                ActivationProposal::root("b", Authority::new([]), bytes(b"result")),
            )
            .is_err()
    );
}

#[test]
fn builder_cannot_reserve_authority_for_an_isolated_root() {
    let direct = tagged_kernel(None, IngressMode::Any);
    assert!(direct.root_ceiling("a").is_some());

    let result = Contract::new("result", "Result", |_| Ok(())).unwrap();
    let component = NodeComponent::new(NodeConfig::new(["Node"], result).unwrap(), |_| async {
        Ok(())
    })
    .with_root_authority(Authority::new([AuthorityTag::new("route").unwrap()]));
    let mut builder = ApplicationBuilder::new("isolated-root").unwrap();
    builder.entry("a", component).unwrap();
    assert!(matches!(
        builder.build(),
        Err(ApplicationError::Definition(
            DefinitionError::RootAuthorityOutsideSchema
        ))
    ));
}
