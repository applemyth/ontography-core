//! Direct-kernel probes for explicit retirement, local rewrite cleanup, and
//! monotone vocabulary extension.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::{
    ActivationId, ActivationProposal, Authority, AuthorityTag, ContentDigest, Contract,
    DefinitionId, Edge, EdgeDefinition, Emission, ExtensionError, Graph, IngressMode, Kernel, Node,
    NodeDefinition, OutputAuthority, PackageId, Phase, Reject, RetireError, RetirementReason,
    RewriteError, RewriteFragment, RewriteGrammar, RewriteMatch, RewriteProduction, RewriteRequest,
    RootRule, Schema, State, StateRestoreError, TransferError,
};

fn bytes(value: &'static [u8]) -> Arc<[u8]> {
    Arc::from(value)
}

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}

/// One edge from `a` to `b`: identity, package contract, authority tag.
type EdgeSpec<'a> = (&'a str, &'a str, &'a str);

/// A closed vocabulary. Kernels built from one `Vocabulary` value, or from
/// its `extend()` copies, share validator identities.
struct Vocabulary {
    result: Contract,
    item: Contract,
    item_present: bool,
    extra: Vec<Contract>,
    tags: Vec<&'static str>,
    object_types: Vec<&'static str>,
}

impl Vocabulary {
    fn base() -> Self {
        Self {
            result: Contract::new("result", "Result", |_| Ok(())).unwrap(),
            item: Contract::new("item", "Item", |_| Ok(())).unwrap(),
            item_present: true,
            extra: Vec::new(),
            tags: vec!["route", "spare"],
            object_types: vec!["Result", "Item"],
        }
    }

    /// A copy that keeps the existing contracts' validator identities.
    fn extend(&self) -> Self {
        Self {
            result: self.result.clone(),
            item: self.item.clone(),
            item_present: self.item_present,
            extra: self.extra.clone(),
            tags: self.tags.clone(),
            object_types: self.object_types.clone(),
        }
    }

    fn contracts(&self) -> Vec<Contract> {
        let mut contracts = vec![self.result.clone()];
        if self.item_present {
            contracts.push(self.item.clone());
        }
        contracts.extend(self.extra.iter().cloned());
        contracts
    }
}

fn admit(
    id: &str,
    vocabulary: &Vocabulary,
    nodes: &[&str],
    edges: &[EdgeSpec<'_>],
    ingress: IngressMode,
) -> Kernel {
    Kernel::admit(
        DefinitionId::new(id).unwrap(),
        Schema::new(
            ["Node"],
            vocabulary.object_types.iter().copied(),
            vocabulary.tags.iter().map(|id| tag(id)),
        )
        .unwrap(),
        Graph::new(
            nodes.iter().map(|node| Node::new(*node).unwrap()),
            edges
                .iter()
                .map(|(edge, _, _)| Edge::new(*edge, "a", "b").unwrap()),
        )
        .unwrap(),
        vocabulary.contracts(),
        nodes.iter().map(|node| {
            let definition = NodeDefinition::new(*node, ["Node"], "result").unwrap();
            if *node == "b" {
                definition.with_ingress_mode(ingress)
            } else {
                definition
            }
        }),
        edges.iter().map(|(edge, contract, edge_tag)| {
            EdgeDefinition::new(
                *edge,
                ["Flow"],
                ["Node"],
                ["Node"],
                *contract,
                [tag(edge_tag)],
            )
            .unwrap()
        }),
        [],
        [RootRule::new("a", Authority::new([tag("route")])).unwrap()],
    )
    .unwrap()
}

/// The sub-definition of `kernel` induced by `nodes`, as a rule-local fragment.
fn fragment(kernel: &Kernel, nodes: &[&str]) -> RewriteFragment {
    let keep: BTreeSet<&str> = nodes.iter().copied().collect();
    let kept_edge = |id: &str| {
        kernel
            .graph()
            .edge(id)
            .is_some_and(|edge| keep.contains(edge.source()) && keep.contains(edge.target()))
    };
    RewriteFragment::new(
        kernel
            .graph()
            .nodes()
            .iter()
            .filter(|node| keep.contains(node.id()))
            .cloned()
            .collect(),
        kernel
            .graph()
            .edges()
            .iter()
            .filter(|edge| kept_edge(edge.id()))
            .cloned()
            .collect(),
        kernel
            .node_definitions()
            .iter()
            .filter(|node| keep.contains(node.node_id()))
            .cloned()
            .collect(),
        kernel
            .edge_definitions()
            .iter()
            .filter(|edge| kept_edge(edge.edge_id()))
            .cloned()
            .collect(),
        Vec::new(),
        kernel
            .roots()
            .iter()
            .filter(|root| keep.contains(root.node_id()))
            .cloned()
            .collect(),
    )
}

fn ids(pairs: &[(&str, &str)]) -> BTreeMap<Arc<str>, Arc<str>> {
    pairs
        .iter()
        .map(|(symbol, actual)| (Arc::from(*symbol), Arc::from(*actual)))
        .collect()
}

fn names(values: &[&str]) -> BTreeSet<Arc<str>> {
    values.iter().map(|value| Arc::from(*value)).collect()
}

fn root(kernel: &Kernel, state: &mut State, emissions: &[Emission]) -> ActivationId {
    let mut proposal =
        ActivationProposal::root("a", Authority::new([tag("route")]), bytes(b"result"));
    for emission in emissions {
        proposal.emit(emission.clone());
    }
    kernel.activate(state, proposal).unwrap()
}

fn outbound() -> Emission {
    Emission::outbound("Item", OutputAuthority::Carry, bytes(b"item"))
}

fn delivered(edge: &str) -> Emission {
    Emission::new(edge, OutputAuthority::Carry, bytes(b"item"))
}

/// Retirement records keyed by output ordinal, without their revision stamps:
/// activation identities are random per run, and the stamp records which
/// step retired a package, which is order-dependent by construction.
type Projected = Vec<(u128, RetirementReason, String, Phase, Option<ActivationId>)>;

fn projected(state: &State) -> Projected {
    state
        .retired()
        .map(|(id, record)| {
            let r = record.retirement().expect("retired record");
            (
                id.output(),
                r.reason(),
                record.holder().to_owned(),
                record.phase(),
                r.evidence(),
            )
        })
        .collect()
}

#[test]
fn explicit_retirement_is_a_recorded_frontier_mutation() {
    let vocabulary = Vocabulary::base();
    let kernel = admit(
        "retire",
        &vocabulary,
        &["a", "b"],
        &[("e1", "item", "route")],
        IngressMode::Any,
    );
    let mut state = kernel.empty_state();
    let received = PackageId::from_parts(root(&kernel, &mut state, &[delivered("e1")]), 0);
    let unrouted = PackageId::from_parts(root(&kernel, &mut state, &[outbound()]), 0);
    let evidence = root(&kernel, &mut state, &[]);
    assert_eq!(state.revision(), 3);

    let retirement = kernel.retire(&mut state, received, Some(evidence)).unwrap();
    assert_eq!(retirement.reason(), RetirementReason::Explicit);
    assert_eq!(state.package(received).unwrap().holder(), "b");
    assert_eq!(state.package(received).unwrap().phase(), Phase::In);
    assert_eq!(retirement.revision(), 4);
    assert_eq!(retirement.evidence(), Some(evidence));
    assert_eq!(state.retirement(received), Some(&retirement));
    assert!(state.position(received).is_none());
    assert_eq!(state.revision(), 4);
    assert_eq!(state.deliveries().get(&received).unwrap().edge_id(), "e1");

    assert!(matches!(
        kernel.activate(
            &mut state,
            ActivationProposal::package(received, bytes(b"result"))
        ),
        Err(Reject::PackageRetired { .. })
    ));
    assert_eq!(
        kernel.retire(&mut state, received, None).unwrap_err(),
        RetireError::NotLive(received)
    );
    assert!(matches!(
        kernel.prepare_transfer(&state, received, "e1", b"item"),
        Err(TransferError::NotLive(_))
    ));

    let before = state.clone();
    let unknown = ActivationId::from_u128(99);
    assert_eq!(
        kernel
            .retire(&mut state, unrouted, Some(unknown))
            .unwrap_err(),
        RetireError::UnknownEvidence(unknown)
    );
    assert_eq!(state, before);

    let retirement = kernel.retire(&mut state, unrouted, None).unwrap();
    assert_eq!(state.package(unrouted).unwrap().phase(), Phase::Out);
    assert_eq!(state.package(unrouted).unwrap().holder(), "a");
    assert_eq!(retirement.evidence(), None);
    assert_eq!(retirement.revision(), 5);
    assert!(state.is_quiescent());
    assert_eq!(state.activations().len(), 3);
    assert_eq!(
        state.to_parts().unwrap_err(),
        StateRestoreError::UnsupportedDynamicState
    );

    let consumed = PackageId::from_parts(root(&kernel, &mut state, &[delivered("e1")]), 0);
    kernel
        .activate(
            &mut state,
            ActivationProposal::package(consumed, bytes(b"result")),
        )
        .unwrap();
    assert_eq!(
        kernel.retire(&mut state, consumed, None).unwrap_err(),
        RetireError::NotLive(consumed)
    );

    let other = admit(
        "other",
        &vocabulary,
        &["a", "b"],
        &[("e1", "item", "route")],
        IngressMode::Any,
    );
    let live = PackageId::from_parts(root(&kernel, &mut state, &[outbound()]), 0);
    assert_eq!(
        other.retire(&mut state, live, None).unwrap_err(),
        RetireError::Admission(RewriteError::StateMismatch)
    );
}

#[test]
fn removing_one_route_of_an_all_receiver_retires_only_that_receipt() {
    let vocabulary = Vocabulary::base();
    let two = admit(
        "all",
        &vocabulary,
        &["a", "b"],
        &[("e1", "item", "route"), ("e2", "item", "route")],
        IngressMode::All,
    );
    let one = admit(
        "all",
        &vocabulary,
        &["a", "b"],
        &[("e1", "item", "route")],
        IngressMode::All,
    );
    let grammar = RewriteGrammar::new([RewriteProduction::new(
        "drop-e2",
        fragment(&two, &["a", "b"]),
        names(&["a", "b"]),
        names(&["e1"]),
        fragment(&one, &["a", "b"]),
    )
    .unwrap()])
    .unwrap();
    let request = RewriteRequest::new(
        "drop-e2",
        RewriteMatch::new(
            ids(&[("a", "a"), ("b", "b")]),
            ids(&[("e1", "e1"), ("e2", "e2")]),
            ids(&[]),
            ids(&[]),
        ),
    );

    let mut state = two.empty_state();
    let producer = root(&two, &mut state, &[delivered("e1"), delivered("e2")]);
    let (on_e1, on_e2) = (
        PackageId::from_parts(producer, 0),
        PackageId::from_parts(producer, 1),
    );
    let prepared = two
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert_eq!(
        prepared.retirements().iter().collect::<Vec<_>>(),
        vec![(&on_e2, &RetirementReason::RouteRemoved)]
    );
    let current = two.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(state.position(on_e1).unwrap().phase(), Phase::In);
    current
        .activate(
            &mut state,
            ActivationProposal::package(on_e1, bytes(b"result")),
        )
        .unwrap();
    assert!(state.is_quiescent());
}

#[test]
fn disjoint_rewrites_commute_on_the_frontier() {
    let vocabulary = Vocabulary::base();
    let nodes = ["a", "b", "far"];
    let without = Arc::new(admit("commute", &vocabulary, &nodes, &[], IngressMode::Any));
    let accepting = admit(
        "commute",
        &vocabulary,
        &nodes,
        &[("e1", "item", "route")],
        IngressMode::Any,
    );
    let rejecting = admit(
        "commute",
        &vocabulary,
        &nodes,
        &[("e1", "result", "route")],
        IngressMode::Any,
    );
    let connect = |id: &str, right: &Kernel| {
        RewriteProduction::new(
            id,
            fragment(&without, &["a", "b"]),
            names(&["a", "b"]),
            BTreeSet::new(),
            fragment(right, &["a", "b"]),
        )
        .unwrap()
    };
    let grammar = RewriteGrammar::new([
        RewriteProduction::new(
            "far",
            fragment(&without, &["far"]),
            names(&["far"]),
            BTreeSet::new(),
            fragment(&without, &["far"]),
        )
        .unwrap(),
        connect("accept", &accepting),
        connect("reject", &rejecting),
    ])
    .unwrap();
    let far = RewriteRequest::new(
        "far",
        RewriteMatch::new(ids(&[("far", "far")]), ids(&[]), ids(&[]), ids(&[])),
    );
    let route = |id: &str| {
        RewriteRequest::new(
            id,
            RewriteMatch::new(
                ids(&[("a", "a"), ("b", "b")]),
                ids(&[]),
                ids(&[]),
                ids(&[("e1", "e1")]),
            ),
        )
    };
    let evidence = BTreeMap::from([(ContentDigest::compute(b"item"), bytes(b"item"))]);

    let run = |order: [&RewriteRequest; 2]| {
        let mut state = without.empty_state();
        let package = PackageId::from_parts(root(&without, &mut state, &[outbound()]), 0);
        let mut kernel = Arc::clone(&without);
        for request in order {
            let prepared = kernel
                .prepare_rewrite(&state, &grammar, request, &evidence)
                .unwrap();
            kernel = kernel.commit_rewrite(&mut state, prepared).unwrap();
        }
        (
            *kernel.fingerprint(),
            state.position(package),
            projected(&state),
            state,
        )
    };

    let accept = route("accept");
    let far_first = run([&far, &accept]);
    let route_first = run([&accept, &far]);
    assert_eq!(far_first.0, route_first.0);
    assert_eq!(far_first.1, route_first.1);
    assert_eq!(far_first.2, route_first.2);
    assert_eq!(far_first.1.unwrap().phase(), Phase::Out);
    assert!(far_first.2.is_empty());

    // A route the package cannot use retires it in both orders. Only the
    // revision stamp differs, because a different step retired it.
    let reject = route("reject");
    let far_first = run([&far, &reject]);
    let route_first = run([&reject, &far]);
    assert_eq!(far_first.0, route_first.0);
    assert_eq!(far_first.1, None);
    assert_eq!(route_first.1, None);
    assert_eq!(far_first.2, route_first.2);
    assert_eq!(far_first.2[0].1, RetirementReason::NoAcceptingEdge);
    let stamp = |state: &State| state.retirements().values().next().unwrap().revision();
    assert_eq!((stamp(&far_first.3), stamp(&route_first.3)), (3, 2));
}

#[test]
fn vocabulary_extension_admits_only_monotone_additions() {
    let base_vocabulary = Vocabulary::base();
    let base = admit("ext", &base_vocabulary, &["a", "b"], &[], IngressMode::Any);
    let mut extended_vocabulary = base_vocabulary.extend();
    extended_vocabulary.tags.push("extra");
    extended_vocabulary.object_types.push("Note");
    extended_vocabulary
        .extra
        .push(Contract::new("note", "Note", |_| Ok(())).unwrap());
    let extended = Arc::new(admit(
        "ext",
        &extended_vocabulary,
        &["a", "b"],
        &[],
        IngressMode::Any,
    ));

    let mut state = base.empty_state();
    let package = PackageId::from_parts(root(&base, &mut state, &[outbound()]), 0);
    let before_extension = state.clone();

    let grammar = RewriteGrammar::new([RewriteProduction::new(
        "connect",
        fragment(&base, &["a", "b"]),
        names(&["a", "b"]),
        BTreeSet::new(),
        fragment(
            &admit(
                "ext",
                &extended_vocabulary,
                &["a", "b"],
                &[("e1", "note", "extra")],
                IngressMode::Any,
            ),
            &["a", "b"],
        ),
    )
    .unwrap()])
    .unwrap();
    let connect = RewriteRequest::new(
        "connect",
        RewriteMatch::new(
            ids(&[("a", "a"), ("b", "b")]),
            ids(&[]),
            ids(&[]),
            ids(&[("e1", "e1")]),
        ),
    );
    assert!(matches!(
        base.prepare_rewrite(&before_extension, &grammar, &connect, &BTreeMap::new()),
        Err(RewriteError::Definition(_))
    ));

    let prepared = base
        .prepare_extension(&state, Arc::clone(&extended))
        .unwrap();
    assert_eq!(prepared.transition().base().revision(), 1);
    assert!(Arc::ptr_eq(prepared.next_kernel(), &extended));
    let current = base.commit_extension(&mut state, prepared).unwrap();
    assert_eq!(current.fingerprint(), extended.fingerprint());
    assert_eq!(state.definition_fingerprint(), extended.fingerprint());
    assert_eq!(state.revision(), 2);
    assert_eq!(state.positions(), before_extension.positions());
    assert_eq!(state.activations(), before_extension.activations());
    assert!(matches!(
        base.activate(
            &mut state,
            ActivationProposal::root("a", Authority::new([tag("route")]), bytes(b"result"))
        ),
        Err(Reject::StateMismatch { .. })
    ));

    // The new edge carries the new contract, whose object type is Note, so the
    // outbound Item at `a` is rechecked (its holder's edges changed) and retired.
    let prepared = current
        .prepare_rewrite(&state, &grammar, &connect, &BTreeMap::new())
        .unwrap();
    assert_eq!(
        prepared.retirements().get(&package),
        Some(&RetirementReason::NoAcceptingEdge)
    );
    let current = current.commit_rewrite(&mut state, prepared).unwrap();
    assert!(current.graph().edge("e1").is_some());
    assert_eq!(
        state.retirement(package).unwrap().reason(),
        RetirementReason::NoAcceptingEdge
    );
    assert_eq!(state.retirement(package).unwrap().revision(), 3);

    let rejects = |candidate: Kernel| {
        let state = base.empty_state();
        base.prepare_extension(&state, Arc::new(candidate))
            .map(|_| ())
            .unwrap_err()
    };
    let mut narrowed = base_vocabulary.extend();
    narrowed.tags = vec!["route"];
    assert_eq!(
        rejects(admit("ext", &narrowed, &["a", "b"], &[], IngressMode::Any)),
        ExtensionError::SchemaNarrowed
    );
    let mut changed = base_vocabulary.extend();
    changed.item = Contract::new("item", "Item", |_| Ok(())).unwrap();
    changed.tags.push("extra");
    assert_eq!(
        rejects(admit("ext", &changed, &["a", "b"], &[], IngressMode::Any)),
        ExtensionError::ContractChanged(Arc::from("item"))
    );
    let mut removed = base_vocabulary.extend();
    removed.item_present = false;
    removed.tags.push("extra");
    assert_eq!(
        rejects(admit("ext", &removed, &["a", "b"], &[], IngressMode::Any)),
        ExtensionError::ContractRemoved(Arc::from("item"))
    );
    assert_eq!(
        rejects(admit(
            "ext",
            &base_vocabulary.extend(),
            &["a", "b"],
            &[],
            IngressMode::Any
        )),
        ExtensionError::Unchanged
    );
    assert_eq!(
        rejects(admit(
            "other",
            &extended_vocabulary,
            &["a", "b"],
            &[],
            IngressMode::Any
        )),
        ExtensionError::DefinitionId
    );
    assert_eq!(
        rejects(admit(
            "ext",
            &extended_vocabulary,
            &["a", "b", "c"],
            &[],
            IngressMode::Any
        )),
        ExtensionError::Structure
    );
    assert_eq!(
        rejects(admit(
            "ext",
            &extended_vocabulary,
            &["a", "b"],
            &[],
            IngressMode::All
        )),
        ExtensionError::Structure
    );

    // A plan prepared against another definition version is stale before
    // the committing kernel considers its vocabulary.
    let mut other = base_vocabulary.extend();
    other.tags.push("other");
    let sibling = admit("ext", &other, &["a", "b"], &[], IngressMode::Any);
    let mut sibling_state = sibling.empty_state();
    let foreign = base
        .prepare_extension(&base.empty_state(), Arc::clone(&extended))
        .unwrap();
    assert_eq!(
        sibling
            .commit_extension(&mut sibling_state, foreign)
            .unwrap_err(),
        ExtensionError::Stale
    );

    let mut stale_state = base.empty_state();
    let prepared = base
        .prepare_extension(&stale_state, Arc::clone(&extended))
        .unwrap();
    root(&base, &mut stale_state, &[]);
    assert_eq!(
        base.commit_extension(&mut stale_state, prepared)
            .unwrap_err(),
        ExtensionError::Stale
    );
    assert_eq!(stale_state.revision(), 1);
    assert_eq!(stale_state.definition_fingerprint(), base.fingerprint());
}
