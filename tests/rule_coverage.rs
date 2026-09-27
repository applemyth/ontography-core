//! Focused pins for admission rules without a dedicated test in this crate:
//! authority transitions, edge authority matching on emission and transfer,
//! join-shape rejections, root rejections, outbound consumption, schema
//! closure, and the definition fingerprint.

use std::collections::BTreeSet;
use std::sync::Arc;

use ontography::{
    ActivationProposal, Authority, AuthorityMatch, AuthorityTag, AuthorityTransitionRule, Contract,
    ContractViolation, DefinitionError, DefinitionFingerprint, DefinitionId, Edge, EdgeDefinition,
    Emission, Graph, IngressMode, Kernel, Node, NodeDefinition, OutputAuthority, PackageId, Phase,
    Reject, RootRule, Schema, State, TransferError,
};

fn bytes(value: &'static [u8]) -> Arc<[u8]> {
    Arc::from(value)
}

fn tag(id: &str) -> AuthorityTag {
    AuthorityTag::new(id).unwrap()
}

fn authority(tags: &[&str]) -> Authority {
    Authority::new(tags.iter().map(|id| tag(id)))
}

fn names(values: &[&str]) -> BTreeSet<Arc<str>> {
    values.iter().map(|value| Arc::from(*value)).collect()
}

/// How every input list is ordered before it reaches a constructor.
#[derive(Clone, Copy)]
enum Order {
    Forward,
    Reversed,
    Rotated,
}

fn ordered<T: Clone>(order: Order, items: &[T]) -> Vec<T> {
    let mut items = items.to_vec();
    match order {
        Order::Forward => {}
        Order::Reversed => items.reverse(),
        Order::Rotated => {
            if items.len() > 1 {
                items.rotate_left(1);
            }
        }
    }
    items
}

fn authority_of(order: Order, tags: &[&str]) -> Authority {
    Authority::new(ordered(order, tags).into_iter().map(tag))
}

#[derive(Clone)]
struct NodeSpec {
    id: &'static str,
    types: Vec<&'static str>,
    result: &'static str,
    ingress: IngressMode,
}

fn node(id: &'static str, ingress: IngressMode) -> NodeSpec {
    NodeSpec {
        id,
        types: vec!["Node"],
        result: "result",
        ingress,
    }
}

#[derive(Clone)]
struct EdgeSpec {
    id: &'static str,
    types: Vec<&'static str>,
    source: Vec<&'static str>,
    target: Vec<&'static str>,
    contract: &'static str,
    tags: Vec<&'static str>,
    authority_match: AuthorityMatch,
}

fn edge(
    id: &'static str,
    contract: &'static str,
    tags: &[&'static str],
    authority_match: AuthorityMatch,
) -> EdgeSpec {
    EdgeSpec {
        id,
        types: vec!["Flow"],
        source: vec!["Node"],
        target: vec!["Node"],
        contract,
        tags: tags.to_vec(),
        authority_match,
    }
}

/// Plain data for one complete `Kernel::admit` call.
#[derive(Clone)]
struct Spec {
    id: &'static str,
    node_types: Vec<&'static str>,
    object_types: Vec<&'static str>,
    tags: Vec<&'static str>,
    nodes: Vec<&'static str>,
    edges: Vec<(&'static str, &'static str, &'static str)>,
    contracts: Vec<(&'static str, &'static str)>,
    node_definitions: Vec<NodeSpec>,
    edge_definitions: Vec<EdgeSpec>,
    transitions: Vec<(&'static str, Vec<&'static str>, Vec<&'static str>)>,
    roots: Vec<(&'static str, Vec<&'static str>)>,
}

impl Spec {
    /// The shared closed vocabulary with no structure.
    fn vocabulary() -> Self {
        Self {
            id: "rule-coverage",
            node_types: vec!["Node"],
            object_types: vec!["Result", "Item", "Note"],
            tags: vec!["t1", "t2", "t3"],
            nodes: Vec::new(),
            edges: Vec::new(),
            contracts: vec![("result", "Result"), ("item", "Item"), ("note", "Note")],
            node_definitions: Vec::new(),
            edge_definitions: Vec::new(),
            transitions: Vec::new(),
            roots: Vec::new(),
        }
    }

    fn admit(&self, order: Order) -> Kernel {
        self.try_admit(order).unwrap()
    }

    fn try_admit(&self, order: Order) -> Result<Kernel, DefinitionError> {
        self.try_admit_with(order, |_| Ok(()))
    }

    fn try_admit_with<V>(&self, order: Order, validate: V) -> Result<Kernel, DefinitionError>
    where
        V: Fn(&[u8]) -> Result<(), ContractViolation> + Clone + Send + Sync + 'static,
    {
        Kernel::admit(
            DefinitionId::new(self.id)?,
            Schema::new(
                ordered(order, &self.node_types),
                ordered(order, &self.object_types),
                ordered(order, &self.tags).into_iter().map(tag),
            )?,
            Graph::new(
                ordered(order, &self.nodes)
                    .into_iter()
                    .map(|id| Node::new(id).unwrap()),
                ordered(order, &self.edges)
                    .into_iter()
                    .map(|(id, source, target)| Edge::new(id, source, target).unwrap()),
            )?,
            ordered(order, &self.contracts)
                .into_iter()
                .map(|(id, object_type)| Contract::new(id, object_type, validate.clone()).unwrap()),
            ordered(order, &self.node_definitions)
                .into_iter()
                .map(|spec| {
                    NodeDefinition::new(spec.id, ordered(order, &spec.types), spec.result)
                        .unwrap()
                        .with_ingress_mode(spec.ingress)
                }),
            ordered(order, &self.edge_definitions)
                .into_iter()
                .map(|spec| {
                    EdgeDefinition::new(
                        spec.id,
                        ordered(order, &spec.types),
                        ordered(order, &spec.source),
                        ordered(order, &spec.target),
                        spec.contract,
                        ordered(order, &spec.tags).into_iter().map(tag),
                    )
                    .unwrap()
                    .with_authority_match(spec.authority_match)
                }),
            ordered(order, &self.transitions)
                .into_iter()
                .map(|(node_id, from, to)| {
                    AuthorityTransitionRule::new(
                        node_id,
                        authority_of(order, &from),
                        authority_of(order, &to),
                    )
                    .unwrap()
                }),
            ordered(order, &self.roots)
                .into_iter()
                .map(|(node_id, ceiling)| {
                    RootRule::new(node_id, authority_of(order, &ceiling)).unwrap()
                }),
        )
    }
}

/// A line `a → b` with one `item` edge `ab` carrying `tags`, rooted at `a`
/// with the full tag set as ceiling.
fn line(tags: &[&'static str], authority_match: AuthorityMatch, ingress_at_b: IngressMode) -> Spec {
    Spec {
        nodes: vec!["a", "b"],
        edges: vec![("ab", "a", "b")],
        node_definitions: vec![node("a", IngressMode::Any), node("b", ingress_at_b)],
        edge_definitions: vec![edge("ab", "item", tags, authority_match)],
        roots: vec![("a", vec!["t1", "t2", "t3"])],
        ..Spec::vocabulary()
    }
}

/// Two parallel `item` edges `e1`, `e2` from `a` to `b`, rooted at `a` with `t1`.
fn fork(ingress_at_b: IngressMode) -> Spec {
    Spec {
        nodes: vec!["a", "b"],
        edges: vec![("e1", "a", "b"), ("e2", "a", "b")],
        node_definitions: vec![node("a", IngressMode::Any), node("b", ingress_at_b)],
        edge_definitions: vec![
            edge("e1", "item", &["t1"], AuthorityMatch::AnyOf),
            edge("e2", "item", &["t1"], AuthorityMatch::AnyOf),
        ],
        roots: vec![("a", vec!["t1"])],
        ..Spec::vocabulary()
    }
}

/// A root at `a` delivering one `item` package on each of `edges`, in order.
fn root_delivering(edges: &[&str]) -> ActivationProposal {
    let mut proposal = ActivationProposal::root("a", authority(&["t1"]), bytes(b"result"));
    for edge_id in edges {
        proposal.emit(Emission::new(
            *edge_id,
            OutputAuthority::Carry,
            bytes(b"item"),
        ));
    }
    proposal
}

fn carried(state: &State, package: PackageId) -> Authority {
    state.package(package).unwrap().authority().clone()
}

/// Rule: `OutputAuthority::Transition(to)` at node `n` governed by `g` is
/// admitted iff `(n, g, to)` is a sealed rule. `from` must equal `g` exactly,
/// `to == g` still needs an explicit `(n, g, g)` rule, and `Carry` needs none.
#[test]
fn transition_rules_govern_amplification_attenuation_and_explicit_preservation() {
    let kernel = Spec {
        edge_definitions: vec![edge(
            "ab",
            "item",
            &["t1", "t2", "t3"],
            AuthorityMatch::AnyOf,
        )],
        transitions: vec![
            ("a", vec!["t1"], vec!["t1", "t2"]),
            ("a", vec!["t1", "t2"], vec!["t2"]),
            ("a", vec!["t2"], vec!["t2"]),
            ("b", vec!["t1"], vec!["t3"]),
        ],
        ..line(&["t1"], AuthorityMatch::AnyOf, IngressMode::Any)
    }
    .admit(Order::Forward);
    let mut state = kernel.empty_state();
    let emit = |governing: &[&str], output: OutputAuthority| {
        let mut proposal = ActivationProposal::root("a", authority(governing), bytes(b"result"));
        proposal.emit(Emission::outbound("Item", output, bytes(b"item")));
        proposal
    };
    let transition = |tags: &[&str]| OutputAuthority::Transition(authority(tags));
    let unauthorized =
        |node: &str, from: &[&str], to: &[&str]| Reject::UnauthorizedAuthorityTransition {
            node_id: Arc::from(node),
            from: authority(from),
            to: authority(to),
        };

    // Amplification, attenuation, and an explicitly preserved authority.
    let amplified = kernel
        .activate(&mut state, emit(&["t1"], transition(&["t1", "t2"])))
        .unwrap();
    assert_eq!(
        carried(&state, PackageId::from_parts(amplified, 0)),
        authority(&["t1", "t2"])
    );
    let attenuated = kernel
        .activate(&mut state, emit(&["t1", "t2"], transition(&["t2"])))
        .unwrap();
    assert_eq!(
        carried(&state, PackageId::from_parts(attenuated, 0)),
        authority(&["t2"])
    );
    let preserved = kernel
        .activate(&mut state, emit(&["t2"], transition(&["t2"])))
        .unwrap();
    assert_eq!(
        carried(&state, PackageId::from_parts(preserved, 0)),
        authority(&["t2"])
    );

    // No (a, {t1}, {t1}) rule: the explicit form is refused although Carry
    // yields the same authority. A superset governing authority matches no rule.
    let before = state.clone();
    assert_eq!(
        kernel.activate(&mut state, emit(&["t1"], transition(&["t1"]))),
        Err(unauthorized("a", &["t1"], &["t1"]))
    );
    assert_eq!(
        kernel.activate(&mut state, emit(&["t1"], transition(&["t2"]))),
        Err(unauthorized("a", &["t1"], &["t2"]))
    );
    assert_eq!(
        kernel.activate(&mut state, emit(&["t1", "t3"], transition(&["t1", "t2"]))),
        Err(unauthorized("a", &["t1", "t3"], &["t1", "t2"]))
    );
    assert_eq!(state, before);
    let carry = kernel
        .activate(&mut state, emit(&["t1"], OutputAuthority::Carry))
        .unwrap();
    assert_eq!(
        carried(&state, PackageId::from_parts(carry, 0)),
        authority(&["t1"])
    );

    // Rules are node-scoped and govern package-triggered activations too.
    let received = PackageId::from_parts(
        kernel
            .activate(&mut state, root_delivering(&["ab"]))
            .unwrap(),
        0,
    );
    let at_b = |output: OutputAuthority| {
        let mut proposal = ActivationProposal::package(received, bytes(b"result"));
        proposal.emit(Emission::outbound("Note", output, bytes(b"note")));
        proposal
    };
    let before = state.clone();
    assert_eq!(
        kernel.activate(&mut state, at_b(transition(&["t1", "t2"]))),
        Err(unauthorized("b", &["t1"], &["t1", "t2"]))
    );
    assert_eq!(state, before);
    let stepped = kernel
        .activate(&mut state, at_b(transition(&["t3"])))
        .unwrap();
    assert_eq!(
        carried(&state, PackageId::from_parts(stepped, 0)),
        authority(&["t3"])
    );
}

/// Rule: `AuthorityMatch::AnyOf` accepts authority sharing at least one edge
/// tag; `AllOf` requires every edge tag. One rule gates both delivered
/// emission (`Reject::EdgeAuthorityMismatch`) and later explicit transfer
/// (`TransferError::Rejected`), and metadata rejection never reads bytes.
#[test]
fn edge_authority_match_rule_applies_to_emission_and_transfer() {
    let any = line(&["t1", "t2"], AuthorityMatch::AnyOf, IngressMode::Any).admit(Order::Forward);
    let all = line(&["t1", "t2"], AuthorityMatch::AllOf, IngressMode::Any).admit(Order::Forward);
    let delivered = |tags: &[&str]| {
        let mut proposal = ActivationProposal::root("a", authority(tags), bytes(b"result"));
        proposal.emit(Emission::new("ab", OutputAuthority::Carry, bytes(b"item")));
        proposal
    };
    let mismatch = |authority_match, tags: &[&str]| Reject::EdgeAuthorityMismatch {
        edge_id: Arc::from("ab"),
        required: BTreeSet::from([tag("t1"), tag("t2")]),
        authority_match,
        authority: authority(tags),
    };

    let mut any_state = any.empty_state();
    any.activate(&mut any_state, delivered(&["t1"])).unwrap();
    any.activate(&mut any_state, delivered(&["t2", "t3"]))
        .unwrap();
    let before = any_state.clone();
    assert_eq!(
        any.activate(&mut any_state, delivered(&["t3"])),
        Err(mismatch(AuthorityMatch::AnyOf, &["t3"]))
    );
    assert_eq!(
        any.activate(&mut any_state, delivered(&[])),
        Err(mismatch(AuthorityMatch::AnyOf, &[]))
    );
    assert_eq!(any_state, before);

    let mut all_state = all.empty_state();
    let before = all_state.clone();
    assert_eq!(
        all.activate(&mut all_state, delivered(&["t1"])),
        Err(mismatch(AuthorityMatch::AllOf, &["t1"]))
    );
    assert_eq!(
        all.activate(&mut all_state, delivered(&["t2", "t3"])),
        Err(mismatch(AuthorityMatch::AllOf, &["t2", "t3"]))
    );
    assert_eq!(all_state, before);
    all.activate(&mut all_state, delivered(&["t1", "t2"]))
        .unwrap();
    all.activate(&mut all_state, delivered(&["t1", "t2", "t3"]))
        .unwrap();

    // Transfer applies the same rule to an outbound package's carried authority.
    let outbound = |kernel: &Kernel, state: &mut State, tags: &[&str]| {
        let mut proposal = ActivationProposal::root("a", authority(tags), bytes(b"result"));
        proposal.emit(Emission::outbound(
            "Item",
            OutputAuthority::Carry,
            bytes(b"item"),
        ));
        PackageId::from_parts(kernel.activate(state, proposal).unwrap(), 0)
    };
    let shared = outbound(&any, &mut any_state, &["t1"]);
    any.prepare_transfer(&any_state, shared, "ab", b"item")
        .unwrap();
    let disjoint = outbound(&any, &mut any_state, &["t3"]);
    assert_eq!(
        any.prepare_transfer_with_evidence(&any_state, disjoint, "ab", |_, _| panic!(
            "AnyOf rejection demanded bytes"
        ))
        .map(|_| ()),
        Err(TransferError::Rejected {
            package: disjoint,
            reason: ontography::TransferRejection::Authority
        })
    );
    let partial = outbound(&all, &mut all_state, &["t1"]);
    assert_eq!(
        all.prepare_transfer_with_evidence(&all_state, partial, "ab", |_, _| panic!(
            "AllOf rejection demanded bytes"
        ))
        .map(|_| ()),
        Err(TransferError::Rejected {
            package: partial,
            reason: ontography::TransferRejection::Authority
        })
    );
    let complete = outbound(&all, &mut all_state, &["t1", "t2"]);
    let prepared = all
        .prepare_transfer(&all_state, complete, "ab", b"item")
        .unwrap();
    all.commit_transfer(&mut all_state, prepared).unwrap();
    assert_eq!(all_state.position(complete).unwrap().phase(), Phase::In);
    assert_eq!(all_state.position(partial).unwrap().phase(), Phase::Out);
}

/// Rule: `Reject::DuplicateJoinEdge` — every package in a join must realize a
/// distinct incoming edge. The check precedes the ingress-mode shape check.
#[test]
fn a_join_cannot_contain_two_packages_from_one_ingress_edge() {
    let kernel = fork(IngressMode::All).admit(Order::Forward);
    let mut state = kernel.empty_state();
    let producer = kernel
        .activate(&mut state, root_delivering(&["e1", "e1", "e2"]))
        .unwrap();
    let [first, second, other] =
        [0_u128, 1, 2].map(|ordinal| PackageId::from_parts(producer, ordinal));
    let duplicate = Reject::DuplicateJoinEdge {
        node_id: Arc::from("b"),
        edge_id: Arc::from("e1"),
    };

    let before = state.clone();
    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::join([first, second], bytes(b"result"))
        ),
        Err(duplicate.clone())
    );
    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::join([first, second, other], bytes(b"result"))
        ),
        Err(duplicate.clone())
    );
    assert_eq!(
        kernel.prepare_trigger(&state, [first, second]),
        Err(duplicate)
    );
    assert_eq!(state, before);

    kernel
        .activate(
            &mut state,
            ActivationProposal::join([first, other], bytes(b"result")),
        )
        .unwrap();
    // The leftover duplicate stays live but can no longer complete an All join.
    assert!(matches!(
        kernel.activate(
            &mut state,
            ActivationProposal::package(second, bytes(b"result"))
        ),
        Err(Reject::JoinEdgeMismatch { .. })
    ));
    assert_eq!(state.position(second).unwrap().phase(), Phase::In);
}

/// Rule: an `Any` node admits exactly one package (`Reject::JoinNotAllowed`);
/// an `All` node admits exactly one package per incoming edge
/// (`Reject::JoinEdgeMismatch`). `ActivationProposal::package` is the
/// one-element join, so it too must match an `All` node's incoming set.
#[test]
fn ingress_mode_fixes_the_shape_of_a_package_trigger() {
    let pair = |kernel: &Kernel, state: &mut State| {
        let producer = kernel
            .activate(state, root_delivering(&["e1", "e2"]))
            .unwrap();
        (
            PackageId::from_parts(producer, 0),
            PackageId::from_parts(producer, 1),
        )
    };

    let any = fork(IngressMode::Any).admit(Order::Forward);
    let mut state = any.empty_state();
    let (on_e1, on_e2) = pair(&any, &mut state);
    let before = state.clone();
    let not_allowed = Reject::JoinNotAllowed {
        node_id: Arc::from("b"),
        input_count: 2,
    };
    assert_eq!(
        any.activate(
            &mut state,
            ActivationProposal::join([on_e1, on_e2], bytes(b"result"))
        ),
        Err(not_allowed.clone())
    );
    assert_eq!(
        any.prepare_trigger(&state, [on_e1, on_e2]),
        Err(not_allowed)
    );
    assert_eq!(state, before);
    any.activate(
        &mut state,
        ActivationProposal::package(on_e1, bytes(b"result")),
    )
    .unwrap();
    any.activate(
        &mut state,
        ActivationProposal::package(on_e2, bytes(b"result")),
    )
    .unwrap();
    assert!(state.is_quiescent());

    let all = fork(IngressMode::All).admit(Order::Forward);
    let mut state = all.empty_state();
    let (on_e1, on_e2) = pair(&all, &mut state);
    let before = state.clone();
    let mismatch = |actual: &[&str]| Reject::JoinEdgeMismatch {
        node_id: Arc::from("b"),
        expected: names(&["e1", "e2"]),
        actual: names(actual),
    };
    assert_eq!(
        all.activate(
            &mut state,
            ActivationProposal::package(on_e1, bytes(b"result"))
        ),
        Err(mismatch(&["e1"]))
    );
    assert_eq!(
        all.activate(
            &mut state,
            ActivationProposal::join([on_e2], bytes(b"result"))
        ),
        Err(mismatch(&["e2"]))
    );
    assert_eq!(all.prepare_trigger(&state, [on_e2]), Err(mismatch(&["e2"])));
    assert_eq!(state, before);
    let witness = all.prepare_trigger(&state, [on_e1, on_e2]).unwrap();
    assert_eq!(witness.realized_edge_ids(), witness.incoming_edge_ids());
    all.activate(
        &mut state,
        ActivationProposal::join([on_e1, on_e2], bytes(b"result")),
    )
    .unwrap();
    assert!(state.is_quiescent());
}

/// Rule: `Reject::RootNotAllowed` at a node without a `RootRule`, whatever the
/// requested authority; `Reject::RootAuthorityExceeded` when the requested
/// authority is not a subset of the ceiling. Equal and empty authority pass.
#[test]
fn root_activation_needs_a_root_rule_and_stays_within_its_ceiling() {
    let kernel = Spec {
        nodes: vec!["a", "b"],
        node_definitions: vec![node("a", IngressMode::Any), node("b", IngressMode::Any)],
        roots: vec![("a", vec!["t1", "t2"])],
        ..Spec::vocabulary()
    }
    .admit(Order::Forward);
    assert_eq!(kernel.root_ceiling("a"), Some(&authority(&["t1", "t2"])));
    assert_eq!(kernel.root_ceiling("b"), None);
    let root = |node: &str, tags: &[&str]| {
        ActivationProposal::root(node, authority(tags), bytes(b"result"))
    };
    let exceeded = |tags: &[&str]| Reject::RootAuthorityExceeded {
        node_id: Arc::from("a"),
        requested: authority(tags),
        ceiling: authority(&["t1", "t2"]),
    };

    let mut state = kernel.empty_state();
    let before = state.clone();
    for tags in [&[][..], &["t1"]] {
        assert_eq!(
            kernel.activate(&mut state, root("b", tags)),
            Err(Reject::RootNotAllowed {
                node_id: Arc::from("b")
            })
        );
    }
    assert_eq!(
        kernel.activate(&mut state, root("a", &["t3"])),
        Err(exceeded(&["t3"]))
    );
    assert_eq!(
        kernel.activate(&mut state, root("a", &["t1", "t2", "t3"])),
        Err(exceeded(&["t1", "t2", "t3"]))
    );
    assert_eq!(
        kernel.activate(&mut state, root("zzz", &[])),
        Err(Reject::UnknownNode {
            node_id: Arc::from("zzz")
        })
    );
    assert_eq!(state, before);

    kernel
        .activate(&mut state, root("a", &["t1", "t2"]))
        .unwrap();
    kernel.activate(&mut state, root("a", &["t2"])).unwrap();
    kernel.activate(&mut state, root("a", &[])).unwrap();
    assert_eq!(state.activations().len(), 3);
}

/// Rule: `Reject::PackageNotDelivered` — only an `In` package is a trigger
/// input. Custody is checked per package before the join shape, and a later
/// transfer makes the same package consumable.
#[test]
fn an_outbound_package_cannot_trigger_until_it_is_delivered() {
    let kernel = line(&["t1"], AuthorityMatch::AnyOf, IngressMode::Any).admit(Order::Forward);
    let mut state = kernel.empty_state();
    let mut proposal = root_delivering(&["ab"]);
    proposal.emit(Emission::outbound(
        "Item",
        OutputAuthority::Carry,
        bytes(b"item"),
    ));
    let producer = kernel.activate(&mut state, proposal).unwrap();
    let received = PackageId::from_parts(producer, 0);
    let outbound = PackageId::from_parts(producer, 1);
    let not_delivered = Reject::PackageNotDelivered {
        package_id: outbound,
    };

    let before = state.clone();
    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::package(outbound, bytes(b"result"))
        ),
        Err(not_delivered.clone())
    );
    assert_eq!(
        kernel.prepare_trigger(&state, [outbound]),
        Err(not_delivered.clone())
    );
    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::join([received, outbound], bytes(b"result"))
        ),
        Err(not_delivered)
    );
    assert_eq!(state, before);

    let prepared = kernel
        .prepare_transfer(&state, outbound, "ab", b"item")
        .unwrap();
    kernel.commit_transfer(&mut state, prepared).unwrap();
    kernel
        .activate(
            &mut state,
            ActivationProposal::package(outbound, bytes(b"result")),
        )
        .unwrap();
    kernel
        .activate(
            &mut state,
            ActivationProposal::package(received, bytes(b"result")),
        )
        .unwrap();
    assert!(state.is_quiescent());
}

/// Rule: `Reject::AuthorityOutsideSchema` for a root authority or an explicit
/// output authority naming a tag absent from the schema. It precedes the root
/// ceiling, root-rule, transition-rule, and edge-match checks. Definitions are
/// closed the same way: ceilings, transition endpoints, and edge tags must be
/// schema subsets.
#[test]
fn authority_outside_the_schema_is_rejected_before_policy_and_edge_rules() {
    let spec = line(&["t1"], AuthorityMatch::AnyOf, IngressMode::Any);
    let kernel = spec.admit(Order::Forward);
    let outside = authority(&["t1", "t9"]);
    let rejected = |node: &str| Reject::AuthorityOutsideSchema {
        node_id: Arc::from(node),
        authority: outside.clone(),
    };
    let mut state = kernel.empty_state();
    let before = state.clone();

    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::root("a", outside.clone(), bytes(b"result"))
        ),
        Err(rejected("a"))
    );
    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::root("b", outside.clone(), bytes(b"result"))
        ),
        Err(rejected("b"))
    );
    let mut outbound = ActivationProposal::root("a", authority(&["t1"]), bytes(b"result"));
    outbound.emit(Emission::outbound(
        "Item",
        OutputAuthority::Transition(outside.clone()),
        bytes(b"item"),
    ));
    assert_eq!(kernel.activate(&mut state, outbound), Err(rejected("a")));
    let mut delivered = ActivationProposal::root("a", authority(&["t1"]), bytes(b"result"));
    delivered.emit(Emission::new(
        "ab",
        OutputAuthority::Transition(outside.clone()),
        bytes(b"item"),
    ));
    assert_eq!(kernel.activate(&mut state, delivered), Err(rejected("a")));
    assert_eq!(state, before);

    let mut root_outside = spec.clone();
    root_outside.roots = vec![("a", vec!["t9"])];
    assert_eq!(
        root_outside.try_admit(Order::Forward).err(),
        Some(DefinitionError::RootAuthorityOutsideSchema)
    );
    let mut transition_outside = spec.clone();
    transition_outside.transitions = vec![("a", vec!["t1"], vec!["t9"])];
    assert_eq!(
        transition_outside.try_admit(Order::Forward).err(),
        Some(DefinitionError::AuthorityTransitionOutsideSchema)
    );
    let mut edge_outside = spec;
    edge_outside.edge_definitions[0].tags = vec!["t9"];
    assert_eq!(
        edge_outside.try_admit(Order::Forward).err(),
        Some(DefinitionError::ForbiddenAuthorityTag {
            edge: Arc::from("ab"),
            tag: tag("t9"),
        })
    );
}

/// A definition exercising every input list with at least three entries,
/// distinct node types, both ingress modes, both match rules, empty and
/// non-empty requirement sets, and empty and non-empty authorities.
fn rich() -> Spec {
    Spec {
        id: "fingerprint",
        node_types: vec!["Src", "Mid", "Sink"],
        object_types: vec!["Result", "Item", "Note"],
        tags: vec!["t1", "t2", "t3"],
        nodes: vec!["a", "b", "c"],
        edges: vec![("ab", "a", "b"), ("bc", "b", "c"), ("ac", "a", "c")],
        contracts: vec![("result", "Result"), ("item", "Item"), ("note", "Note")],
        node_definitions: vec![
            NodeSpec {
                id: "a",
                types: vec!["Src", "Mid"],
                result: "result",
                ingress: IngressMode::Any,
            },
            NodeSpec {
                id: "b",
                types: vec!["Mid"],
                result: "result",
                ingress: IngressMode::Any,
            },
            NodeSpec {
                id: "c",
                types: vec!["Sink"],
                result: "note",
                ingress: IngressMode::All,
            },
        ],
        edge_definitions: vec![
            EdgeSpec {
                id: "ab",
                types: vec!["Flow"],
                source: vec!["Src"],
                target: vec!["Mid"],
                contract: "item",
                tags: vec!["t1"],
                authority_match: AuthorityMatch::AnyOf,
            },
            EdgeSpec {
                id: "bc",
                types: vec!["Flow", "Audited"],
                source: vec!["Mid"],
                target: vec!["Sink"],
                contract: "note",
                tags: vec!["t2", "t3"],
                authority_match: AuthorityMatch::AllOf,
            },
            EdgeSpec {
                id: "ac",
                types: vec!["Direct"],
                source: Vec::new(),
                target: Vec::new(),
                contract: "item",
                tags: vec!["t1", "t3"],
                authority_match: AuthorityMatch::AnyOf,
            },
        ],
        transitions: vec![
            ("a", vec!["t1"], vec!["t1", "t2"]),
            ("b", vec!["t2"], Vec::new()),
            ("c", vec!["t1", "t2"], vec!["t3"]),
        ],
        roots: vec![
            ("a", vec!["t1", "t2", "t3"]),
            ("b", vec!["t2"]),
            ("c", Vec::new()),
        ],
    }
}

/// Rule: the fingerprint hashes canonical (sorted, deduplicated) structure, so
/// the order of every input list is irrelevant. The definition identity,
/// validator code, and duplicate transition rules lie outside it.
#[test]
fn definition_fingerprint_is_invariant_under_permutation_of_every_input_list() {
    let spec = rich();
    let forward = *spec.admit(Order::Forward).fingerprint();
    assert_eq!(*spec.admit(Order::Reversed).fingerprint(), forward);
    assert_eq!(*spec.admit(Order::Rotated).fingerprint(), forward);

    let renamed = Spec {
        id: "renamed",
        ..spec.clone()
    };
    assert_eq!(*renamed.admit(Order::Forward).fingerprint(), forward);
    let strict = spec
        .try_admit_with(Order::Forward, |bytes| {
            if bytes.is_empty() {
                Err(ContractViolation::new("empty"))
            } else {
                Ok(())
            }
        })
        .unwrap();
    assert_eq!(*strict.fingerprint(), forward);
    let mut duplicated = spec.clone();
    duplicated
        .transitions
        .push(duplicated.transitions[0].clone());
    assert_eq!(*duplicated.admit(Order::Forward).fingerprint(), forward);
    assert_eq!(
        DefinitionFingerprint::from_bytes(*forward.as_bytes()),
        forward
    );
}

/// Rule: every single structural change to any `Kernel::admit` input changes
/// the fingerprint, and distinct changes yield distinct fingerprints.
#[test]
fn definition_fingerprint_changes_under_every_single_structural_change() {
    let base = rich();
    let with = |change: fn(&mut Spec)| {
        let mut spec = base.clone();
        change(&mut spec);
        spec
    };
    let variants = [
        ("schema node type", with(|s| s.node_types.push("Extra"))),
        ("schema object type", with(|s| s.object_types.push("Extra"))),
        ("schema authority tag", with(|s| s.tags.push("t4"))),
        (
            "isolated node",
            with(|s| {
                s.nodes.push("d");
                s.node_definitions.push(node("d", IngressMode::Any));
                s.node_definitions[3].types = vec!["Sink"];
            }),
        ),
        (
            "removed edge",
            with(|s| {
                s.edges.retain(|(id, _, _)| *id != "ac");
                s.edge_definitions.retain(|spec| spec.id != "ac");
            }),
        ),
        ("edge endpoints", with(|s| s.edges[2] = ("ac", "c", "a"))),
        (
            "contract object type",
            with(|s| s.contracts[2] = ("note", "Item")),
        ),
        (
            "extra contract",
            with(|s| s.contracts.push(("memo", "Note"))),
        ),
        (
            "node types",
            with(|s| s.node_definitions[1].types.push("Src")),
        ),
        (
            "node result contract",
            with(|s| s.node_definitions[1].result = "note"),
        ),
        (
            "node ingress mode",
            with(|s| s.node_definitions[2].ingress = IngressMode::Any),
        ),
        (
            "edge types",
            with(|s| s.edge_definitions[0].types.push("Audited")),
        ),
        (
            "edge source requirements",
            with(|s| s.edge_definitions[0].source.clear()),
        ),
        (
            "edge target requirements",
            with(|s| s.edge_definitions[0].target.clear()),
        ),
        (
            "edge package contract",
            with(|s| s.edge_definitions[0].contract = "note"),
        ),
        (
            "edge authority match",
            with(|s| s.edge_definitions[0].authority_match = AuthorityMatch::AllOf),
        ),
        (
            "edge authority tags",
            with(|s| s.edge_definitions[0].tags.push("t2")),
        ),
        (
            "removed transition",
            with(|s| {
                s.transitions.pop();
            }),
        ),
        ("transition node", with(|s| s.transitions[0].0 = "b")),
        (
            "transition source",
            with(|s| s.transitions[0].1 = vec!["t3"]),
        ),
        (
            "transition target",
            with(|s| s.transitions[0].2 = vec!["t3"]),
        ),
        (
            "removed root",
            with(|s| {
                s.roots.pop();
            }),
        ),
        ("root ceiling", with(|s| s.roots[1].1 = vec!["t2", "t3"])),
    ];
    let mut seen = BTreeSet::from([*base.admit(Order::Forward).fingerprint()]);
    for (change, spec) in variants {
        assert!(
            seen.insert(*spec.admit(Order::Forward).fingerprint()),
            "{change} left the fingerprint unchanged or collided"
        );
    }
    assert_eq!(seen.len(), 24);
}

/// Fixed-graph replay rejects a persisted output whose declared object type
/// is not the accepting edge contract's type: `Reject::PackageTypeMismatch`.
#[test]
fn replay_rejects_an_output_whose_declared_type_disagrees_with_its_edge() {
    use std::collections::BTreeMap;
    use std::sync::Arc;

    use ontography::{
        Activation, ActivationId, Authority, AuthorityTag, ContentDigest, Contract, DefinitionId,
        Edge, EdgeDefinition, Graph, Kernel, Node, NodeDefinition, Output, PackageId, Reject,
        RootRule, Schema, StateParts, StateRestoreError, Trigger,
    };

    let tag = AuthorityTag::new("t").unwrap();
    let kernel = Kernel::admit(
        DefinitionId::new("replay").unwrap(),
        Schema::new(["Node"], ["Value", "Other"], [tag.clone()]).unwrap(),
        Graph::new(
            [Node::new("a").unwrap(), Node::new("b").unwrap()],
            [Edge::new("ab", "a", "b").unwrap()],
        )
        .unwrap(),
        [
            Contract::new("value", "Value", |_| Ok(())).unwrap(),
            Contract::new("other", "Other", |_| Ok(())).unwrap(),
        ],
        ["a", "b"].map(|node| NodeDefinition::new(node, ["Node"], "value").unwrap()),
        [
            EdgeDefinition::new("ab", ["Flow"], ["Node"], ["Node"], "value", [tag.clone()])
                .unwrap(),
        ],
        [],
        [RootRule::new("a", Authority::new([tag.clone()])).unwrap()],
    )
    .unwrap();
    let payload: Arc<[u8]> = Arc::from(b"bytes".as_slice());
    let digest = ContentDigest::compute(&payload);
    let producer = ActivationId::from_u128(1);
    let package = PackageId::from_parts(producer, 0);
    let activation = Activation::new(
        "a",
        Trigger::Orig {
            node_id: Arc::from("a"),
            authority: Authority::new([tag.clone()]),
        },
        Arc::clone(&payload),
        BTreeMap::from([(
            package,
            Output::new("ab", "Other", Authority::new([tag]), digest),
        )]),
    );
    let parts = StateParts::new(
        kernel.id().clone(),
        *kernel.fingerprint(),
        BTreeMap::from([(producer, activation)]),
    );
    let error = kernel
        .restore_state(parts, &BTreeMap::from([(digest, payload)]))
        .unwrap_err();
    assert!(matches!(
        error,
        StateRestoreError::InvalidActivation { activation_id, source }
            if activation_id == producer
                && matches!(*source, Reject::PackageTypeMismatch { package_id, .. } if package_id == package)
    ));
}
