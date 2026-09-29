//! Behavioral checks for the node-held package calculus and admitted graph
//! edits, ported from the sibling application suite and re-targeted to this
//! crate's local cleanup rule: an `Out` package is rechecked only when its
//! holder's outgoing edge identity set changed; an `In` receipt at an `All`
//! receiver is retired only when its delivery edge left the incoming set.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::{Arc, Mutex};

use ontography::{
    ActivationProposal, Authority, AuthorityTransitionRule, DenyAll, Edge, EdgeDefinition,
    EditContext, GraphEdit, GraphFragment, IngressMode, Kernel, Node, NodeDefinition, PackageId,
    PermitAll, Phase, PolicyDenial, Principal, Reject, RetirementReason, RewriteError,
    RewriteRequest, RootRule, StateRestoreError, TransferError,
};

mod support;
use support::{
    authority, delivered, evidence, kernel, names, normalization, outbound, payload, replace,
    request, tag,
};

/// An edit that only adds `fragment`.
fn add(fragment: GraphFragment) -> GraphEdit {
    GraphEdit::new(BTreeSet::new(), BTreeSet::new(), fragment)
}

#[test]
fn atomic_subdivision_preserves_outbound_and_delivered_context_without_transfer() {
    let initial = kernel(&["A", "B", "U"], &[("ab", "A", "B", "payload")]);
    let left = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let right = kernel(
        &["A", "B", "C"],
        &[("ac", "A", "C", "payload"), ("cb", "C", "B", "payload")],
    );
    let subdivide = request(replace(&left, &right, &["A", "B"], &[]));
    let mut state = initial.empty_state();
    let out = outbound(&initial, &mut state, "A");
    let received = delivered(&initial, &mut state, "ab");
    let stranded_context = outbound(&initial, &mut state, "U");
    let before_history = state.activations().clone();
    let before_packages = state.packages().clone();
    let prepared = initial
        .prepare_rewrite(&state, &PermitAll, &subdivide, &evidence())
        .unwrap();
    // local cleanup: U's out-edges are unchanged, so its unroutable package is
    // not rechecked; A's out-edges changed and the fresh `ac` accepts `out`.
    assert!(prepared.retirements().is_empty());
    let next = initial.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(state.position(out).unwrap().holder(), "A");
    assert_eq!(state.position(out).unwrap().phase(), Phase::Out);
    assert_eq!(state.position(received).unwrap().holder(), "B");
    assert_eq!(state.position(received).unwrap().phase(), Phase::In);
    assert_eq!(state.position(stranded_context).unwrap().holder(), "U");
    assert_eq!(
        state.position(stranded_context).unwrap().phase(),
        Phase::Out
    );
    assert!(state.retirements().is_empty());
    assert_eq!(state.deliveries().get(&received).unwrap().edge_id(), "ab");
    assert_eq!(state.activations(), &before_history);
    assert_eq!(state.packages(), &before_packages);
    assert!(next.graph().edge("ab").is_none());
    assert!(matches!(
        state.to_parts(),
        Err(StateRestoreError::UnsupportedDynamicState)
    ));
}

#[test]
fn transfer_is_single_and_requires_phase_type_authority_contract_and_commitment() {
    let initial = kernel(
        &["A", "B"],
        &[
            ("ok", "A", "B", "payload"),
            ("badtype", "A", "B", "other"),
            ("badcap", "A", "B", "unauthorized"),
            ("deny", "A", "B", "deny"),
            ("panic", "A", "B", "panic"),
        ],
    );
    let mut state = initial.empty_state();
    let package = outbound(&initial, &mut state, "A");
    let before = state.clone();
    assert!(matches!(
        initial.activate(&mut state, ActivationProposal::package(package, payload())),
        Err(Reject::PackageNotDelivered { .. })
    ));
    for edge in ["badtype", "badcap", "deny"] {
        let Err(TransferError::Rejected {
            package: id,
            reason,
        }) = initial.prepare_transfer(&state, package, edge, &payload())
        else {
            panic!("edge must reject")
        };
        assert_eq!(id, package);
        assert!(matches!(
            (edge, reason),
            ("badtype", ontography::TransferRejection::ObjectType { .. })
                | ("badcap", ontography::TransferRejection::Authority)
                | ("deny", ontography::TransferRejection::Contract { .. })
        ));
    }
    assert!(matches!(
        initial.prepare_transfer(&state, package, "ok", b"wrong bytes"),
        Err(TransferError::Admission(RewriteError::EvidenceMismatch(_)))
    ));
    assert!(matches!(
        initial.prepare_transfer(&state, package, "panic", &payload()),
        Err(TransferError::Admission(RewriteError::ValidatorPanicked(_)))
    ));
    assert_eq!(state, before);
    let prepared = initial
        .prepare_transfer(&state, package, "ok", &payload())
        .unwrap();
    initial.commit_transfer(&mut state, prepared).unwrap();
    assert_eq!(state.position(package).unwrap().phase(), Phase::In);
    assert!(matches!(
        initial.prepare_transfer(&state, package, "ok", &payload()),
        Err(TransferError::NotOutbound(_))
    ));
    assert_eq!(state.activations(), before.activations());
    initial
        .activate(&mut state, ActivationProposal::package(package, payload()))
        .unwrap();
    assert!(state.position(package).is_none());
}

#[test]
fn ordinary_rejection_retires_but_missing_evidence_and_panics_abort_preparation() {
    for contract in ["payload", "deny", "other", "unauthorized", "panic"] {
        let initial = kernel(&["A", "B"], &[("edge", "A", "B", contract)]);
        let replaced = kernel(&["A", "B"], &[("edge2", "A", "B", contract)]);
        let mut state = initial.empty_state();
        let package = outbound(&initial, &mut state, "A");
        let before = state.clone();

        // local cleanup: the empty edit changes no holder's out-edges, so it
        // retires nothing and never requests evidence, even when the only
        // route would deny or panic.
        let untouched = initial
            .prepare_rewrite_with_evidence(&state, &PermitAll, &normalization(), |_, _| {
                panic!("identity rewrite demanded bytes")
            })
            .unwrap();
        assert!(untouched.retirements().is_empty());

        // Replacing A's only route changes its out-edge set, so `package` is
        // rechecked against the fresh edge under the same contract.
        let swap = request(replace(&initial, &replaced, &["A", "B"], &[]));
        let missing = initial.prepare_rewrite(&state, &PermitAll, &swap, &BTreeMap::new());
        if matches!(contract, "other" | "unauthorized") {
            assert_eq!(
                missing.unwrap().retirements().get(&package),
                Some(&RetirementReason::NoAcceptingEdge)
            );
        } else {
            assert!(matches!(missing, Err(RewriteError::MissingEvidence(_))));
        }
        let result = initial.prepare_rewrite(&state, &PermitAll, &swap, &evidence());
        match contract {
            "payload" => assert!(result.unwrap().retirements().is_empty()),
            "panic" => assert!(matches!(result, Err(RewriteError::ValidatorPanicked(_)))),
            _ => assert_eq!(
                result.unwrap().retirements().get(&package),
                Some(&RetirementReason::NoAcceptingEdge)
            ),
        }
        assert_eq!(state, before);
    }
}

#[test]
fn deletion_retires_both_phases_and_identity_cannot_be_reused() {
    let initial = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let after = kernel(&["A"], &[]);
    let remove_b = request(replace(&initial, &after, &["A"], &[]));
    let recreate_b = request(replace(&after, &initial, &["A"], &[]));
    let mut state = initial.empty_state();
    let inbound = delivered(&initial, &mut state, "ab");
    let outbound_b = outbound(&initial, &mut state, "B");
    let prepared = initial
        .prepare_rewrite(&state, &PermitAll, &remove_b, &BTreeMap::new())
        .unwrap();
    assert_eq!(
        prepared.retirements(),
        BTreeMap::from([
            (inbound, RetirementReason::HolderRemoved),
            (outbound_b, RetirementReason::HolderRemoved),
        ])
    );
    let next = initial.commit_rewrite(&mut state, prepared).unwrap();
    // B and ab are lifetime identities now, so an edit cannot add them again.
    assert!(matches!(
        next.prepare_rewrite(&state, &PermitAll, &recreate_b, &evidence()),
        Err(RewriteError::InvalidEdit(_))
    ));
    assert!(
        next.activate(
            &mut state,
            ActivationProposal::root("B", authority(), payload())
        )
        .is_err()
    );
    assert!(
        next.activate(&mut state, ActivationProposal::package(inbound, payload()))
            .is_err()
    );
    assert!(
        next.activate(
            &mut state,
            ActivationProposal::package(outbound_b, payload())
        )
        .is_err()
    );
}

#[test]
fn dangling_edges_and_survivor_annotations_are_rejected() {
    let initial = kernel(
        &["A", "B", "U"],
        &[("ab", "A", "B", "payload"), ("ub", "U", "B", "payload")],
    );
    let state = initial.empty_state();
    let left = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let right = kernel(&["A"], &[]);
    // Removing B while `ub` survives would leave `ub` without a target.
    let dangling = request(replace(&left, &right, &["A"], &[]));
    assert!(matches!(
        initial.prepare_rewrite(&state, &PermitAll, &dangling, &evidence()),
        Err(RewriteError::InvalidEdit(_))
    ));

    // A surviving node or edge keeps its definition, root rule, and
    // transitions; an edit may annotate only what it adds.
    let annotations = [
        GraphFragment::new(
            vec![],
            vec![],
            vec![NodeDefinition::new("A", ["n"], "result").unwrap()],
            vec![],
            vec![],
            vec![],
        ),
        GraphFragment::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![RootRule::new("A", Authority::new([tag("other")])).unwrap()],
        ),
        GraphFragment::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![
                AuthorityTransitionRule::new("A", authority(), Authority::new([tag("other")]))
                    .unwrap(),
            ],
            vec![],
        ),
        GraphFragment::new(
            vec![],
            vec![],
            vec![],
            vec![
                EdgeDefinition::new("ab", ["flow"], ["n"], ["n"], "payload", [tag("other")])
                    .unwrap(),
            ],
            vec![],
            vec![],
        ),
    ];
    for annotation in annotations {
        assert!(matches!(
            initial.prepare_rewrite(&state, &PermitAll, &request(add(annotation)), &evidence()),
            Err(RewriteError::InvalidEdit(_))
        ));
    }
}

#[test]
fn equal_revision_divergence_and_transfer_make_plans_stale_without_mutation() {
    let initial = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let mut state = initial.empty_state();
    let package = outbound(&initial, &mut state, "A");
    let identity = normalization();
    let rewrite = initial
        .prepare_rewrite(&state, &PermitAll, &identity, &evidence())
        .unwrap();
    let transfer = initial
        .prepare_transfer(&state, package, "ab", &payload())
        .unwrap();
    initial.commit_transfer(&mut state, transfer).unwrap();
    let current = state.clone();
    assert!(matches!(
        initial.commit_rewrite(&mut state, rewrite),
        Err(RewriteError::Stale)
    ));
    assert_eq!(state, current);

    let mut one = initial.empty_state();
    outbound(&initial, &mut one, "A");
    let mut two = initial.empty_state();
    outbound(&initial, &mut two, "B");
    assert_eq!(one.revision(), two.revision());
    let plan = initial
        .prepare_rewrite(&one, &PermitAll, &identity, &evidence())
        .unwrap();
    let before = two.clone();
    assert!(matches!(
        initial.commit_rewrite(&mut two, plan),
        Err(RewriteError::Stale)
    ));
    assert_eq!(two, before);
}

#[test]
fn delivered_retention_does_not_change_topology_relative_all() {
    let with_ingress = |base: Kernel, ingress: IngressMode| {
        Kernel::admit(
            base.id().clone(),
            base.schema().clone(),
            base.graph().clone(),
            base.contracts().iter().cloned(),
            base.node_definitions().iter().cloned().map(|node| {
                if node.node_id() == "B" {
                    node.with_ingress_mode(ingress)
                } else {
                    node
                }
            }),
            base.edge_definitions().iter().cloned(),
            base.authority_transitions().iter().cloned(),
            base.roots().iter().cloned(),
        )
        .unwrap()
    };
    let initial = with_ingress(
        kernel(&["A", "B"], &[("ab", "A", "B", "payload")]),
        IngressMode::All,
    );
    let mut state = initial.empty_state();
    let received = delivered(&initial, &mut state, "ab");
    let right = with_ingress(kernel(&["A", "B"], &[]), IngressMode::All);
    let disconnect = request(replace(&initial, &right, &["A", "B"], &[]));
    let prepared = initial
        .prepare_rewrite(&state, &PermitAll, &disconnect, &BTreeMap::new())
        .unwrap();
    // local cleanup: `ab` left the incoming set of the surviving `All`
    // receiver B, so its receipt is retired as RouteRemoved without evidence.
    assert_eq!(
        prepared.retirements(),
        BTreeMap::from([(received, RetirementReason::RouteRemoved)])
    );
    let next = initial.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(
        next.node_definition("B").unwrap().ingress_mode(),
        IngressMode::All
    );
    assert!(state.position(received).is_none());
    let retirement = state.retirement(received).unwrap();
    assert_eq!(retirement.reason(), RetirementReason::RouteRemoved);
    assert_eq!(state.package(received).unwrap().holder(), "B");
    assert_eq!(state.package(received).unwrap().phase(), Phase::In);
    assert_eq!(retirement.evidence(), None);
    assert_eq!(state.deliveries().get(&received).unwrap().edge_id(), "ab");
    assert!(matches!(
        next.activate(&mut state, ActivationProposal::package(received, payload())),
        Err(Reject::PackageRetired { .. })
    ));

    // local cleanup: an `Any` receiver keeps its receipt through the same
    // disconnection, and the receipt remains consumable.
    let initial = with_ingress(
        kernel(&["A", "B"], &[("ab", "A", "B", "payload")]),
        IngressMode::Any,
    );
    let mut state = initial.empty_state();
    let received = delivered(&initial, &mut state, "ab");
    let right = with_ingress(kernel(&["A", "B"], &[]), IngressMode::Any);
    let disconnect = request(replace(&initial, &right, &["A", "B"], &[]));
    let prepared = initial
        .prepare_rewrite(&state, &PermitAll, &disconnect, &BTreeMap::new())
        .unwrap();
    assert!(prepared.retirements().is_empty());
    let next = initial.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(state.position(received).unwrap().phase(), Phase::In);
    next.activate(&mut state, ActivationProposal::package(received, payload()))
        .unwrap();
    assert!(state.is_quiescent());
}

#[test]
fn evidence_is_requested_only_after_live_custody_and_edge_metadata_require_it() {
    let initial = kernel(
        &["A", "B"],
        &[
            ("type", "A", "B", "other"),
            ("cap", "A", "B", "unauthorized"),
        ],
    );
    let replaced = kernel(
        &["A", "B"],
        &[
            ("type2", "A", "B", "other"),
            ("cap2", "A", "B", "unauthorized"),
        ],
    );
    let mut state = initial.empty_state();
    let package = outbound(&initial, &mut state, "A");

    // local cleanup: the empty edit leaves A's out-edges unchanged, so the
    // unroutable package is neither rechecked nor retired, and no bytes are read.
    let untouched = initial
        .prepare_rewrite_with_evidence(&state, &PermitAll, &normalization(), |_, _| {
            panic!("unchanged holder demanded bytes")
        })
        .unwrap();
    assert!(untouched.retirements().is_empty());

    // Replacing both routes changes A's out-edge set; every fresh edge rejects
    // the package on type or authority metadata, so no bytes are requested.
    let swap = request(replace(&initial, &replaced, &["A", "B"], &[]));
    let prepared = initial
        .prepare_rewrite_with_evidence(&state, &PermitAll, &swap, |_, _| {
            panic!("metadata-rejected edge demanded bytes")
        })
        .unwrap();
    assert_eq!(
        prepared.retirements().get(&package),
        Some(&RetirementReason::NoAcceptingEdge)
    );
    assert!(matches!(
        initial.prepare_transfer_with_evidence(&state, package, "type", |_, _| panic!(
            "type rejection demanded bytes"
        )),
        Err(TransferError::Rejected { .. })
    ));
    let current = initial.commit_rewrite(&mut state, prepared).unwrap();
    assert!(matches!(
        current.prepare_transfer_with_evidence(&state, package, "type2", |_, _| panic!(
            "retired package demanded bytes"
        )),
        Err(TransferError::NotLive(_))
    ));
}

#[test]
fn edits_remove_existing_identities_and_add_only_fresh_ones() {
    let initial = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let left = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let right = kernel(
        &["A", "B", "C"],
        &[("ac", "A", "C", "payload"), ("cb", "C", "B", "payload")],
    );
    let state = initial.empty_state();
    let subdivide = replace(&left, &right, &["A", "B"], &[]);
    let prepared = initial
        .prepare_rewrite(
            &state,
            &PermitAll,
            &request(subdivide.clone()),
            &BTreeMap::new(),
        )
        .unwrap();
    let next = prepared.next_kernel().graph();
    assert!(next.node("C").is_some());
    assert!(next.edge("ab").is_none());
    assert_eq!(
        (
            next.edge("ac").unwrap().source(),
            next.edge("cb").unwrap().target()
        ),
        ("A", "B")
    );

    let with = |remove_nodes: &[&str], remove_edges: &[&str], add: &GraphFragment| {
        request(GraphEdit::new(
            names(remove_nodes),
            names(remove_edges),
            add.clone(),
        ))
    };
    let node_c = |id: &str| {
        GraphFragment::new(
            vec![Node::new(id).unwrap()],
            vec![],
            vec![NodeDefinition::new(id, ["n"], "result").unwrap()],
            vec![],
            vec![],
            vec![],
        )
    };
    let edge = |id: &str| {
        GraphFragment::new(
            vec![],
            vec![Edge::new(id, "A", "B").unwrap()],
            vec![],
            vec![EdgeDefinition::new(id, ["flow"], ["n"], ["n"], "payload", [tag("run")]).unwrap()],
            vec![],
            vec![],
        )
    };
    let empty = GraphFragment::default();
    let invalid = [
        // Removed elements must exist.
        with(&["Z"], &[], &empty),
        with(&[], &["zz"], &empty),
        // Added elements must be fresh for the workflow's lifetime: a live
        // node, a live edge, and an edge removed by the same edit all reuse.
        with(&[], &[], &node_c("B")),
        with(&[], &[], &edge("ab")),
        with(&[], &["ab"], &edge("ab")),
    ];
    for request in invalid {
        assert!(matches!(
            initial.prepare_rewrite(&state, &PermitAll, &request, &BTreeMap::new()),
            Err(RewriteError::InvalidEdit(_))
        ));
    }
    // A fragment naming one fresh node twice fails ordinary admission.
    let duplicated = GraphFragment::new(
        vec![Node::new("C").unwrap(), Node::new("C").unwrap()],
        vec![],
        vec![NodeDefinition::new("C", ["n"], "result").unwrap()],
        vec![],
        vec![],
        vec![],
    );
    assert!(matches!(
        initial.prepare_rewrite(
            &state,
            &PermitAll,
            &with(&[], &[], &duplicated),
            &BTreeMap::new()
        ),
        Err(RewriteError::Definition(_))
    ));
    // An added node without a definition fails admission too.
    let undefined = GraphFragment::new(
        vec![Node::new("C").unwrap()],
        vec![],
        vec![],
        vec![],
        vec![],
        vec![],
    );
    assert!(matches!(
        initial.prepare_rewrite(
            &state,
            &PermitAll,
            &with(&[], &[], &undefined),
            &BTreeMap::new()
        ),
        Err(RewriteError::Definition(_))
    ));
    assert_eq!(state, initial.empty_state());
}

/// What a recording policy saw: principal, whether B exists before and after,
/// and the retirements.
type Seen = (String, bool, bool, BTreeMap<PackageId, RetirementReason>);

#[test]
fn the_policy_decides_after_admission_and_a_refusal_changes_nothing() {
    let initial = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let after = kernel(&["A"], &[]);
    let remove_b = replace(&initial, &after, &["A"], &[]);
    let mut state = initial.empty_state();
    let received = delivered(&initial, &mut state, "ab");
    let before = state.clone();

    // Every default refuses: a runtime or application without a policy
    // accepts no graph edits.
    assert!(matches!(
        initial.prepare_rewrite(
            &state,
            &DenyAll,
            &request(remove_b.clone()),
            &BTreeMap::new()
        ),
        Err(RewriteError::Denied(_))
    ));

    // The policy sees the principal, both definitions, the edit, and the
    // exact retirements, and may refuse with its own reason.
    let seen: Mutex<Vec<Seen>> = Mutex::new(Vec::new());
    let observe = |context: &EditContext<'_>| {
        seen.lock().unwrap().push((
            context.principal.name().to_owned(),
            context.before.graph().node("B").is_some(),
            context.after.graph().node("B").is_some(),
            context.retirements.clone(),
        ));
        if context.principal.name() == "intruder" {
            Err(PolicyDenial::new("intruders may not remove nodes"))
        } else {
            Ok(())
        }
    };
    let as_intruder = RewriteRequest::new(Principal::new("intruder"), remove_b.clone());
    assert!(matches!(
        initial.prepare_rewrite(&state, &observe, &as_intruder, &BTreeMap::new()),
        Err(RewriteError::Denied(reason)) if &*reason == "intruders may not remove nodes"
    ));
    let prepared = initial
        .prepare_rewrite(
            &state,
            &observe,
            &request(remove_b.clone()),
            &BTreeMap::new(),
        )
        .unwrap();
    let expected = BTreeMap::from([(received, RetirementReason::HolderRemoved)]);
    assert_eq!(prepared.retirements(), expected);
    assert_eq!(
        *seen.lock().unwrap(),
        vec![
            ("intruder".to_owned(), true, false, expected.clone()),
            ("test".to_owned(), true, false, expected),
        ]
    );

    // Structure is checked first: an invalid edit is invalid whatever the
    // policy would say, and the policy is not consulted.
    let invalid = request(GraphEdit::new(
        names(&["Z"]),
        BTreeSet::new(),
        GraphFragment::default(),
    ));
    assert!(matches!(
        initial.prepare_rewrite(&state, &DenyAll, &invalid, &BTreeMap::new()),
        Err(RewriteError::InvalidEdit(_))
    ));
    assert!(matches!(
        initial.prepare_rewrite(&state, &observe, &invalid, &BTreeMap::new()),
        Err(RewriteError::InvalidEdit(_))
    ));
    assert_eq!(seen.lock().unwrap().len(), 2);

    // A panicking policy rejects the edit instead of unwinding.
    let panicking = |_: &EditContext<'_>| -> Result<(), PolicyDenial> { panic!("policy fault") };
    assert!(matches!(
        initial.prepare_rewrite(&state, &panicking, &request(remove_b), &BTreeMap::new()),
        Err(RewriteError::PolicyPanicked)
    ));
    assert_eq!(state, before);

    initial.commit_rewrite(&mut state, prepared).unwrap();
    assert_eq!(
        state.retirement(received).unwrap().reason(),
        RetirementReason::HolderRemoved
    );
}

#[test]
fn cleanup_fetches_one_payload_per_package_across_candidate_edges() {
    let initial = kernel(&["A", "B"], &[]);
    let after = kernel(
        &["A", "B"],
        &[
            ("a-deny", "A", "B", "deny"),
            ("b-deny", "A", "B", "deny"),
            ("c-accept", "A", "B", "payload"),
        ],
    );
    let connect = request(replace(&initial, &after, &["A", "B"], &[]));
    let mut state = initial.empty_state();
    let package = outbound(&initial, &mut state, "A");
    let mut reads = 0;
    let plan = initial
        .prepare_rewrite_with_evidence(&state, &PermitAll, &connect, |id, _| {
            assert_eq!(id, package);
            reads += 1;
            Ok(payload())
        })
        .unwrap();
    assert!(plan.retirements().is_empty());
    assert_eq!(reads, 1);
}

#[test]
fn two_real_rewrites_commute_only_with_independent_holder_footprints() {
    let initial = Arc::new(kernel(&["A", "B", "C", "D"], &[]));
    let accepting = kernel(&["A", "B", "C", "D"], &[("ab", "A", "B", "payload")]);
    for (source, independent) in [("C", true), ("A", false)] {
        let rejecting = kernel(&["A", "B", "C", "D"], &[("reject", source, "D", "deny")]);
        let accept = request(replace(&initial, &accepting, &["A", "B", "C", "D"], &[]));
        let reject = request(replace(&initial, &rejecting, &["A", "B", "C", "D"], &[]));
        let mut seed = initial.empty_state();
        outbound(&initial, &mut seed, "A");
        outbound(&initial, &mut seed, "C");
        let run = |order: [&RewriteRequest; 2]| {
            let mut current = Arc::clone(&initial);
            let mut state = seed.clone();
            for request in order {
                let plan = current
                    .prepare_rewrite(&state, &PermitAll, request, &evidence())
                    .unwrap();
                current = current.commit_rewrite(&mut state, plan).unwrap();
            }
            let retired = state
                .packages()
                .iter()
                .filter_map(|(id, record)| record.retirement().map(|r| (*id, r.reason())))
                .collect::<BTreeMap<_, _>>();
            (*current.fingerprint(), state.positions(), retired)
        };
        let forward = run([&accept, &reject]);
        let backward = run([&reject, &accept]);
        assert_eq!(forward.0, backward.0);
        if independent {
            assert_eq!(forward, backward);
        } else {
            assert_ne!(forward.1, backward.1);
        }
    }
}
