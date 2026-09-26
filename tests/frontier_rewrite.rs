//! Behavioral checks for the node-held package calculus and admitted rewrites,
//! ported from the sibling application suite and re-targeted to this crate's
//! local cleanup rule: an `Out` package is rechecked only when its holder's
//! outgoing edge identity set changed; an `In` receipt at an `All` receiver is
//! retired only when its delivery edge left the incoming set.

use std::collections::BTreeMap;
use std::sync::Arc;

use ontography::{
    ActivationProposal, IngressMode, Kernel, Phase, Reject, RetirementReason, RewriteError,
    RewriteFragment, RewriteGrammar, RewriteMatch, RewriteProduction, RewriteRequest,
    StateRestoreError, TransferError,
};

mod support;
use support::{
    authority, bindings, delivered, evidence, kernel, names, normalization, outbound, payload, rule,
};

#[test]
fn atomic_subdivision_preserves_outbound_and_delivered_context_without_transfer() {
    let initial = kernel(&["A", "B", "U"], &[("ab", "A", "B", "payload")]);
    let left = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let right = kernel(
        &["A", "B", "C"],
        &[("ac", "A", "C", "payload"), ("cb", "C", "B", "payload")],
    );
    let (production, request) = rule("subdivide", &left, &right, &["A", "B"], &[]);
    let grammar = RewriteGrammar::new([production]).unwrap();
    let mut state = initial.empty_state();
    let out = outbound(&initial, &mut state, "A");
    let received = delivered(&initial, &mut state, "ab");
    let stranded_context = outbound(&initial, &mut state, "U");
    let before_history = state.activations().clone();
    let before_packages = state.packages().clone();
    let prepared = initial
        .prepare_rewrite(&state, &grammar, &request, &evidence())
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
        assert!(
            matches!(initial.prepare_transfer(&state, package, edge, &payload()), Err(TransferError::Rejected(id)) if id == package)
        );
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

        // local cleanup: an identity rewrite (L = K = R) changes no holder's
        // out-edges, so it retires nothing and never requests evidence, even
        // when the only route would deny or panic.
        let (identity, normalize) = normalization();
        let untouched = initial
            .prepare_rewrite_with_evidence(&state, &identity, &normalize, |_, _| {
                panic!("identity rewrite demanded bytes")
            })
            .unwrap();
        assert!(untouched.retirements().is_empty());

        // Replacing A's only route changes its out-edge set, so `package` is
        // rechecked against the fresh edge under the same contract.
        let (production, request) = rule("replace", &initial, &replaced, &["A", "B"], &[]);
        let grammar = RewriteGrammar::new([production]).unwrap();
        let missing = initial.prepare_rewrite(&state, &grammar, &request, &BTreeMap::new());
        if matches!(contract, "other" | "unauthorized") {
            assert_eq!(
                missing.unwrap().retirements().get(&package),
                Some(&RetirementReason::NoAcceptingEdge)
            );
        } else {
            assert!(matches!(missing, Err(RewriteError::MissingEvidence(_))));
        }
        let result = initial.prepare_rewrite(&state, &grammar, &request, &evidence());
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
    let (remove, request) = rule("remove-b", &initial, &after, &["A"], &[]);
    let (recreate, recreate_request) = rule("recreate-b", &after, &initial, &["A"], &[]);
    let grammar = RewriteGrammar::new([remove, recreate]).unwrap();
    let mut state = initial.empty_state();
    let inbound = delivered(&initial, &mut state, "ab");
    let outbound_b = outbound(&initial, &mut state, "B");
    let prepared = initial
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
        .unwrap();
    assert_eq!(
        prepared.retirements(),
        BTreeMap::from([
            (inbound, RetirementReason::HolderRemoved),
            (outbound_b, RetirementReason::HolderRemoved),
        ])
    );
    let next = initial.commit_rewrite(&mut state, prepared).unwrap();
    assert!(matches!(
        next.prepare_rewrite(&state, &grammar, &recreate_request, &evidence()),
        Err(RewriteError::InvalidMatch(_))
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
fn dangling_context_and_changed_preserved_policy_are_rejected() {
    let initial = kernel(
        &["A", "B", "U"],
        &[("ab", "A", "B", "payload"), ("ub", "U", "B", "payload")],
    );
    let left = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let right = kernel(&["A"], &[]);
    let (remove, request) = rule("dangling", &left, &right, &["A"], &[]);
    let grammar = RewriteGrammar::new([remove]).unwrap();
    assert!(matches!(
        initial.prepare_rewrite(&initial.empty_state(), &grammar, &request, &evidence()),
        Err(RewriteError::InvalidMatch(_))
    ));

    let changed = RewriteFragment::new(
        right.graph().nodes().to_vec(),
        right.graph().edges().to_vec(),
        right.node_definitions().to_vec(),
        right.edge_definitions().to_vec(),
        right.authority_transitions().to_vec(),
        vec![],
    );
    let preserve = RewriteProduction::new(
        "policy",
        RewriteFragment::from_kernel(&right),
        names(&["A"]),
        names(&[]),
        changed,
    )
    .unwrap();
    let request = RewriteRequest::new(
        "policy",
        RewriteMatch::new(
            bindings(&["A"]),
            bindings(&[]),
            bindings(&[]),
            bindings(&[]),
        ),
    );
    let grammar = RewriteGrammar::new([preserve]).unwrap();
    assert!(matches!(
        right.prepare_rewrite(&right.empty_state(), &grammar, &request, &evidence()),
        Err(RewriteError::InvalidProduction(_))
    ));
}

#[test]
fn equal_revision_divergence_and_transfer_make_plans_stale_without_mutation() {
    let initial = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let mut state = initial.empty_state();
    let package = outbound(&initial, &mut state, "A");
    let (grammar, request) = normalization();
    let rewrite = initial
        .prepare_rewrite(&state, &grammar, &request, &evidence())
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
        .prepare_rewrite(&one, &grammar, &request, &evidence())
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
    let (production, request) = rule("disconnect", &initial, &right, &["A", "B"], &[]);
    let grammar = RewriteGrammar::new([production]).unwrap();
    let prepared = initial
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
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
    let (production, request) = rule("disconnect", &initial, &right, &["A", "B"], &[]);
    let grammar = RewriteGrammar::new([production]).unwrap();
    let prepared = initial
        .prepare_rewrite(&state, &grammar, &request, &BTreeMap::new())
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

    // local cleanup: an identity rewrite leaves A's out-edges unchanged, so the
    // unroutable package is neither rechecked nor retired, and no bytes are read.
    let (identity, normalize) = normalization();
    let untouched = initial
        .prepare_rewrite_with_evidence(&state, &identity, &normalize, |_, _| {
            panic!("unchanged holder demanded bytes")
        })
        .unwrap();
    assert!(untouched.retirements().is_empty());

    // Replacing both routes changes A's out-edge set; every fresh edge rejects
    // the package on type or authority metadata, so no bytes are requested.
    let (production, request) = rule("replace", &initial, &replaced, &["A", "B"], &[]);
    let grammar = RewriteGrammar::new([production]).unwrap();
    let prepared = initial
        .prepare_rewrite_with_evidence(&state, &grammar, &request, |_, _| {
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
        Err(TransferError::Rejected(_))
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
fn rule_symbols_match_injectively_and_fresh_allocations_are_not_survivor_assertions() {
    let initial = kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let left = kernel(&["X", "Y"], &[("xy", "X", "Y", "payload")]);
    let right = kernel(
        &["X", "Y", "Z"],
        &[("xz", "X", "Z", "payload"), ("zy", "Z", "Y", "payload")],
    );
    let production = RewriteProduction::new(
        "symbols",
        RewriteFragment::from_kernel(&left),
        names(&["X", "Y"]),
        names(&[]),
        RewriteFragment::from_kernel(&right),
    )
    .unwrap();
    let grammar = RewriteGrammar::new([production]).unwrap();
    let correct = RewriteMatch::new(
        BTreeMap::from([
            (Arc::from("X"), Arc::from("A")),
            (Arc::from("Y"), Arc::from("B")),
        ]),
        BTreeMap::from([(Arc::from("xy"), Arc::from("ab"))]),
        BTreeMap::from([(Arc::from("Z"), Arc::from("C"))]),
        BTreeMap::from([
            (Arc::from("xz"), Arc::from("ac")),
            (Arc::from("zy"), Arc::from("cb")),
        ]),
    );
    let state = initial.empty_state();
    let prepared = initial
        .prepare_rewrite(
            &state,
            &grammar,
            &RewriteRequest::new("symbols", correct.clone()),
            &BTreeMap::new(),
        )
        .unwrap();
    assert!(prepared.next_kernel().graph().node("C").is_some());
    assert!(prepared.next_kernel().graph().node("Z").is_none());
    for corrupt in ["missing", "noninjective", "reuse"] {
        let mut nodes = BTreeMap::from([
            (Arc::from("X"), Arc::from("A")),
            (Arc::from("Y"), Arc::from("B")),
        ]);
        let mut fresh_nodes = BTreeMap::from([(Arc::from("Z"), Arc::from("C"))]);
        match corrupt {
            "missing" => {
                nodes.remove("Y");
            }
            "noninjective" => {
                nodes.insert(Arc::from("Y"), Arc::from("A"));
            }
            _ => {
                fresh_nodes.insert(Arc::from("Z"), Arc::from("B"));
            }
        }
        let matching = RewriteMatch::new(
            nodes,
            BTreeMap::from([(Arc::from("xy"), Arc::from("ab"))]),
            fresh_nodes,
            BTreeMap::from([
                (Arc::from("xz"), Arc::from("ac")),
                (Arc::from("zy"), Arc::from("cb")),
            ]),
        );
        assert!(matches!(
            initial.prepare_rewrite(
                &state,
                &grammar,
                &RewriteRequest::new("symbols", matching),
                &BTreeMap::new()
            ),
            Err(RewriteError::InvalidMatch(_))
        ));
    }
    assert!(matches!(
        initial.prepare_rewrite(
            &state,
            &RewriteGrammar::default(),
            &RewriteRequest::new("symbols", correct),
            &BTreeMap::new()
        ),
        Err(RewriteError::UnknownProduction(_))
    ));
}
