//! The graph-edit rule: what an edit may remove and add, what the kernel
//! admits, and how the policy decides after it.

#[allow(dead_code)]
mod support;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use ontography::{
    Authority, AuthorityTransitionRule, DenyAll, Edge, EdgeDefinition, EditContext, EditPolicy,
    GraphEdit, GraphFragment, Kernel, Node, NodeDefinition, Phase, PolicyDenial, PreparedRewrite,
    Principal, RetirementReason, RewriteError, RewriteRequest, RootRule, State,
};
use support::{authority, delivered, evidence, kernel, names, outbound, tag};

fn edit(remove_nodes: &[&str], remove_edges: &[&str], add: GraphFragment) -> GraphEdit {
    GraphEdit::new(names(remove_nodes), names(remove_edges), add)
}

fn node(id: &str) -> Node {
    Node::new(id).unwrap()
}

fn node_definition(id: &str) -> NodeDefinition {
    NodeDefinition::new(id, ["n"], "result").unwrap()
}

fn edge(id: &str, source: &str, target: &str) -> Edge {
    Edge::new(id, source, target).unwrap()
}

fn edge_definition(id: &str) -> EdgeDefinition {
    EdgeDefinition::new(id, ["flow"], ["n"], ["n"], "payload", [tag("run")]).unwrap()
}

/// Defined nodes and edges, with nothing else.
fn fragment(nodes: &[&str], edges: &[(&str, &str, &str)]) -> GraphFragment {
    GraphFragment::new(
        nodes.iter().map(|id| node(id)).collect(),
        edges
            .iter()
            .map(|(id, source, target)| edge(id, source, target))
            .collect(),
        nodes.iter().map(|id| node_definition(id)).collect(),
        edges.iter().map(|(id, _, _)| edge_definition(id)).collect(),
        vec![],
        vec![],
    )
}

fn prepare_as(
    kernel: &Kernel,
    state: &State,
    policy: &dyn EditPolicy,
    principal: &str,
    edit: GraphEdit,
) -> Result<PreparedRewrite, RewriteError> {
    kernel.prepare_rewrite(
        state,
        policy,
        &RewriteRequest::new(Principal::new(principal), edit),
        &evidence(),
    )
}

fn prepare(
    kernel: &Kernel,
    state: &State,
    edit: GraphEdit,
) -> Result<PreparedRewrite, RewriteError> {
    prepare_as(kernel, state, &ontography::PermitAll, "test", edit)
}

fn apply(kernel: &Kernel, state: &mut State, edit: GraphEdit) -> Arc<Kernel> {
    let prepared = prepare(kernel, state, edit).unwrap();
    kernel.commit_rewrite(state, prepared).unwrap()
}

fn invalid(result: Result<PreparedRewrite, RewriteError>) -> String {
    match result {
        Err(RewriteError::InvalidEdit(message)) => message.to_string(),
        other => panic!("expected an invalid edit, got {other:?}"),
    }
}

fn chain() -> Kernel {
    kernel(
        &["a", "b", "c"],
        &[("ab", "a", "b", "payload"), ("bc", "b", "c", "payload")],
    )
}

#[test]
fn removing_a_node_takes_its_edges_and_retires_what_it_held() {
    let initial = chain();
    let mut state = initial.empty_state();
    let held = delivered(&initial, &mut state, "ab");
    let revision = state.revision();

    let prepared = prepare(
        &initial,
        &state,
        edit(&["b"], &["ab", "bc"], GraphFragment::default()),
    )
    .unwrap();
    assert_eq!(
        prepared.retirements(),
        BTreeMap::from([(held, RetirementReason::HolderRemoved)])
    );
    let current = initial.commit_rewrite(&mut state, prepared).unwrap();

    assert!(current.graph().node("b").is_none());
    assert!(current.graph().edges().is_empty());
    assert!(current.node_definition("b").is_none());
    assert!(current.root_ceiling("b").is_none());
    assert_eq!(state.revision(), revision + 1);
    assert!(!state.package(held).unwrap().is_live());
}

#[test]
fn every_removed_element_must_exist() {
    let initial = chain();
    let state = initial.empty_state();
    assert!(
        invalid(prepare(
            &initial,
            &state,
            edit(&["z"], &[], GraphFragment::default())
        ))
        .contains('z')
    );
    assert!(
        invalid(prepare(
            &initial,
            &state,
            edit(&[], &["zz"], GraphFragment::default())
        ))
        .contains("zz")
    );
}

#[test]
fn an_edge_touching_a_removed_node_must_be_removed_with_it() {
    let initial = chain();
    let state = initial.empty_state();
    let message = invalid(prepare(
        &initial,
        &state,
        edit(&["b"], &["ab"], GraphFragment::default()),
    ));
    assert!(message.contains("bc"), "{message}");
}

#[test]
fn added_elements_connect_to_survivors_and_carry_their_own_policies() {
    let initial = chain();
    let mut state = initial.empty_state();
    let mut add = fragment(&["d"], &[("cd", "c", "d"), ("da", "d", "a")]);
    let transition =
        AuthorityTransitionRule::new("d", authority(), Authority::new([tag("other")])).unwrap();
    add = GraphFragment::new(
        add.nodes().to_vec(),
        add.edges().to_vec(),
        add.node_definitions().to_vec(),
        add.edge_definitions().to_vec(),
        vec![transition.clone()],
        vec![RootRule::new("d", authority()).unwrap()],
    );

    let current = apply(&initial, &mut state, edit(&[], &[], add));

    assert_eq!(current.node_definition("d"), Some(&node_definition("d")));
    assert_eq!(current.root_ceiling("d"), Some(&authority()));
    assert!(current.authority_transitions().contains(&transition));
    assert_eq!(current.graph().edge("cd").unwrap().source(), "c");
    assert_eq!(current.edge_definition("da"), Some(&edge_definition("da")));
    assert!(state.used_node_ids().contains("d"));
    assert!(state.used_edge_ids().contains("cd"));
    // Survivors are untouched.
    assert_eq!(current.node_definition("a"), initial.node_definition("a"));
    assert_eq!(current.edge_definition("ab"), initial.edge_definition("ab"));
}

#[test]
fn identities_are_never_reused_even_after_removal() {
    let initial = chain();
    let mut state = initial.empty_state();
    assert!(
        invalid(prepare(
            &initial,
            &state,
            edit(&[], &[], fragment(&["a"], &[]))
        ))
        .contains("reuses")
    );
    assert!(
        invalid(prepare(
            &initial,
            &state,
            edit(&[], &[], fragment(&[], &[("ab", "a", "b")]))
        ))
        .contains("reuses")
    );

    let current = apply(
        &initial,
        &mut state,
        edit(&["c"], &["bc"], GraphFragment::default()),
    );
    assert!(
        invalid(prepare(
            &current,
            &state,
            edit(&[], &[], fragment(&["c"], &[]))
        ))
        .contains("reuses")
    );
    assert!(
        invalid(prepare(
            &current,
            &state,
            edit(&[], &[], fragment(&[], &[("bc", "b", "a")]))
        ))
        .contains("reuses")
    );
}

#[test]
fn only_added_elements_may_be_annotated() {
    let initial = chain();
    let state = initial.empty_state();
    let annotate = |node_definitions, edge_definitions, transitions, roots| {
        edit(
            &[],
            &[],
            GraphFragment::new(
                vec![],
                vec![],
                node_definitions,
                edge_definitions,
                transitions,
                roots,
            ),
        )
    };
    let survivor_rule =
        AuthorityTransitionRule::new("a", authority(), Authority::new([tag("other")])).unwrap();
    for survivor_annotation in [
        annotate(vec![node_definition("a")], vec![], vec![], vec![]),
        annotate(vec![], vec![edge_definition("ab")], vec![], vec![]),
        annotate(vec![], vec![], vec![survivor_rule], vec![]),
        annotate(
            vec![],
            vec![],
            vec![],
            vec![RootRule::new("a", authority()).unwrap()],
        ),
    ] {
        let message = invalid(prepare(&initial, &state, survivor_annotation));
        assert!(message.contains("not added"), "{message}");
    }
}

#[test]
fn the_edited_definition_must_be_admitted() {
    let initial = chain();
    let state = initial.empty_state();
    let undefined = GraphFragment::new(vec![node("d")], vec![], vec![], vec![], vec![], vec![]);
    let to_removed = fragment(&[], &[("ac", "a", "c")]);
    for inadmissible in [edit(&[], &[], undefined), edit(&["c"], &["bc"], to_removed)] {
        assert!(matches!(
            prepare(&initial, &state, inadmissible),
            Err(RewriteError::Definition(_))
        ));
    }
}

#[test]
fn one_edit_replaces_a_route_without_retiring_the_work_waiting_for_it() {
    let initial = kernel(&["a", "b"], &[("ab", "a", "b", "payload")]);
    let mut state = initial.empty_state();
    let waiting = outbound(&initial, &mut state, "a");

    // Removing the only route on its own would strand the package.
    let removal = prepare(
        &initial,
        &state,
        edit(&[], &["ab"], GraphFragment::default()),
    )
    .unwrap();
    assert_eq!(
        removal.retirements(),
        BTreeMap::from([(waiting, RetirementReason::NoAcceptingEdge)])
    );

    // Replacing it in one edit keeps the package, because cleanup sees only
    // the final graph.
    let replacement = edit(&[], &["ab"], fragment(&[], &[("ab2", "a", "b")]));
    let prepared = prepare(&initial, &state, replacement).unwrap();
    assert!(prepared.retirements().is_empty());
    let current = initial.commit_rewrite(&mut state, prepared).unwrap();
    let record = state.package(waiting).unwrap();
    assert!(record.is_live());
    assert_eq!(record.phase(), Phase::Out);
    assert!(current.graph().edge("ab2").is_some());
}

#[test]
fn the_empty_edit_only_advances_the_revision() {
    let initial = chain();
    let mut state = initial.empty_state();
    let package = outbound(&initial, &mut state, "a");
    let revision = state.revision();

    let current = apply(&initial, &mut state, GraphEdit::default());

    assert_eq!(current.fingerprint(), initial.fingerprint());
    assert_eq!(state.revision(), revision + 1);
    assert!(state.package(package).unwrap().is_live());
}

#[test]
fn the_policy_decides_last_and_sees_the_admitted_result() {
    let initial = chain();
    let mut state = initial.empty_state();
    let held = delivered(&initial, &mut state, "ab");
    let seen = Mutex::new(None);
    let observer = |context: &EditContext<'_>| {
        *seen.lock().unwrap() = Some((
            context.principal.name().to_owned(),
            context.before.graph().node("b").is_some(),
            context.after.graph().node("b").is_some(),
            context.edit.remove_nodes().clone(),
            context.retirements.clone(),
        ));
        Ok(())
    };

    prepare_as(
        &initial,
        &state,
        &observer,
        "manager",
        edit(&["b"], &["ab", "bc"], GraphFragment::default()),
    )
    .unwrap();

    assert_eq!(
        seen.into_inner().unwrap(),
        Some((
            "manager".to_owned(),
            true,
            false,
            names(&["b"]),
            BTreeMap::from([(held, RetirementReason::HolderRemoved)]),
        ))
    );
}

#[test]
fn a_denial_rejects_the_edit() {
    let initial = chain();
    let state = initial.empty_state();
    let only_the_manager = |context: &EditContext<'_>| {
        if context.principal.name() == "manager" {
            Ok(())
        } else {
            Err(PolicyDenial::new(format!(
                "{} may not edit",
                context.principal
            )))
        }
    };

    assert!(
        prepare_as(
            &initial,
            &state,
            &only_the_manager,
            "manager",
            GraphEdit::default()
        )
        .is_ok()
    );
    assert_eq!(
        prepare_as(
            &initial,
            &state,
            &only_the_manager,
            "agent",
            GraphEdit::default()
        )
        .unwrap_err(),
        RewriteError::Denied(Arc::from("agent may not edit"))
    );
    assert!(matches!(
        prepare_as(&initial, &state, &DenyAll, "manager", GraphEdit::default()),
        Err(RewriteError::Denied(_))
    ));
}

#[test]
fn a_panicking_policy_rejects_the_edit() {
    let initial = chain();
    let state = initial.empty_state();
    let faulty = |_: &EditContext<'_>| -> Result<(), PolicyDenial> { panic!("policy fault") };
    assert_eq!(
        prepare_as(&initial, &state, &faulty, "manager", GraphEdit::default()).unwrap_err(),
        RewriteError::PolicyPanicked
    );
}

#[test]
fn structural_errors_are_reported_before_the_policy_runs() {
    let initial = chain();
    let state = initial.empty_state();
    let calls = AtomicUsize::new(0);
    let counting = |_: &EditContext<'_>| {
        calls.fetch_add(1, Ordering::Relaxed);
        Ok(())
    };
    let dangling = edit(&["b"], &["ab"], GraphFragment::default());
    assert!(matches!(
        prepare_as(&initial, &state, &counting, "manager", dangling),
        Err(RewriteError::InvalidEdit(_))
    ));
    assert_eq!(calls.load(Ordering::Relaxed), 0);
}
