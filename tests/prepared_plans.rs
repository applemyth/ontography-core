//! Every direct prepare/commit pair fences its predecessor before admission,
//! and every evaluator refuses a state whose revision cannot advance.
use ontography::{
    ActivationProposal, ExtensionError, Kernel, PermitAll, Reject, RetireError, RewriteError,
    Schema, TransferError,
};
use std::sync::Arc;
#[allow(dead_code)]
mod support;

fn extended(k: &Kernel) -> Arc<Kernel> {
    Arc::new(
        Kernel::admit(
            k.id().clone(),
            Schema::new(
                k.schema().node_types().chain(["added"]),
                k.schema().object_types(),
                k.schema().authority_tags().cloned(),
            )
            .unwrap(),
            k.graph().clone(),
            k.contracts().iter().cloned(),
            k.node_definitions().to_vec(),
            k.edge_definitions().to_vec(),
            k.authority_transitions().to_vec(),
            k.roots().to_vec(),
        )
        .unwrap(),
    )
}

#[test]
fn definition_changes_make_every_prepared_operation_stale() {
    let k = support::kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let next = support::kernel(&["A", "B"], &[]);
    let remove = support::request(support::replace(&k, &next, &["A", "B"], &[]));
    let mut state = k.empty_state();
    let package = support::outbound(&k, &mut state, "A");
    let rewrite = k
        .prepare_rewrite(&state, &PermitAll, &remove, &support::evidence())
        .unwrap();
    let transfer = k
        .prepare_transfer(&state, package, "ab", &support::payload())
        .unwrap();
    let extension = k.prepare_extension(&state, extended(&k)).unwrap();
    let current = k.commit_extension(&mut state, extension.clone()).unwrap();
    let before = state.clone();
    assert!(matches!(
        current.commit_rewrite(&mut state, rewrite),
        Err(RewriteError::Stale)
    ));
    assert!(matches!(
        current.commit_extension(&mut state, extension),
        Err(ExtensionError::Stale)
    ));
    assert!(matches!(
        current.commit_transfer(&mut state, transfer),
        Err(TransferError::Admission(RewriteError::Stale))
    ));
    assert_eq!(state, before);
}

/// Checkpoint restoration accepts any revision whose accounting is exact, so a
/// trusted store can hand back a state at `u64::MAX`. Every evaluator rejects
/// it before building a transition, and the state is unchanged.
#[test]
fn an_exhausted_revision_rejects_every_transition_kind() {
    let k = support::kernel(&["A", "B"], &[("ab", "A", "B", "payload")]);
    let identity = support::normalization();
    let mut state = k.empty_state();
    let package = support::outbound(&k, &mut state, "A");
    let mut checkpoint = state.checkpoint();
    checkpoint.definition_changes = u64::MAX - 1;
    checkpoint.revision = u64::MAX;
    let mut state = k.restore_checkpoint(checkpoint).unwrap();
    assert_eq!(state.revision(), u64::MAX);
    let before = state.clone();

    let root = ActivationProposal::root("A", support::authority(), support::payload());
    assert_eq!(k.activate(&mut state, root), Err(Reject::RevisionExhausted));
    assert!(matches!(
        k.prepare_transfer(&state, package, "ab", &support::payload()),
        Err(TransferError::Admission(RewriteError::RevisionExhausted))
    ));
    assert!(matches!(
        k.retire(&mut state, package, None),
        Err(RetireError::Admission(RewriteError::RevisionExhausted))
    ));
    assert!(matches!(
        k.prepare_rewrite(&state, &PermitAll, &identity, &support::evidence()),
        Err(RewriteError::RevisionExhausted)
    ));
    assert!(matches!(
        k.prepare_extension(&state, extended(&k)),
        Err(ExtensionError::Admission(RewriteError::RevisionExhausted))
    ));
    assert_eq!(state, before);
}

#[test]
fn rewrite_cannot_replace_validators_with_a_matching_fingerprint() {
    let k = support::kernel(&["A"], &[]);
    let foreign = support::kernel(&["A"], &[]);
    assert_eq!(k.fingerprint(), foreign.fingerprint());
    let mut state = k.empty_state();
    let plan = foreign
        .prepare_rewrite(
            &state,
            &PermitAll,
            &support::normalization(),
            &support::evidence(),
        )
        .unwrap();
    let before = state.clone();
    assert!(matches!(
        k.commit_rewrite(&mut state, plan),
        Err(RewriteError::ContractChanged(_))
    ));
    assert_eq!(state, before);
}

#[test]
fn checkpoint_keeps_definition_changes_and_unique_explicit_retirements() {
    let k = support::kernel(&["A"], &[]);
    let mut state = k.empty_state();
    let extension = k.prepare_extension(&state, extended(&k)).unwrap();
    let current = k.commit_extension(&mut state, extension).unwrap();
    assert_eq!(state.definition_changes(), 1);
    let mut checkpoint = state.checkpoint();
    checkpoint.revision = 0;
    assert!(matches!(
        current.restore_checkpoint(checkpoint),
        Err(ontography::CheckpointError::Revision(_))
    ));
    let p = support::outbound(&current, &mut state, "A");
    let q = support::outbound(&current, &mut state, "A");
    current.retire(&mut state, p, None).unwrap();
    current.retire(&mut state, q, None).unwrap();
    let mut checkpoint = state.checkpoint();
    let record = checkpoint.packages[&q].clone();
    let retirement = checkpoint.packages[&p].retirement().unwrap().clone();
    checkpoint.packages.insert(
        q,
        ontography::PackageRecord::new(
            record.object_type(),
            record.authority().clone(),
            record.content_digest(),
            record.producer_node(),
            record.delivery().cloned(),
            ontography::PackageStatus::Retired(retirement),
        ),
    );
    assert!(matches!(
        current.restore_checkpoint(checkpoint),
        Err(ontography::CheckpointError::Retirement(_))
    ));
    let restored = current.restore_checkpoint(state.checkpoint()).unwrap();
    assert_eq!(restored, state);
    assert!(restored.to_parts().is_err());
}
