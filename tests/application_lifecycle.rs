//! Run lifecycle at the application boundary: starts that fail after the run
//! exists, and resumes of runs whose graph a rewrite changed.

use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use ontography::{
    Application, ApplicationBuilder, ApplicationContext, ApplicationRunMode, ApplicationStartError,
    Authority, Contract, Graph, GraphEdit, GraphFragment, Kernel, Node, NodeComponent, NodeConfig,
    NodeDefinition, Payload, PermitAll, Principal, RewriteRequest, SessionStatus,
};

type Launches = Arc<Mutex<Vec<(String, ApplicationRunMode)>>>;

fn payload() -> Payload {
    Arc::from(&b"input"[..])
}

fn result_contract() -> Contract {
    Contract::new("result", "Result", |_| Ok(())).unwrap()
}

fn component(contract: &Contract, launches: &Launches) -> NodeComponent {
    let launches = Arc::clone(launches);
    NodeComponent::new(
        NodeConfig::new(["Node"], contract.clone()).unwrap(),
        move |context: ApplicationContext| {
            let launches = Arc::clone(&launches);
            async move {
                launches
                    .lock()
                    .unwrap()
                    .push((context.node_id().to_owned(), context.run_mode()));
                Ok(())
            }
        },
    )
}

fn application(id: &str, nodes: &[&str], launches: &Launches) -> Application {
    let contract = result_contract();
    let mut builder = ApplicationBuilder::new(id).unwrap();
    builder
        .entry(
            "entry",
            component(&contract, launches).with_root_authority(Authority::new([])),
        )
        .unwrap();
    for node in nodes {
        builder.node(*node, component(&contract, launches)).unwrap();
    }
    builder.build().unwrap()
}

/// The application's vocabulary over a different node set, for rewrite fragments.
fn kernel_with(base: &Kernel, nodes: &[&str]) -> Kernel {
    Kernel::admit(
        base.id().clone(),
        base.schema().clone(),
        Graph::new(nodes.iter().map(|id| Node::new(*id).unwrap()), []).unwrap(),
        base.contracts().to_vec(),
        nodes
            .iter()
            .map(|id| NodeDefinition::new(*id, ["Node"], "result").unwrap()),
        [],
        [],
        base.roots().to_vec(),
    )
    .unwrap()
}

#[tokio::test]
async fn start_failure_after_run_creation_closes_the_run() {
    let launches = Launches::default();
    let contract = result_contract();
    let mut builder = ApplicationBuilder::new("unstartable").unwrap();
    builder
        .entry(
            "entry",
            component(&contract, &launches).with_root_authority(Authority::new([])),
        )
        .unwrap();
    // The node state directory name is the hex of the node id, so this id
    // exceeds NAME_MAX and node state preparation fails after the persistent
    // session already exists.
    builder
        .node("n".repeat(200), component(&contract, &launches))
        .unwrap();
    let application = builder.build().unwrap();
    let directory = tempfile::tempdir().unwrap();

    let error = application
        .start_in(directory.path(), payload())
        .await
        .unwrap_err();
    assert!(
        matches!(error, ApplicationStartError::StateDirectory { .. }),
        "{error}"
    );
    assert!(launches.lock().unwrap().is_empty());

    let runs = std::fs::read_dir(directory.path().join("runs"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();
    assert_eq!(runs.len(), 1);
    let error = application.resume(&runs[0]).await.unwrap_err();
    assert!(
        matches!(
            error,
            ApplicationStartError::NotResumable(SessionStatus::Closed)
        ),
        "{error}"
    );
}

#[tokio::test]
async fn resume_fails_closed_on_binding_drift_unless_partial_resume_is_requested() {
    let launches = Launches::default();
    let application = application("drifting", &["worker"], &launches);
    let base = application.kernel();
    let with_extra = kernel_with(base, &["entry", "extra"]);
    let drop_worker = GraphEdit::new(
        BTreeSet::from([Arc::from("worker")]),
        base.graph()
            .edges()
            .iter()
            .map(|edge| Arc::from(edge.id()))
            .collect(),
        GraphFragment::default(),
    );
    let add_extra = GraphEdit::new(
        BTreeSet::new(),
        BTreeSet::new(),
        GraphFragment::new(
            vec![Node::new("extra").unwrap()],
            vec![],
            vec![with_extra.node_definition("extra").unwrap().clone()],
            vec![],
            vec![],
            vec![],
        ),
    );
    let application = application.with_policy(Arc::new(PermitAll));
    let directory = tempfile::tempdir().unwrap();
    let run = application
        .start_in(directory.path(), payload())
        .await
        .unwrap();
    run.wait_idle().await;
    assert_eq!(run.executions().len(), 2);

    for edit in [drop_worker, add_extra] {
        let request = RewriteRequest::new(Principal::new("operator"), edit);
        let plan = run
            .session()
            .prepare_rewrite(&request)
            .await
            .unwrap()
            .unwrap();
        run.session().commit_rewrite(plan).await.unwrap().unwrap();
    }
    let path = run.suspend().await.unwrap();
    let worker_state = path.join("nodes").join("node-776f726b6572");
    assert!(worker_state.is_dir());

    let error = application.resume(&path).await.unwrap_err();
    match error {
        ApplicationStartError::BindingDrift { removed, unbound } => {
            assert_eq!(removed, vec![Arc::<str>::from("worker")]);
            assert_eq!(unbound, vec![Arc::<str>::from("extra")]);
        }
        other => panic!("expected binding drift, got {other}"),
    }

    // The failed strict resume released the run without closing it, and the
    // partial resume neither launches nor prepares state for removed nodes.
    std::fs::remove_dir_all(&worker_state).unwrap();
    let resumed = application.resume_partial(&path).await.unwrap();
    resumed.wait_idle().await;
    assert_eq!(resumed.executions().len(), 1);
    assert_eq!(resumed.executions()[0].node_id(), "entry");
    assert!(!worker_state.exists());
    assert!(path.join("nodes").join("node-656e747279").is_dir());
    assert_eq!(
        launches.lock().unwrap().last(),
        Some(&("entry".to_owned(), ApplicationRunMode::PartialResume))
    );
    resumed.shutdown().await;
}
