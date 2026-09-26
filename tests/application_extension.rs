//! Reconstructing executable applications after a durable vocabulary extension.

use ontography::{
    ApplicationBuilder, ApplicationContext, ApplicationRunMode, Authority, Contract, Kernel,
    NodeComponent, NodeConfig, RewriteFragment, RewriteGrammar, RewriteMatch, RewriteProduction,
    RewriteRequest, Schema,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::{Arc, Mutex},
};

#[tokio::test]
async fn extended_application_resumes_bindings_and_grammar_without_replaying_input() {
    let launches = Arc::new(Mutex::new(Vec::new()));
    let observed = launches.clone();
    let result = Contract::new("result", "Result", |_| Ok(())).unwrap();
    let mut builder = ApplicationBuilder::new("extended-application").unwrap();
    builder
        .entry(
            "entry",
            NodeComponent::new(
                NodeConfig::new(["Node"], result).unwrap(),
                move |context: ApplicationContext| {
                    let observed = observed.clone();
                    async move {
                        observed
                            .lock()
                            .unwrap()
                            .push((context.run_mode(), context.initial_input().cloned()));
                        Ok(())
                    }
                },
            )
            .with_root_authority(Authority::new([])),
        )
        .unwrap();
    let application = builder.build().unwrap();
    let base = application.kernel();
    let fragment = RewriteFragment::from_kernel(base);
    let grammar = RewriteGrammar::new([RewriteProduction::new(
        "identity",
        fragment.clone(),
        BTreeSet::from([Arc::from("entry")]),
        BTreeSet::new(),
        fragment,
    )
    .unwrap()])
    .unwrap();
    let schema = Schema::new(
        base.schema().node_types().chain(["Worker"]),
        base.schema().object_types().chain(["Note"]),
        base.schema().authority_tags().cloned(),
    )
    .unwrap();
    let mut contracts = base.contracts().to_vec();
    contracts.push(Contract::new("note", "Note", |_| Ok(())).unwrap());
    let extended = Arc::new(
        Kernel::admit(
            base.id().clone(),
            schema,
            base.graph().clone(),
            contracts,
            base.node_definitions().to_vec(),
            base.edge_definitions().to_vec(),
            base.authority_transitions().to_vec(),
            base.roots().to_vec(),
        )
        .unwrap(),
    );
    let base_fingerprint = *base.fingerprint();
    let application = application.with_grammar(grammar);
    let directory = tempfile::tempdir().unwrap();
    let run = application
        .start_in(directory.path(), Arc::from(&b"once"[..]))
        .await
        .unwrap();
    run.wait_idle().await;
    let rebuilt = application
        .with_vocabulary_extension(extended.clone())
        .unwrap();
    assert_eq!(
        *run.snapshot().await.kernel().fingerprint(),
        base_fingerprint
    );
    run.session()
        .extend(extended.clone())
        .await
        .unwrap()
        .unwrap();
    let path = run.suspend().await.unwrap();
    let resumed = rebuilt.resume(path).await.unwrap();
    resumed.wait_idle().await;
    assert_eq!(resumed.executions().len(), 1);
    assert_eq!(
        resumed.snapshot().await.kernel().fingerprint(),
        extended.fingerprint()
    );
    let request = RewriteRequest::new(
        "identity",
        RewriteMatch::new(
            BTreeMap::from([(Arc::from("entry"), Arc::from("entry"))]),
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeMap::new(),
        ),
    );
    let plan = resumed
        .session()
        .prepare_rewrite(&request)
        .await
        .unwrap()
        .unwrap();
    resumed
        .session()
        .commit_rewrite(plan)
        .await
        .unwrap()
        .unwrap();
    {
        let observed = launches.lock().unwrap();
        assert_eq!(observed.len(), 2);
        assert_eq!(observed[0].0, ApplicationRunMode::Fresh);
        assert_eq!(observed[0].1.as_deref(), Some(&b"once"[..]));
        assert_eq!(observed[1].0, ApplicationRunMode::Resume);
        assert!(observed[1].1.is_none());
    }
    resumed.shutdown().await;
}
