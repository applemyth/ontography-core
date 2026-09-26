//! Observable behavior at the application-to-kernel boundary.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use ontography::project::ProjectConfig;
use ontography::{
    ActivationProposal, ApplicationBuilder, ApplicationConfig, ApplicationContext, Authority,
    ContextError, Contract, DefinitionId, ExecutionFailure, ExecutionStatus, Graph,
    InvocationTrigger, Kernel, Node, NodeComponent, NodeConfig, NodeDefinition, Payload,
    ProposalDecision, ProposalRuntime, RewriteError, RewriteFragment, RewriteGrammar, RewriteMatch,
    RewriteProduction, RewriteRequest, RootRule, Schema, SessionTransitionError, Trigger,
};

fn payload(value: &'static [u8]) -> Payload {
    Arc::from(value)
}

fn result_contract() -> Contract {
    Contract::new("result", "Result", |_| Ok(())).unwrap()
}

fn idle_component(contract: Contract) -> NodeComponent {
    NodeComponent::new(NodeConfig::new(["Node"], contract).unwrap(), |_| async {
        Ok(())
    })
}

#[tokio::test]
async fn starting_an_application_does_not_automatically_create_a_root_activation() {
    let mut builder = ApplicationBuilder::new("idle-entry").unwrap();
    builder
        .entry(
            "entry",
            idle_component(result_contract()).with_root_authority(Authority::new([])),
        )
        .unwrap();
    let run = builder
        .build()
        .unwrap()
        .start_ephemeral(payload(b"input"))
        .await
        .unwrap();
    run.wait_idle().await;
    assert!(run.snapshot().await.state().activations().is_empty());
    run.shutdown().await;
}

#[tokio::test]
async fn raw_component_submission_can_root_another_node_while_bound_invocation_cannot() {
    let result = result_contract();
    let mut builder = ApplicationBuilder::new("cross-node-root").unwrap();
    builder
        .entry(
            "entry",
            idle_component(result.clone()).with_root_authority(Authority::new([])),
        )
        .unwrap();
    let worker = NodeComponent::new(
        NodeConfig::new(["Node"], result).unwrap(),
        |context: ApplicationContext| async move {
            assert_eq!(context.node_id(), "worker");
            let bound = context
                .begin_invocation(InvocationTrigger::Root {
                    authority: Authority::new([]),
                    input: payload(b"input"),
                })
                .await;
            if !matches!(bound, Err(ContextError::Denied(_))) {
                return Err(ExecutionFailure::new(
                    "scope",
                    "non-root worker acquired a root-bound invocation",
                ));
            }
            let proposal =
                ActivationProposal::root("entry", Authority::new([]), payload(b"result"));
            match context.submit(proposal).await {
                Ok(ProposalDecision::Committed(_)) => Ok(()),
                Ok(ProposalDecision::Rejected(error)) => {
                    Err(ExecutionFailure::new("admission", error.to_string()))
                }
                Err(error) => Err(ExecutionFailure::new("submission", error.to_string())),
            }
        },
    );
    builder.node("worker", worker).unwrap();
    let run = builder
        .build()
        .unwrap()
        .start_ephemeral(payload(b"entry input"))
        .await
        .unwrap();
    run.wait_idle().await;
    assert!(
        run.executions()
            .iter()
            .all(|handle| handle.status() == ExecutionStatus::Exited)
    );
    let snapshot = run.snapshot().await;
    assert_eq!(snapshot.state().activations().len(), 1);
    let activation = snapshot.state().activations().values().next().unwrap();
    assert!(matches!(
        activation.trigger(),
        Trigger::Orig { node_id, .. } if node_id.as_ref() == "entry"
    ));
    run.shutdown().await;
}

#[test]
fn both_declarative_formats_reject_duplicate_keys_inside_opaque_configuration() {
    let native = r#"{
        "id":"native", "entry":"a",
        "node_definitions":{"n":{
            "types":["Node"], "result_contract":"result",
            "implementation":{"kind":"test","config":{"sandbox":"read","sandbox":"write"}}
        }},
        "edge_definitions":{}, "nodes":{"a":{"definition":"n"}}, "edges":{}
    }"#;
    let error = ApplicationConfig::from_json(native).unwrap_err();
    assert!(error.to_string().contains("duplicate JSON key \"sandbox\""));

    let project = r#"{
        "id":"project", "entry":"a",
        "components":{"c":{"provider":"test","config":{"sandbox":"read","sandbox":"write"}}},
        "nodes":{}, "connections":[]
    }"#;
    let error = ProjectConfig::from_json(project).unwrap_err();
    assert!(error.to_string().contains("duplicate JSON key \"sandbox\""));
}

#[tokio::test]
async fn direct_rewrite_grammar_is_caller_supplied_but_runtime_grammar_is_sealed() {
    let kernel = Arc::new(
        Kernel::admit(
            DefinitionId::new("grammar-boundary").unwrap(),
            Schema::new(["Node"], ["Result"], []).unwrap(),
            Graph::new([Node::new("entry").unwrap()], []).unwrap(),
            [result_contract()],
            [NodeDefinition::new("entry", ["Node"], "result").unwrap()],
            [],
            [],
            [RootRule::new("entry", Authority::new([])).unwrap()],
        )
        .unwrap(),
    );
    let fragment = RewriteFragment::from_kernel(&kernel);
    let production = RewriteProduction::new(
        "identity",
        fragment.clone(),
        BTreeSet::from([Arc::from("entry")]),
        BTreeSet::new(),
        fragment,
    )
    .unwrap();
    let grammar = RewriteGrammar::new([production]).unwrap();
    let request = RewriteRequest::new(
        "identity",
        RewriteMatch::new(
            BTreeMap::from([(Arc::from("entry"), Arc::from("entry"))]),
            BTreeMap::new(),
            BTreeMap::new(),
            BTreeMap::new(),
        ),
    );

    assert!(
        kernel
            .prepare_rewrite(&kernel.empty_state(), &grammar, &request, &BTreeMap::new())
            .is_ok()
    );

    let unconfigured = ProposalRuntime::new(Arc::clone(&kernel));
    let session = unconfigured.open().unwrap();
    assert!(matches!(
        session.prepare_rewrite(&request).await,
        Err(SessionTransitionError::Rewrite(
            RewriteError::UnknownProduction(_)
        ))
    ));

    let configured = ProposalRuntime::with_grammar(kernel, grammar);
    let session = configured.open().unwrap();
    assert!(session.prepare_rewrite(&request).await.is_ok());
}
