//! Exercise content-package reuse through an actual workflow output.

use std::{collections::BTreeMap, sync::Arc};

use ontography::{
    ActivationProposal, Authority, AuthorityTag, Contract, DefinitionId, Edge, EdgeDefinition,
    Emission, Graph, Kernel, Node, NodeDefinition, OutputAuthority, PackageDocument,
    PackageEnvelope, PackageId, PackageStore, ProposalDecision, ProposalRuntime, RootRule, Schema,
};

#[tokio::test]
async fn changes_package_reuses_prior_content_and_emits_only_its_envelope() {
    let route = AuthorityTag::new("route").unwrap();
    let kernel = Kernel::admit(
        DefinitionId::new("content-composition-probe").unwrap(),
        Schema::new(["Node"], ["Result", "Artifact"], [route.clone()]).unwrap(),
        Graph::new(
            [
                Node::new("producer").unwrap(),
                Node::new("consumer").unwrap(),
            ],
            [Edge::new("flow", "producer", "consumer").unwrap()],
        )
        .unwrap(),
        [
            Contract::new("result", "Result", |_| Ok(())).unwrap(),
            Contract::new("artifact", "Artifact", |_| Ok(())).unwrap(),
        ],
        [
            NodeDefinition::new("producer", ["Node"], "result").unwrap(),
            NodeDefinition::new("consumer", ["Node"], "result").unwrap(),
        ],
        [EdgeDefinition::new(
            "flow",
            ["Flow"],
            ["Node"],
            ["Node"],
            "artifact",
            [route.clone()],
        )
        .unwrap()],
        [],
        [RootRule::new("producer", Authority::new([route.clone()])).unwrap()],
    )
    .unwrap();
    let session = ProposalRuntime::new(Arc::new(kernel)).open().unwrap();
    let content = session.content_store().await.unwrap();
    let packages = PackageStore::new(content.clone());
    let mut files = Vec::new();
    for bytes in [vec![b'x'; 64 * 1024], b"before".to_vec(), b"after".to_vec()] {
        let content = content.import_bytes(bytes).await.unwrap();
        files.push(
            packages
                .put(&PackageDocument::File {
                    content,
                    executable: false,
                })
                .await
                .unwrap(),
        );
    }
    let base = packages
        .put(&PackageDocument::Collection {
            entries: BTreeMap::from([
                ("unchanged.bin".into(), files[0]),
                ("changed.txt".into(), files[1]),
            ]),
        })
        .await
        .unwrap();
    let changed = packages
        .put(&PackageDocument::Changes {
            base,
            changes: BTreeMap::from([("changed.txt".into(), Some(files[2]))]),
        })
        .await
        .unwrap();
    let base = packages.resolve(base).await.unwrap();
    let changed = packages.resolve(changed).await.unwrap();

    let PackageDocument::Changes {
        base: referenced_base,
        changes,
    } = packages.get(changed.root()).await.unwrap()
    else {
        panic!("expected a Changes package");
    };
    assert_eq!(referenced_base, base.root());
    assert_eq!(changes.len(), 1);
    assert!(changes.contains_key("changed.txt"));
    assert_eq!(
        base.entries()
            .iter()
            .find(|entry| entry.path == "unchanged.bin")
            .unwrap()
            .package,
        changed
            .entries()
            .iter()
            .find(|entry| entry.path == "unchanged.bin")
            .unwrap()
            .package,
    );

    let envelope = PackageEnvelope::new(changed.root()).to_payload().unwrap();
    assert!(envelope.len() < 512);
    let mut proposal = ActivationProposal::root(
        "producer",
        Authority::new([route]),
        Arc::from(b"result".as_slice()),
    );
    proposal.emit(Emission::new(
        "flow",
        OutputAuthority::Carry,
        envelope.clone(),
    ));
    let activation = match session
        .submit_with_content(proposal, changed.dependencies())
        .await
        .unwrap()
    {
        ProposalDecision::Committed(id) => id,
        ProposalDecision::Rejected(error) => panic!("composition was rejected: {error}"),
    };
    let package = session
        .snapshot()
        .await
        .state()
        .package(PackageId::from_parts(activation, 0))
        .unwrap()
        .clone();
    let stored = session
        .content(package.content_digest())
        .await
        .unwrap()
        .unwrap();
    assert_eq!(stored, envelope);
    assert_eq!(
        PackageEnvelope::from_payload(&stored)
            .unwrap()
            .unwrap()
            .ontography_package,
        changed.root(),
    );
    assert_eq!(
        session.activation_content(activation).await.unwrap(),
        changed.dependencies()
    );
}
