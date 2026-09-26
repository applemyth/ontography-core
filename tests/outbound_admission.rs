//! Outbound package births, explicit transfer, and fixed-graph restoration,
//! ported from the sibling application suite.

use std::collections::BTreeMap;
use std::sync::Arc;

use ontography::{
    ActivationProposal, Authority, AuthorityTag, ContentDigest, Contract, ContractViolation,
    DefinitionId, Edge, EdgeDefinition, Emission, Graph, Kernel, Node, NodeDefinition,
    OutputAuthority, PackageId, Phase, Reject, RootRule, Schema, State,
};

fn fixture(with_edge: bool) -> (Kernel, Authority, Authority) {
    let route = AuthorityTag::new("route").unwrap();
    let admin = AuthorityTag::new("admin").unwrap();
    let authority = Authority::new([route.clone()]);
    let expanded = Authority::new([route.clone(), admin.clone()]);
    let schema = Schema::new(
        ["Source", "Sink"],
        ["Message", "Other", "Result"],
        [route.clone(), admin],
    )
    .unwrap();
    let graph = Graph::new(
        [Node::new("source").unwrap(), Node::new("sink").unwrap()],
        if with_edge {
            vec![Edge::new("route", "source", "sink").unwrap()]
        } else {
            vec![]
        },
    )
    .unwrap();
    let message = Contract::new("message", "Message", |bytes| {
        if bytes.starts_with(b"message:") {
            Ok(())
        } else {
            Err(ContractViolation::new("expected message prefix"))
        }
    })
    .unwrap();
    let result = Contract::new("result", "Result", |_| Ok(())).unwrap();
    let edges = if with_edge {
        vec![
            EdgeDefinition::new(
                "route",
                ["Delivery"],
                ["Source"],
                ["Sink"],
                "message",
                [route],
            )
            .unwrap(),
        ]
    } else {
        vec![]
    };
    let kernel = Kernel::admit(
        DefinitionId::new("outbound-tests").unwrap(),
        schema,
        graph,
        [message, result],
        [
            NodeDefinition::new("source", ["Source"], "result").unwrap(),
            NodeDefinition::new("sink", ["Sink"], "result").unwrap(),
        ],
        edges,
        [],
        [RootRule::new("source", expanded.clone()).unwrap()],
    )
    .unwrap();
    (kernel, authority, expanded)
}

fn produce(
    kernel: &Kernel,
    state: &mut State,
    authority: Authority,
    object_type: &str,
    body: &[u8],
) -> PackageId {
    let mut proposal = ActivationProposal::root("source", authority, Arc::from(&b"result"[..]));
    proposal.emit(Emission::outbound(
        object_type,
        OutputAuthority::Carry,
        Arc::from(body),
    ));
    let activation = kernel.activate(state, proposal).unwrap();
    state
        .activation(activation)
        .unwrap()
        .outputs()
        .next()
        .unwrap()
}

#[test]
fn outbound_birth_is_real_undelivered_state_even_without_an_outgoing_edge() {
    let (kernel, authority, _) = fixture(false);
    let mut state = kernel.empty_state();
    let package_id = produce(
        &kernel,
        &mut state,
        authority.clone(),
        "Message",
        b"message:one",
    );
    let package = state.package(package_id).unwrap();
    assert_eq!(package.object_type(), "Message");
    assert_eq!(package.holder(), "source");
    assert_eq!(package.delivery().map(ontography::Delivery::edge_id), None);
    assert_eq!(package.authority(), &authority);
    assert_eq!(state.position(package_id).unwrap().phase(), Phase::Out);
    assert!(state.deliveries().is_empty());
    assert!(state.positions().contains_key(&package_id));
    assert_eq!(state.deliveries().len(), 0);

    let before = state.clone();
    assert_eq!(
        kernel.prepare_trigger(&state, [package_id]),
        Err(Reject::PackageNotDelivered { package_id })
    );
    assert_eq!(
        kernel.activate(
            &mut state,
            ActivationProposal::package(package_id, Arc::from(&b"result"[..]))
        ),
        Err(Reject::PackageNotDelivered { package_id })
    );
    assert_eq!(state, before);
}

#[test]
fn outbound_birth_checks_type_and_authority_without_inventing_a_route_policy() {
    let (kernel, authority, expanded) = fixture(true);
    let mut state = kernel.empty_state();
    for (object_type, output_authority, expected) in [
        (
            "Missing",
            OutputAuthority::Carry,
            Reject::UnknownObjectType {
                object_type: Arc::from("Missing"),
            },
        ),
        (
            "Message",
            OutputAuthority::Transition(expanded.clone()),
            Reject::UnauthorizedAuthorityTransition {
                node_id: Arc::from("source"),
                from: authority.clone(),
                to: expanded,
            },
        ),
    ] {
        let mut proposal =
            ActivationProposal::root("source", authority.clone(), Arc::from(&b"result"[..]));
        proposal.emit(Emission::outbound(
            object_type,
            output_authority,
            Arc::from(&b"message:one"[..]),
        ));
        let before = state.clone();
        assert_eq!(kernel.activate(&mut state, proposal), Err(expected));
        assert_eq!(state, before);
    }
    // An outbound birth has a schema type, but no selected edge contract yet.
    let package_id = produce(
        &kernel,
        &mut state,
        authority,
        "Other",
        b"unconstrained at birth",
    );
    assert_eq!(state.package(package_id).unwrap().object_type(), "Other");
    assert_eq!(state.position(package_id).unwrap().phase(), Phase::Out);
}

#[test]
fn composed_birth_and_delivery_is_atomic() {
    let (kernel, authority, _) = fixture(true);
    let mut state = kernel.empty_state();
    let mut proposal = ActivationProposal::root("source", authority, Arc::from(&b"result"[..]));
    proposal.emit(Emission::new(
        "route",
        OutputAuthority::Carry,
        Arc::from(&b"message:one"[..]),
    ));
    let activation_id = kernel.activate(&mut state, proposal).unwrap();
    let package_id = state
        .activation(activation_id)
        .unwrap()
        .outputs()
        .next()
        .unwrap();
    assert_eq!(state.position(package_id).unwrap().phase(), Phase::In);
    assert_eq!(state.position(package_id).unwrap().holder(), "sink");
    assert_eq!(
        state
            .package(package_id)
            .unwrap()
            .delivery()
            .map(ontography::Delivery::edge_id),
        Some("route")
    );
    let delivery = &state.deliveries()[&package_id];
    assert_eq!(state.package(package_id).unwrap().producer_node(), "source");
    assert_eq!(delivery.receiver(), "sink");
    kernel.prepare_trigger(&state, [package_id]).unwrap();
    kernel
        .activate(
            &mut state,
            ActivationProposal::package(package_id, Arc::from(&b"done"[..])),
        )
        .unwrap();
    assert!(!state.positions().contains_key(&package_id));
    assert!(state.deliveries().contains_key(&package_id));
}

#[test]
fn outbound_birth_restores_under_a_fixed_graph() {
    let (kernel, authority, _) = fixture(false);
    let mut state = kernel.empty_state();
    let package_id = produce(&kernel, &mut state, authority, "Message", b"message:one");
    let restored = kernel
        .restore_state(
            state.to_parts().expect("fixed-graph history"),
            &BTreeMap::from([(
                ContentDigest::compute(b"message:one"),
                Arc::from(&b"message:one"[..]),
            )]),
        )
        .unwrap();
    assert_eq!(restored, state);
    assert_eq!(restored.position(package_id).unwrap().phase(), Phase::Out);
}

#[test]
fn explicit_transfer_delivers_once_and_preserves_the_immutable_birth() {
    let (kernel, authority, _) = fixture(true);
    let mut state = kernel.empty_state();
    let package_id = produce(&kernel, &mut state, authority, "Message", b"message:one");
    let birth = state.activation(package_id.producer()).unwrap().clone();
    let prepared = kernel
        .prepare_transfer(&state, package_id, "route", b"message:one")
        .unwrap();
    kernel.commit_transfer(&mut state, prepared).unwrap();
    assert_eq!(
        state.to_parts(),
        Err(ontography::StateRestoreError::UnsupportedDynamicState)
    );
    assert_eq!(state.position(package_id).unwrap().phase(), Phase::In);
    assert_eq!(state.position(package_id).unwrap().holder(), "sink");
    assert_eq!(
        state
            .package(package_id)
            .unwrap()
            .delivery()
            .map(ontography::Delivery::edge_id),
        Some("route")
    );
    assert_eq!(state.activation(package_id.producer()).unwrap(), &birth);
    assert_eq!(birth.package_outputs()[&package_id].edge_id(), None);
    assert_eq!(state.deliveries().len(), 1);
    let before = state.clone();
    assert!(
        kernel
            .prepare_transfer(&state, package_id, "route", b"message:one")
            .is_err()
    );
    assert_eq!(state, before);
    kernel
        .activate(
            &mut state,
            ActivationProposal::package(package_id, Arc::from(&b"done"[..])),
        )
        .unwrap();
    assert!(state.position(package_id).is_none());
}

#[test]
fn transfer_checks_type_authority_contract_and_digest_as_distinct_facts() {
    let (kernel, authority, _) = fixture(true);
    let mut state = kernel.empty_state();
    let cases: Vec<(&str, Authority, &[u8], &[u8])> = vec![
        ("Other", authority.clone(), b"message:one", b"message:one"),
        (
            "Message",
            Authority::new([AuthorityTag::new("admin").unwrap()]),
            b"message:one",
            b"message:one",
        ),
        (
            "Message",
            authority.clone(),
            b"wrong payload",
            b"wrong payload",
        ),
        ("Message", authority, b"message:one", b"message:different"),
    ];
    for (object_type, authority, body, evidence) in cases {
        let package_id = produce(&kernel, &mut state, authority, object_type, body);
        let before = state.clone();
        assert!(
            kernel
                .prepare_transfer(&state, package_id, "route", evidence)
                .is_err()
        );
        assert_eq!(state, before);
    }
}
