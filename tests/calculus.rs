//! Fixed-graph admission law: definitions, roots, joins, authority
//! transitions, occurrence identity, and restoration. Ported from the sibling
//! application suite; this crate has no `Trigger::Session` variant.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use ontography::{
    Activation, ActivationId, ActivationProposal, Authority, AuthorityMatch, AuthorityTag,
    AuthorityTransitionRule, ContentDigest, Contract, ContractViolation, DefinitionError,
    DefinitionFingerprint, DefinitionId, Edge, EdgeDefinition, Emission, Graph, IngressMode,
    Kernel, Node, NodeDefinition, Output, OutputAuthority, PackageId, PackageRecord, Payload,
    Reject, RootRule, Schema, State, StateParts, StateRestoreError, Trigger,
};

fn payload(value: &[u8]) -> Payload {
    Arc::from(value)
}

fn digest(value: &[u8]) -> ContentDigest {
    ContentDigest::compute(value)
}

macro_rules! payload_evidence {
    ($($value:expr),* $(,)?) => {{
        let mut evidence = BTreeMap::new();
        $(
            let bytes = payload($value);
            evidence.insert(ContentDigest::compute(&bytes), bytes);
        )*
        evidence
    }};
}

fn prefixed_contract(id: &str, object_type: &str, prefix: &'static [u8]) -> Contract {
    Contract::new(id, object_type, move |bytes| {
        bytes
            .starts_with(prefix)
            .then_some(())
            .ok_or_else(|| ContractViolation::new("wrong prefix"))
    })
    .expect("contract")
}

fn authority_tag(source: &str, object: &str, target: &str) -> AuthorityTag {
    AuthorityTag::new(format!("{source}.{object}.{target}")).expect("authority tag")
}

fn authority(tags: impl IntoIterator<Item = AuthorityTag>) -> Authority {
    Authority::new(tags)
}

fn definition_id(value: &str) -> DefinitionId {
    DefinitionId::new(value).expect("definition ID")
}

fn snapshot(state: &State) -> State {
    state.clone()
}

fn root_node_id(activation: &Activation) -> &Arc<str> {
    match activation.trigger() {
        Trigger::Orig { node_id, .. } => node_id,
        Trigger::Pkgs { .. } => panic!("expected a root activation"),
    }
}

fn state_parts_with(
    kernel: &Kernel,
    activations: BTreeMap<ActivationId, Activation>,
) -> StateParts {
    StateParts::new(kernel.id().clone(), *kernel.fingerprint(), activations)
}

fn only_package_id(state: &State) -> PackageId {
    assert_eq!(state.packages().len(), 1);
    *state.packages().keys().next().expect("package")
}

fn package_at_node<'a>(state: &'a State, node_id: &str) -> (PackageId, &'a PackageRecord) {
    let mut matches = state
        .packages()
        .iter()
        .filter(|(_, package)| package.holder() == node_id);
    let (package_id, package) = matches.next().expect("package at node");
    assert!(matches.next().is_none(), "expected one package at node");
    (*package_id, package)
}

struct Fixture {
    schema: Schema,
    graph: Graph,
    contracts: Vec<Contract>,
    definitions: Vec<NodeDefinition>,
    edge_definitions: Vec<EdgeDefinition>,
    evidence: AuthorityTag,
    deploy: AuthorityTag,
    revise: AuthorityTag,
}

fn make_fixture() -> Fixture {
    let evidence = authority_tag("Source", "Evidence", "Review");
    let deploy = authority_tag("Source", "Deploy", "Production");
    let revise = authority_tag("Review", "Request", "Source");
    let schema = Schema::new(
        ["Source", "Review", "Production"],
        ["Request", "Result", "Evidence", "Deploy"],
        [evidence.clone(), deploy.clone(), revise.clone()],
    )
    .expect("schema");
    let graph = Graph::new(
        [
            Node::new("source").expect("source"),
            Node::new("review").expect("review"),
            Node::new("production").expect("production"),
        ],
        [
            Edge::new("source.review", "source", "review").expect("review edge"),
            Edge::new("source.production", "source", "production").expect("production edge"),
            Edge::new("review.source", "review", "source").expect("revision edge"),
        ],
    )
    .expect("graph");
    let contracts = vec![
        prefixed_contract("request", "Request", b"request:"),
        prefixed_contract("result", "Result", b"result:"),
        prefixed_contract("evidence", "Evidence", b"evidence:"),
        prefixed_contract("deploy", "Deploy", b"deploy:"),
    ];
    let definitions = vec![
        NodeDefinition::new("source", ["Source"], "result").expect("source definition"),
        NodeDefinition::new("review", ["Review"], "result").expect("review definition"),
        NodeDefinition::new("production", ["Production"], "result").expect("production definition"),
    ];
    let edge_definitions = vec![
        EdgeDefinition::new(
            "source.review",
            ["EvidenceSubmission"],
            ["Source"],
            ["Review"],
            "evidence",
            [evidence.clone()],
        )
        .expect("review definition"),
        EdgeDefinition::new(
            "source.production",
            ["Deployment"],
            ["Source"],
            ["Production"],
            "deploy",
            [deploy.clone()],
        )
        .expect("production definition"),
        EdgeDefinition::new(
            "review.source",
            ["RevisionRequest"],
            ["Review"],
            ["Source"],
            "request",
            [revise.clone()],
        )
        .expect("revision definition"),
    ];
    Fixture {
        schema,
        graph,
        contracts,
        definitions,
        edge_definitions,
        evidence,
        deploy,
        revise,
    }
}

fn make_kernel(
    authority_transitions: impl IntoIterator<Item = AuthorityTransitionRule>,
    roots: impl IntoIterator<Item = RootRule>,
) -> Kernel {
    make_kernel_with_id(definition_id("fixture"), authority_transitions, roots)
}

fn make_kernel_with_id(
    id: DefinitionId,
    authority_transitions: impl IntoIterator<Item = AuthorityTransitionRule>,
    roots: impl IntoIterator<Item = RootRule>,
) -> Kernel {
    let fixture = make_fixture();
    Kernel::admit(
        id,
        fixture.schema,
        fixture.graph,
        fixture.contracts,
        fixture.definitions,
        fixture.edge_definitions,
        authority_transitions,
        roots,
    )
    .expect("kernel")
}

fn source_root(ceiling: Authority) -> RootRule {
    RootRule::new("source", ceiling).expect("root rule")
}

struct JoinFixture {
    kernel: Kernel,
    full: Authority,
    left: Authority,
    right: Authority,
}

fn make_join_fixture(ingress_mode: IngressMode) -> JoinFixture {
    let root_left = authority_tag("Root", "Signal", "Left");
    let root_right = authority_tag("Root", "Signal", "Right");
    let left_join = authority_tag("Left", "Signal", "Join");
    let right_join = authority_tag("Right", "Signal", "Join");
    let full = authority([
        root_left.clone(),
        root_right.clone(),
        left_join.clone(),
        right_join.clone(),
    ]);
    let left = authority([root_left.clone(), left_join.clone()]);
    let right = authority([root_right.clone(), right_join.clone()]);
    let schema = Schema::new(
        ["Root", "Left", "Right", "Join"],
        ["Signal", "Result"],
        [root_left, root_right, left_join, right_join],
    )
    .expect("join schema");
    let graph = Graph::new(
        [
            Node::new("root").expect("root"),
            Node::new("left").expect("left"),
            Node::new("right").expect("right"),
            Node::new("join").expect("join"),
        ],
        [
            Edge::new("root.left", "root", "left").expect("root-left"),
            Edge::new("root.right", "root", "right").expect("root-right"),
            Edge::new("left.join", "left", "join").expect("left-join"),
            Edge::new("right.join", "right", "join").expect("right-join"),
        ],
    )
    .expect("join graph");
    let contracts = [
        prefixed_contract("signal", "Signal", b"signal:"),
        prefixed_contract("result", "Result", b"result:"),
    ];
    let definitions = [
        NodeDefinition::new("root", ["Root"], "result").expect("root"),
        NodeDefinition::new("left", ["Left"], "result").expect("left"),
        NodeDefinition::new("right", ["Right"], "result").expect("right"),
        NodeDefinition::new("join", ["Join"], "result")
            .expect("join")
            .with_ingress_mode(ingress_mode),
    ];
    let edge_definitions = [
        EdgeDefinition::new(
            "root.left",
            ["Signal"],
            ["Root"],
            ["Left"],
            "signal",
            [authority_tag("Root", "Signal", "Left")],
        )
        .expect("root-left definition"),
        EdgeDefinition::new(
            "root.right",
            ["Signal"],
            ["Root"],
            ["Right"],
            "signal",
            [authority_tag("Root", "Signal", "Right")],
        )
        .expect("root-right definition"),
        EdgeDefinition::new(
            "left.join",
            ["Signal"],
            ["Left"],
            ["Join"],
            "signal",
            [authority_tag("Left", "Signal", "Join")],
        )
        .expect("left-join definition"),
        EdgeDefinition::new(
            "right.join",
            ["Signal"],
            ["Right"],
            ["Join"],
            "signal",
            [authority_tag("Right", "Signal", "Join")],
        )
        .expect("right-join definition"),
    ];
    let transitions = [
        AuthorityTransitionRule::new("root", full.clone(), left.clone()).expect("left authority"),
        AuthorityTransitionRule::new("root", full.clone(), right.clone()).expect("right authority"),
    ];
    let kernel = Kernel::admit(
        definition_id("join"),
        schema,
        graph,
        contracts,
        definitions,
        edge_definitions,
        transitions,
        [RootRule::new("root", full.clone()).expect("join root")],
    )
    .expect("join kernel");
    JoinFixture {
        kernel,
        full,
        left,
        right,
    }
}

fn prepare_join(
    kernel: &Kernel,
    authority: Authority,
    root_outputs: [OutputAuthority; 2],
) -> (State, BTreeSet<PackageId>) {
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("root", authority, payload(b"result:root"));
    for ((edge, message), output_authority) in [
        ("root.left", b"signal:left".as_slice()),
        ("root.right", b"signal:right".as_slice()),
    ]
    .into_iter()
    .zip(root_outputs)
    {
        root.emit(Emission::new(edge, output_authority, payload(message)));
    }
    kernel.activate(&mut state, root).expect("join root");
    let (left_input, _) = package_at_node(&state, "left");
    let (right_input, _) = package_at_node(&state, "right");

    for (input, edge, message) in [
        (left_input, "left.join", b"signal:left-ready".as_slice()),
        (right_input, "right.join", b"signal:right-ready".as_slice()),
    ] {
        let mut branch = ActivationProposal::package(input, payload(b"result:branch"));
        branch.emit(Emission::new(
            edge,
            OutputAuthority::Carry,
            payload(message),
        ));
        kernel.activate(&mut state, branch).expect("join branch");
    }

    let inputs = state
        .positions()
        .keys()
        .copied()
        .filter(|package_id| {
            state
                .package(*package_id)
                .is_some_and(|package| package.holder() == "join")
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(inputs.len(), 2);
    (state, inputs)
}

#[test]
fn graph_is_topology_only_and_supports_multigraph_structure() {
    let empty = Graph::new(Vec::<Node>::new(), Vec::<Edge>::new()).expect("empty graph");
    assert!(empty.nodes().is_empty());
    assert!(empty.edges().is_empty());
    let empty_schema = Schema::new(
        Vec::<&str>::new(),
        Vec::<&str>::new(),
        Vec::<AuthorityTag>::new(),
    )
    .expect("empty schema");
    Kernel::admit(
        definition_id("empty"),
        empty_schema,
        empty,
        Vec::<Contract>::new(),
        Vec::<NodeDefinition>::new(),
        Vec::<EdgeDefinition>::new(),
        Vec::<AuthorityTransitionRule>::new(),
        Vec::<RootRule>::new(),
    )
    .expect("empty definition");

    let graph = Graph::new(
        [Node::new("node").expect("node")],
        [
            Edge::new("loop.one", "node", "node").expect("edge"),
            Edge::new("loop.two", "node", "node").expect("parallel edge"),
        ],
    )
    .expect("graph");

    assert_eq!(graph.nodes()[0].id(), "node");
    assert_eq!(graph.edges().len(), 2);
    assert_eq!(graph.edge("loop.one").expect("edge").source(), "node");
    assert!(matches!(
        Graph::new(
            [Node::new("node").expect("node")],
            [Edge::new("missing", "node", "other").expect("edge")],
        ),
        Err(DefinitionError::UnknownEndpoint(_))
    ));
}

#[test]
fn canonical_activations_and_derived_indexes_are_identity_keyed() {
    fn packages(_: &BTreeMap<PackageId, PackageRecord>) {}
    fn activations(_: &BTreeMap<ActivationId, ontography::Activation>) {}

    let kernel = make_kernel([], [source_root(Authority::default())]);
    let state = kernel.empty_state();

    packages(state.packages());
    activations(state.activations());
}

#[test]
fn definition_uses_explicit_edge_authority_tags() {
    let fixture = make_fixture();
    let kernel = Kernel::admit(
        definition_id("fixture"),
        fixture.schema,
        fixture.graph,
        fixture.contracts,
        fixture.definitions,
        fixture.edge_definitions,
        [],
        [],
    )
    .expect("definition");

    assert_eq!(
        kernel
            .edge_definition("source.review")
            .map(ontography::EdgeDefinition::authority_tags),
        Some(&BTreeSet::from([fixture.evidence]))
    );
    assert_eq!(
        kernel
            .edge_definition("source.production")
            .map(ontography::EdgeDefinition::authority_tags),
        Some(&BTreeSet::from([fixture.deploy]))
    );
    assert_eq!(
        kernel
            .edge_definition("review.source")
            .map(ontography::EdgeDefinition::authority_tags),
        Some(&BTreeSet::from([fixture.revise]))
    );
    assert_eq!(kernel.graph().edges()[0].id(), "review.source");
}

#[test]
fn edge_authority_matching_is_any_of_by_default_and_all_of_when_selected() {
    let west = AuthorityTag::new("west").expect("west");
    let central = AuthorityTag::new("central").expect("central");
    let east = AuthorityTag::new("east").expect("east");
    let any = EdgeDefinition::new(
        "route",
        ["Delivery"],
        ["Source"],
        ["Target"],
        "item",
        [west.clone(), central.clone()],
    )
    .expect("edge definition");

    assert_eq!(any.authority_match(), AuthorityMatch::AnyOf);
    assert!(any.matches_authority(&authority([west.clone()])));
    assert!(any.matches_authority(&authority([central.clone(), east.clone()])));
    assert!(!any.matches_authority(&authority([east.clone()])));
    assert!(!any.matches_authority(&Authority::default()));

    let all = any.with_authority_match(AuthorityMatch::AllOf);
    assert!(!all.matches_authority(&authority([west.clone()])));
    assert!(all.matches_authority(&authority([west.clone(), central.clone()])));
    assert!(all.matches_authority(&authority([west, central, east])));
}

#[test]
fn edge_authority_tags_must_be_nonempty() {
    assert_eq!(
        EdgeDefinition::new(
            "route",
            ["Delivery"],
            ["Source"],
            ["Target"],
            "item",
            std::iter::empty::<AuthorityTag>(),
        ),
        Err(DefinitionError::MissingEdgeAuthorityTags(Arc::from(
            "route"
        )))
    );
}

#[test]
fn definition_rejects_an_edge_attached_to_an_incompatible_node() {
    let mut fixture = make_fixture();
    fixture.definitions[1] =
        NodeDefinition::new("review", ["Production"], "result").expect("changed definition");

    assert!(matches!(
        Kernel::admit(
            definition_id("invalid"),
            fixture.schema,
            fixture.graph,
            fixture.contracts,
            fixture.definitions,
            fixture.edge_definitions,
            [],
            [],
        ),
        Err(DefinitionError::EdgeSourceRequirements { .. }
            | DefinitionError::EdgeTargetRequirements { .. })
    ));
}

#[test]
fn definition_rejects_an_edge_authority_tag_outside_the_schema() {
    let mut fixture = make_fixture();
    let outside = AuthorityTag::new("outside").expect("outside tag");
    fixture.edge_definitions[0] = EdgeDefinition::new(
        "source.review",
        ["EvidenceSubmission"],
        ["Source"],
        ["Review"],
        "evidence",
        [fixture.evidence.clone(), outside.clone()],
    )
    .expect("edge definition");

    assert!(matches!(
        Kernel::admit(
            definition_id("invalid-authority-tag"),
            fixture.schema,
            fixture.graph,
            fixture.contracts,
            fixture.definitions,
            fixture.edge_definitions,
            [],
            [],
        ),
        Err(DefinitionError::ForbiddenAuthorityTag { edge, tag })
            if &*edge == "source.review" && tag == outside
    ));
}

#[test]
fn every_topology_node_requires_exactly_one_definition() {
    let mut fixture = make_fixture();
    fixture.definitions.pop();
    assert!(matches!(
        Kernel::admit(
            definition_id("missing"),
            fixture.schema,
            fixture.graph,
            fixture.contracts,
            fixture.definitions,
            fixture.edge_definitions,
            [],
            [],
        ),
        Err(DefinitionError::MissingNodeDefinition(_))
    ));

    let mut fixture = make_fixture();
    fixture.definitions.push(fixture.definitions[0].clone());
    assert!(matches!(
        Kernel::admit(
            definition_id("duplicate"),
            fixture.schema,
            fixture.graph,
            fixture.contracts,
            fixture.definitions,
            fixture.edge_definitions,
            [],
            [],
        ),
        Err(DefinitionError::DuplicateNodeDefinition(_))
    ));
}

#[test]
fn root_policy_is_partial_and_its_ceiling_must_be_in_the_schema() {
    let fixture = make_fixture();
    let outside = authority([authority_tag("Review", "Deploy", "Production")]);
    assert_eq!(
        Kernel::admit(
            definition_id("invalid-root"),
            fixture.schema,
            fixture.graph,
            fixture.contracts,
            fixture.definitions,
            fixture.edge_definitions,
            [],
            [RootRule::new("source", outside).expect("rule")],
        )
        .err(),
        Some(DefinitionError::RootAuthorityOutsideSchema)
    );

    let kernel = make_kernel([], []);
    let mut state = kernel.empty_state();
    assert!(matches!(
        kernel.activate(
            &mut state,
            ActivationProposal::root("source", Authority::default(), payload(b"result:root"),),
        ),
        Err(Reject::RootNotAllowed { node_id }) if &*node_id == "source"
    ));
}

#[test]
fn root_activation_has_no_ingress_package_and_validates_only_its_result() {
    let kernel = make_kernel([], [source_root(Authority::default())]);
    let mut state = kernel.empty_state();
    let unchanged = snapshot(&state);
    assert!(matches!(
        kernel.activate(
            &mut state,
            ActivationProposal::root(
                "source",
                Authority::default(),
                payload(b"request:not-a-result"),
            ),
        ),
        Err(Reject::ResultContract { .. })
    ));
    assert_eq!(snapshot(&state), unchanged);

    let activation_id = kernel
        .activate(
            &mut state,
            ActivationProposal::root(
                "source",
                Authority::default(),
                payload(b"result:external-occurrence"),
            ),
        )
        .expect("root");

    assert!(state.activation(activation_id).is_some());
    assert_eq!(state.packages().len(), 0);
    assert_eq!(state.activations().len(), 1);
    assert!(state.positions().is_empty());
    let activation = state.activation(activation_id).expect("activation");
    assert!(matches!(
        activation.trigger(),
        Trigger::Orig { node_id, authority }
            if &**node_id == "source" && authority == &Authority::default()
    ));
    assert_eq!(
        activation
            .package_outputs()
            .values()
            .filter(|output| output.edge_id().is_some())
            .count(),
        0
    );
}

#[test]
fn accepted_root_node_ids_reuse_static_storage() {
    let kernel = make_kernel([], [source_root(Authority::default())]);
    let mut state = kernel.empty_state();
    let first = kernel
        .activate(
            &mut state,
            ActivationProposal::root(
                Arc::<str>::from("source"),
                Authority::default(),
                payload(b"result:first"),
            ),
        )
        .expect("first root");
    let second = kernel
        .activate(
            &mut state,
            ActivationProposal::root(
                Arc::<str>::from("source"),
                Authority::default(),
                payload(b"result:second"),
            ),
        )
        .expect("second root");

    assert!(Arc::ptr_eq(
        root_node_id(state.activation(first).expect("first activation")),
        root_node_id(state.activation(second).expect("second activation")),
    ));

    let mut activations = state.activations().clone();
    let first_record = activations.get(&first).expect("first record");
    let external_node_id = Arc::<str>::from("source");
    let forged = Activation::new(
        "source",
        Trigger::Orig {
            node_id: Arc::clone(&external_node_id),
            authority: Authority::default(),
        },
        Arc::clone(first_record.result()),
        first_record.package_outputs().clone(),
    );
    activations.insert(first, forged);
    let restored = kernel
        .restore_state(state_parts_with(&kernel, activations), &BTreeMap::new())
        .expect("restore roots");
    let restored_first = root_node_id(
        restored
            .activation(first)
            .expect("restored first activation"),
    );
    let restored_second = root_node_id(
        restored
            .activation(second)
            .expect("restored second activation"),
    );
    assert!(!Arc::ptr_eq(&external_node_id, restored_first));
    assert!(Arc::ptr_eq(restored_first, restored_second));
}

#[test]
fn root_authority_must_be_within_its_ceiling() {
    let fixture = make_fixture();
    let kernel = make_kernel([], [source_root(authority([fixture.evidence.clone()]))]);
    let mut state = kernel.empty_state();
    let unchanged = snapshot(&state);

    assert!(matches!(
        kernel.activate(
            &mut state,
            ActivationProposal::root(
                "source",
                authority([fixture.deploy]),
                payload(b"result:root"),
            ),
        ),
        Err(Reject::RootAuthorityExceeded { node_id, .. }) if &*node_id == "source"
    ));
    assert_eq!(snapshot(&state), unchanged);
}

#[test]
fn root_activation_delivers_requested_packages_atomically() {
    let fixture = make_fixture();
    let root_authority = authority([fixture.evidence.clone(), fixture.deploy.clone()]);
    let kernel = make_kernel([], [source_root(root_authority.clone())]);
    let mut state = kernel.empty_state();
    let mut proposal =
        ActivationProposal::root("source", root_authority.clone(), payload(b"result:root"));
    proposal.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:first"),
    ));
    proposal.emit(Emission::new(
        "source.production",
        OutputAuthority::Carry,
        payload(b"deploy:second"),
    ));

    let activation_id = kernel.activate(&mut state, proposal).expect("activation");

    assert_eq!(state.packages().len(), 2);
    let (review_package, review_custody) = package_at_node(&state, "review");
    let (production_package, _) = package_at_node(&state, "production");
    assert_eq!(review_custody.authority(), &root_authority);
    let review = kernel
        .edge_definition(review_custody.delivery().expect("delivered edge").edge_id())
        .expect("review edge definition");
    assert_eq!(
        kernel
            .contract(review.package_contract())
            .expect("package contract")
            .object_type(),
        "Evidence"
    );
    assert_eq!(state.package_producer(review_package), Some(activation_id));
    assert_eq!(
        state.package_producer(production_package),
        Some(activation_id)
    );
    assert_eq!(review_package.producer(), activation_id);
    assert_eq!(
        review_custody.delivery().map(ontography::Delivery::edge_id),
        Some("source.review")
    );
    let activation = state.activation(activation_id).expect("activation");
    assert_eq!(
        activation
            .package_outputs()
            .get(&review_package)
            .expect("activation-owned output")
            .edge_id(),
        review_custody.delivery().map(ontography::Delivery::edge_id)
    );
    assert_eq!(
        state.positions().keys().copied().collect::<BTreeSet<_>>(),
        BTreeSet::from([review_package, production_package])
    );
    assert_eq!(state.deliveries().len(), 2);
}

#[test]
fn package_triggered_activation_consumes_once_and_can_terminate() {
    let fixture = make_fixture();
    let root_authority = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(root_authority.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", root_authority, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:work"),
    ));
    kernel.activate(&mut state, root).expect("root");
    let package_id = only_package_id(&state);

    let activation_id = kernel
        .activate(
            &mut state,
            ActivationProposal::package(package_id, payload(b"result:reviewed")),
        )
        .expect("package activation");

    assert_eq!(state.package_consumer(package_id), Some(activation_id));
    assert!(state.is_quiescent());
    assert!(matches!(
        state.activation(activation_id).expect("activation").trigger(),
        Trigger::Pkgs { package_ids } if package_ids == &BTreeSet::from([package_id])
    ));
    let unchanged = snapshot(&state);
    assert!(matches!(
        kernel.activate(
            &mut state,
            ActivationProposal::package(package_id, payload(b"result:again")),
        ),
        Err(Reject::AlreadyActivated {
            package_id: rejected,
            activation_id: consumer,
        }) if rejected == package_id && consumer == activation_id
    ));
    assert_eq!(snapshot(&state), unchanged);
}

#[test]
fn trigger_preparation_snapshots_any_input_without_reserving_it() {
    let fixture = make_fixture();
    let root_authority = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(root_authority.clone())]);
    let mut state = kernel.empty_state();
    let mut root =
        ActivationProposal::root("source", root_authority.clone(), payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:work"),
    ));
    kernel.activate(&mut state, root).expect("root");
    let package_id = only_package_id(&state);
    let unchanged = snapshot(&state);

    let witness = kernel
        .prepare_trigger(&state, [package_id])
        .expect("prepared package trigger");
    let repeated = kernel
        .prepare_trigger(&state, [package_id])
        .expect("preparation does not reserve inputs");

    assert_eq!(witness, repeated);
    assert_eq!(state, unchanged);
    assert_eq!(witness.definition_id(), state.definition_id());
    assert_eq!(
        witness.definition_fingerprint(),
        state.definition_fingerprint()
    );
    assert_eq!(witness.package_ids(), &BTreeSet::from([package_id]));
    assert_eq!(witness.node_id(), "review");
    assert_eq!(witness.authority(), &root_authority);
    assert_eq!(witness.ingress_mode(), IngressMode::Any);
    assert_eq!(
        witness.incoming_edge_ids(),
        &BTreeSet::from([Arc::<str>::from("source.review")])
    );
    assert_eq!(witness.incoming_edge_ids(), witness.realized_edge_ids());
    assert_eq!(
        witness.packages().get(&package_id),
        state.package(package_id)
    );

    let consumer = kernel
        .activate(
            &mut state,
            ActivationProposal::package(package_id, payload(b"result:reviewed")),
        )
        .expect("package activation");
    assert_eq!(state.package_consumer(package_id), Some(consumer));
    assert_eq!(
        witness
            .packages()
            .get(&package_id)
            .expect("witness retains its snapshot")
            .content_digest(),
        digest(b"evidence:work")
    );
    assert!(matches!(
        kernel.prepare_trigger(&state, [package_id]),
        Err(Reject::AlreadyActivated {
            package_id: rejected,
            activation_id,
        }) if rejected == package_id && activation_id == consumer
    ));
}

#[test]
fn trigger_preparation_exposes_exact_all_ingress_facts() {
    let fixture = make_join_fixture(IngressMode::All);
    let (state, inputs) = prepare_join(
        &fixture.kernel,
        fixture.full.clone(),
        [OutputAuthority::Carry, OutputAuthority::Carry],
    );
    let unchanged = snapshot(&state);

    let witness = fixture
        .kernel
        .prepare_trigger(&state, inputs.iter().copied())
        .expect("complete All trigger");
    let expected_edges = BTreeSet::from([
        Arc::<str>::from("left.join"),
        Arc::<str>::from("right.join"),
    ]);

    assert_eq!(state, unchanged);
    assert_eq!(witness.package_ids(), &inputs);
    assert_eq!(witness.packages().len(), 2);
    assert!(
        inputs
            .iter()
            .all(|package_id| { witness.packages().get(package_id) == state.package(*package_id) })
    );
    assert_eq!(witness.node_id(), "join");
    assert_eq!(witness.authority(), &fixture.full);
    assert_eq!(witness.ingress_mode(), IngressMode::All);
    assert_eq!(witness.incoming_edge_ids(), &expected_edges);
    assert_eq!(witness.realized_edge_ids(), &expected_edges);

    let one = *inputs.first().expect("one join input");
    assert!(matches!(
        fixture.kernel.prepare_trigger(&state, [one]),
        Err(Reject::JoinEdgeMismatch { .. })
    ));
    assert_eq!(state, unchanged);
}

#[test]
fn join_consumes_all_inputs_and_restores_the_causal_dag() {
    let fixture = make_join_fixture(IngressMode::All);
    let any_fixture = make_join_fixture(IngressMode::Any);
    assert_ne!(
        fixture.kernel.fingerprint(),
        any_fixture.kernel.fingerprint()
    );
    let (mut state, inputs) = prepare_join(
        &fixture.kernel,
        fixture.full,
        [OutputAuthority::Carry, OutputAuthority::Carry],
    );
    let join_id = fixture
        .kernel
        .activate(
            &mut state,
            ActivationProposal::join(inputs.iter().copied(), payload(b"result:joined")),
        )
        .expect("join");

    assert_eq!(
        state.activation(join_id).expect("join activation").inputs(),
        Some(&inputs)
    );
    assert!(
        inputs
            .iter()
            .all(|package_id| state.package_consumer(*package_id) == Some(join_id))
    );
    assert!(state.is_quiescent());

    let expected = state.clone();
    let restored = fixture
        .kernel
        .restore_state(
            state.into_parts().expect("fixed-graph history"),
            &payload_evidence!(
                b"signal:left",
                b"signal:right",
                b"signal:left-ready",
                b"signal:right-ready",
            ),
        )
        .expect("join DAG restores");
    assert_eq!(restored, expected);
}

#[test]
fn incomplete_empty_and_invalid_result_joins_are_atomic() {
    let fixture = make_join_fixture(IngressMode::All);
    let (mut state, inputs) = prepare_join(
        &fixture.kernel,
        fixture.full,
        [OutputAuthority::Carry, OutputAuthority::Carry],
    );
    let unchanged = snapshot(&state);

    assert_eq!(
        fixture.kernel.activate(
            &mut state,
            ActivationProposal::join([], payload(b"result:empty")),
        ),
        Err(Reject::EmptyPackageTrigger)
    );
    assert_eq!(state, unchanged);

    let one = *inputs.first().expect("one join input");
    assert!(matches!(
        fixture.kernel.activate(
            &mut state,
            ActivationProposal::join([one], payload(b"result:partial")),
        ),
        Err(Reject::JoinEdgeMismatch { .. })
    ));
    assert_eq!(state, unchanged);

    assert!(matches!(
        fixture.kernel.activate(
            &mut state,
            ActivationProposal::join(inputs, payload(b"invalid-result")),
        ),
        Err(Reject::ResultContract { .. })
    ));
    assert_eq!(state, unchanged);

    let any_fixture = make_join_fixture(IngressMode::Any);
    let (mut any_state, any_inputs) = prepare_join(
        &any_fixture.kernel,
        any_fixture.full,
        [OutputAuthority::Carry, OutputAuthority::Carry],
    );
    let unchanged = snapshot(&any_state);
    assert!(matches!(
        any_fixture.kernel.activate(
            &mut any_state,
            ActivationProposal::join(any_inputs, payload(b"result:not-allowed")),
        ),
        Err(Reject::JoinNotAllowed { input_count: 2, .. })
    ));
    assert_eq!(any_state, unchanged);
}

#[test]
fn join_rejects_mismatched_targets_and_authorities_atomically() {
    let fixture = make_join_fixture(IngressMode::All);
    let mut state = fixture.kernel.empty_state();
    let mut root = ActivationProposal::root("root", fixture.full.clone(), payload(b"result:root"));
    for (edge, message) in [
        ("root.left", b"signal:left".as_slice()),
        ("root.right", b"signal:right".as_slice()),
    ] {
        root.emit(Emission::new(
            edge,
            OutputAuthority::Carry,
            payload(message),
        ));
    }
    fixture.kernel.activate(&mut state, root).expect("root");
    let different_targets = state.positions().keys().copied().collect::<BTreeSet<_>>();
    let unchanged = snapshot(&state);
    assert!(matches!(
        fixture.kernel.activate(
            &mut state,
            ActivationProposal::join(different_targets, payload(b"result:invalid")),
        ),
        Err(Reject::JoinTargetMismatch { .. })
    ));
    assert_eq!(state, unchanged);

    let (mut state, inputs) = prepare_join(
        &fixture.kernel,
        fixture.full,
        [
            OutputAuthority::Transition(fixture.left),
            OutputAuthority::Transition(fixture.right),
        ],
    );
    let unchanged = snapshot(&state);
    assert!(matches!(
        fixture.kernel.activate(
            &mut state,
            ActivationProposal::join(inputs, payload(b"result:invalid")),
        ),
        Err(Reject::JoinAuthorityMismatch { .. })
    ));
    assert_eq!(state, unchanged);
}

#[test]
fn restoration_rejects_empty_and_partial_join_triggers() {
    let fixture = make_join_fixture(IngressMode::All);
    let empty_id = ActivationId::from_u128(301);
    let empty = Activation::new(
        "review",
        Trigger::Pkgs {
            package_ids: BTreeSet::new(),
        },
        payload(b"result:empty"),
        BTreeMap::new(),
    );
    assert!(matches!(
        fixture.kernel.restore_state(
            state_parts_with(
                &fixture.kernel,
                BTreeMap::from([(empty_id, empty)]),
            ),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id,
            source,
        }) if activation_id == empty_id && *source == Reject::EmptyPackageTrigger
    ));

    let (state, inputs) = prepare_join(
        &fixture.kernel,
        fixture.full,
        [OutputAuthority::Carry, OutputAuthority::Carry],
    );
    let partial_id = ActivationId::from_u128(302);
    let partial = Activation::new(
        "review",
        Trigger::Pkgs {
            package_ids: BTreeSet::from([*inputs.first().expect("join input")]),
        },
        payload(b"result:partial"),
        BTreeMap::new(),
    );
    let mut activations = state.activations().clone();
    assert!(activations.insert(partial_id, partial).is_none());
    assert!(matches!(
        fixture
            .kernel
            .restore_state(
                state_parts_with(&fixture.kernel, activations),
                &payload_evidence!(
                    b"signal:left",
                    b"signal:right",
                    b"signal:left-ready",
                    b"signal:right-ready",
                ),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id,
            source,
        }) if activation_id == partial_id
            && matches!(*source, Reject::JoinEdgeMismatch { .. })
    ));
}

#[test]
fn package_activation_can_handoff_and_preserve_authority() {
    let fixture = make_fixture();
    let root_authority = authority([fixture.evidence, fixture.revise]);
    let kernel = make_kernel([], [source_root(root_authority.clone())]);
    let mut state = kernel.empty_state();
    let mut root =
        ActivationProposal::root("source", root_authority.clone(), payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:work"),
    ));
    kernel.activate(&mut state, root).expect("root");
    let input_id = only_package_id(&state);
    let mut review = ActivationProposal::package(input_id, payload(b"result:reviewed"));
    review.emit(Emission::new(
        "review.source",
        OutputAuthority::Carry,
        payload(b"request:revision"),
    ));

    let review_id = kernel.activate(&mut state, review).expect("review");

    let (output_id, output) = package_at_node(&state, "source");
    assert_eq!(output.authority(), &root_authority);
    assert_eq!(state.package_consumer(input_id), Some(review_id));
    assert_eq!(state.package_producer(output_id), Some(review_id));
    assert_eq!(
        state.positions().keys().copied().collect::<BTreeSet<_>>(),
        BTreeSet::from([output_id])
    );
}

#[test]
fn authority_transitions_may_amplify_and_apply_to_both_trigger_forms() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence.clone()]);
    let deploy = authority([fixture.deploy.clone()]);
    let transition = AuthorityTransitionRule::new("source", evidence.clone(), deploy.clone())
        .expect("transition");
    let kernel = make_kernel([transition], [source_root(evidence.clone())]);
    let mut root_state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    root.emit(Emission::new(
        "source.production",
        OutputAuthority::Transition(deploy.clone()),
        payload(b"deploy:root"),
    ));
    kernel
        .activate(&mut root_state, root)
        .expect("root transition");
    assert_eq!(
        root_state
            .package(only_package_id(&root_state))
            .expect("package")
            .authority(),
        &deploy
    );

    let source_authority = authority([fixture.evidence, fixture.revise]);
    let kernel = make_kernel(
        [
            AuthorityTransitionRule::new("source", source_authority.clone(), deploy.clone())
                .expect("transition"),
        ],
        [source_root(source_authority.clone())],
    );
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", source_authority, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:to-review"),
    ));
    kernel.activate(&mut state, root).expect("root");
    let first = only_package_id(&state);
    let mut review = ActivationProposal::package(first, payload(b"result:review"));
    review.emit(Emission::new(
        "review.source",
        OutputAuthority::Carry,
        payload(b"request:return"),
    ));
    kernel.activate(&mut state, review).expect("review");
    let second = *state.positions().keys().next().expect("second package");
    let mut source = ActivationProposal::package(second, payload(b"result:source"));
    source.emit(Emission::new(
        "source.production",
        OutputAuthority::Transition(deploy.clone()),
        payload(b"deploy:package"),
    ));
    kernel
        .activate(&mut state, source)
        .expect("package transition");
    let output = *state.positions().keys().next().expect("output package");
    assert_eq!(state.package(output).expect("output").authority(), &deploy);
}

#[test]
fn one_transition_authority_can_govern_multiple_outputs() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence.clone()]);
    let transition = AuthorityTransitionRule::new("source", evidence.clone(), evidence.clone())
        .expect("transition");
    let kernel = make_kernel([transition], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut proposal =
        ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    for value in [b"evidence:first".as_slice(), b"evidence:second".as_slice()] {
        proposal.emit(Emission::new(
            "source.review",
            OutputAuthority::Transition(evidence.clone()),
            payload(value),
        ));
    }

    kernel.activate(&mut state, proposal).expect("activation");

    assert!(
        state
            .packages()
            .values()
            .all(|package| package.authority() == &evidence)
    );
}

#[test]
fn explicit_preserving_transition_requires_an_exact_rule_and_is_atomic() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let unchanged = snapshot(&state);
    let mut proposal =
        ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    proposal.emit(Emission::new(
        "source.review",
        OutputAuthority::Transition(evidence.clone()),
        payload(b"evidence:preserved"),
    ));

    assert_eq!(
        kernel.activate(&mut state, proposal),
        Err(Reject::UnauthorizedAuthorityTransition {
            node_id: Arc::from("source"),
            from: evidence.clone(),
            to: evidence,
        })
    );
    assert_eq!(state, unchanged);
}

#[test]
fn unauthorized_output_authority_does_not_mutate_state() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence.clone()]);
    let deploy = authority([fixture.deploy]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let unchanged = snapshot(&state);
    let mut unauthorized = ActivationProposal::root("source", evidence, payload(b"result:root"));
    unauthorized.emit(Emission::new(
        "source.production",
        OutputAuthority::Transition(deploy),
        payload(b"deploy:unauthorized"),
    ));
    assert!(matches!(
        kernel.activate(&mut state, unauthorized),
        Err(Reject::UnauthorizedAuthorityTransition { node_id, .. })
            if &*node_id == "source"
    ));
    assert_eq!(snapshot(&state), unchanged);
}

#[test]
fn authority_source_and_edge_contracts_are_checked_before_mutation() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence.clone()]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();

    let mut unauthorized =
        ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    unauthorized.emit(Emission::new(
        "source.production",
        OutputAuthority::Carry,
        payload(b"deploy:item"),
    ));
    let unchanged = snapshot(&state);
    assert!(matches!(
        kernel.activate(&mut state, unauthorized),
        Err(Reject::EdgeAuthorityMismatch { edge_id, .. })
            if &*edge_id == "source.production"
    ));
    assert_eq!(snapshot(&state), unchanged);

    let mut wrong_source =
        ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    wrong_source.emit(Emission::new(
        "review.source",
        OutputAuthority::Carry,
        payload(b"request:item"),
    ));
    assert!(matches!(
        kernel.activate(&mut state, wrong_source),
        Err(Reject::WrongSource {
            edge_id,
            expected,
            actual,
        }) if &*edge_id == "review.source"
            && &*expected == "source"
            && &*actual == "review"
    ));
    assert_eq!(snapshot(&state), unchanged);

    let mut bad_payload = ActivationProposal::root("source", evidence, payload(b"result:root"));
    bad_payload.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"not-evidence"),
    ));
    assert!(matches!(
        kernel.activate(&mut state, bad_payload),
        Err(Reject::PayloadContract { .. })
    ));
    assert_eq!(snapshot(&state), unchanged);
}

#[test]
fn kernel_enforces_each_edges_authority_match_rule() {
    fn kernel(authority_match: AuthorityMatch) -> Kernel {
        let mut fixture = make_fixture();
        fixture.edge_definitions[0] = EdgeDefinition::new(
            "source.review",
            ["EvidenceSubmission"],
            ["Source"],
            ["Review"],
            "evidence",
            [fixture.evidence.clone(), fixture.deploy.clone()],
        )
        .expect("multi-tag edge")
        .with_authority_match(authority_match);
        let ceiling = authority([fixture.evidence.clone(), fixture.deploy.clone()]);
        Kernel::admit(
            definition_id("edge-authority-match"),
            fixture.schema,
            fixture.graph,
            fixture.contracts,
            fixture.definitions,
            fixture.edge_definitions,
            [],
            [source_root(ceiling)],
        )
        .expect("definition")
    }

    fn proposal(authority: Authority) -> ActivationProposal {
        let mut proposal = ActivationProposal::root("source", authority, payload(b"result:root"));
        proposal.emit(Emission::new(
            "source.review",
            OutputAuthority::Carry,
            payload(b"evidence:item"),
        ));
        proposal
    }

    let evidence = authority_tag("Source", "Evidence", "Review");
    let deploy = authority_tag("Source", "Deploy", "Production");
    let any = kernel(AuthorityMatch::AnyOf);
    let mut any_state = any.empty_state();
    any.activate(&mut any_state, proposal(authority([deploy.clone()])))
        .expect("one matching tag satisfies AnyOf");

    let all = kernel(AuthorityMatch::AllOf);
    let mut all_state = all.empty_state();
    let unchanged = snapshot(&all_state);
    assert!(matches!(
        all.activate(&mut all_state, proposal(authority([deploy.clone()]))),
        Err(Reject::EdgeAuthorityMismatch {
            authority_match: AuthorityMatch::AllOf,
            ..
        })
    ));
    assert_eq!(all_state, unchanged);

    all.activate(&mut all_state, proposal(authority([evidence, deploy])))
        .expect("every matching tag satisfies AllOf");
}

#[test]
fn identical_output_contents_still_create_distinct_package_occurrences() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut proposal = ActivationProposal::root("source", evidence, payload(b"result:root"));
    for _ in 0..2 {
        proposal.emit(Emission::new(
            "source.review",
            OutputAuthority::Carry,
            payload(b"evidence:identical"),
        ));
    }

    let activation_id = kernel.activate(&mut state, proposal).expect("activation");

    let mut packages = state.packages().iter();
    let (first_id, first) = packages.next().expect("first package");
    let (second_id, second) = packages.next().expect("second package");
    assert!(packages.next().is_none());
    assert_eq!(first.authority(), second.authority());
    assert_eq!(first.content_digest(), second.content_digest());
    assert_eq!(first.holder(), second.holder());
    assert_ne!(first_id, second_id);
    assert_eq!(first, second);
    assert_eq!(
        state
            .activation(activation_id)
            .expect("activation")
            .outputs()
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([*first_id, *second_id])
    );
}

#[test]
fn live_output_rejection_follows_emission_order() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let unchanged = snapshot(&state);

    let mut wrong_source_first =
        ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    wrong_source_first.emit(Emission::new(
        "review.source",
        OutputAuthority::Carry,
        payload(b"request:first"),
    ));
    wrong_source_first.emit(Emission::new(
        "missing.edge",
        OutputAuthority::Carry,
        payload(b"evidence:second"),
    ));
    assert!(matches!(
        kernel.activate(&mut state, wrong_source_first),
        Err(Reject::WrongSource { edge_id, .. }) if &*edge_id == "review.source"
    ));

    let mut unknown_first = ActivationProposal::root("source", evidence, payload(b"result:root"));
    unknown_first.emit(Emission::new(
        "missing.edge",
        OutputAuthority::Carry,
        payload(b"evidence:first"),
    ));
    unknown_first.emit(Emission::new(
        "review.source",
        OutputAuthority::Carry,
        payload(b"request:second"),
    ));
    assert!(matches!(
        kernel.activate(&mut state, unknown_first),
        Err(Reject::UnknownEdge { edge_id }) if &*edge_id == "missing.edge"
    ));
    assert_eq!(state, unchanged);
}

#[test]
fn identical_contract_content_is_proven_once_per_operation() {
    let Fixture {
        schema,
        graph,
        mut contracts,
        definitions,
        edge_definitions,
        evidence,
        ..
    } = make_fixture();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed_calls = Arc::clone(&calls);
    contracts.retain(|contract| contract.id() != "evidence");
    contracts.push(
        Contract::new("evidence", "Evidence", move |bytes| {
            observed_calls.fetch_add(1, Ordering::SeqCst);
            bytes
                .starts_with(b"evidence:")
                .then_some(())
                .ok_or_else(|| ContractViolation::new("wrong prefix"))
        })
        .expect("counted evidence contract"),
    );
    let governing = authority([evidence]);
    let kernel = Kernel::admit(
        definition_id("proof-cache"),
        schema,
        graph,
        contracts,
        definitions,
        edge_definitions,
        [],
        [source_root(governing.clone())],
    )
    .expect("kernel");
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", governing, payload(b"result:root"));
    for _ in 0..2 {
        root.emit(Emission::new(
            "source.review",
            OutputAuthority::Carry,
            payload(b"evidence:shared"),
        ));
    }

    kernel.activate(&mut state, root).expect("live activation");
    assert_eq!(calls.load(Ordering::SeqCst), 1);

    calls.store(0, Ordering::SeqCst);
    let restored = kernel
        .restore_state(
            state.into_parts().expect("fixed-graph history"),
            &payload_evidence!(b"evidence:shared"),
        )
        .expect("restored state");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(restored.packages().len(), 2);
}

#[test]
fn content_digest_is_stable_domain_separated_and_round_trippable() {
    let digest = ContentDigest::compute(b"hello");

    assert_eq!(
        digest.to_string(),
        "baa9b6540816d6581cb58ffa29fcd1bd9c94b2ca114b61268b5c628dad3c39f4"
    );
    assert!(digest.verifies(b"hello"));
    assert!(!digest.verifies(b"hello!"));
    assert_eq!(
        ContentDigest::from_bytes(*digest.as_bytes()),
        ContentDigest::compute(b"hello")
    );
}

#[test]
fn accepted_package_records_drop_distinct_emission_bytes() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    let emitted = payload(b"evidence:retained-only-externally");
    let emitted_weak = Arc::downgrade(&emitted);
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        Arc::clone(&emitted),
    ));
    drop(emitted);

    let activation_id = kernel.activate(&mut state, root).expect("root");
    assert!(
        emitted_weak.upgrade().is_none(),
        "accepted package records retained distinct emission bytes"
    );
    let expected = digest(b"evidence:retained-only-externally");
    let package_id = only_package_id(&state);
    assert_eq!(
        state.package(package_id).expect("package").content_digest(),
        expected
    );
    assert_eq!(
        state
            .activation(activation_id)
            .expect("activation")
            .package_outputs()[&package_id]
            .content_digest(),
        expected
    );
}

#[test]
fn branching_history_has_unique_producers_and_independent_consumers() {
    let fixture = make_fixture();
    let root_authority = authority([fixture.evidence, fixture.deploy]);
    let kernel = make_kernel([], [source_root(root_authority.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", root_authority, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:branch"),
    ));
    root.emit(Emission::new(
        "source.production",
        OutputAuthority::Carry,
        payload(b"deploy:branch"),
    ));
    let root_id = kernel.activate(&mut state, root).expect("root");
    let (review_package, _) = package_at_node(&state, "review");
    let (production_package, _) = package_at_node(&state, "production");
    let production_id = kernel
        .activate(
            &mut state,
            ActivationProposal::package(production_package, payload(b"result:production")),
        )
        .expect("production");

    assert_eq!(state.package_producer(review_package), Some(root_id));
    assert_eq!(state.package_producer(production_package), Some(root_id));
    assert_eq!(state.package_consumer(review_package), None);
    assert_eq!(
        state.package_consumer(production_package),
        Some(production_id)
    );
    assert_eq!(
        state.positions().keys().copied().collect::<BTreeSet<_>>(),
        BTreeSet::from([review_package])
    );
}

#[test]
fn occurrence_ids_do_not_alias_between_states_from_one_kernel() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut left = kernel.empty_state();
    let mut right = kernel.empty_state();

    for (state, value) in [
        (&mut left, b"evidence:left".as_slice()),
        (&mut right, b"evidence:right"),
    ] {
        let mut root =
            ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
        root.emit(Emission::new(
            "source.review",
            OutputAuthority::Carry,
            payload(value),
        ));
        kernel.activate(state, root).expect("root");
    }

    let left_package = only_package_id(&left);
    let right_package = only_package_id(&right);
    let left_activation = *left.activations().keys().next().expect("left activation");
    let right_activation = *right.activations().keys().next().expect("right activation");
    assert_ne!(left_package, right_package);
    assert_ne!(left_activation, right_activation);
    assert_eq!(
        PackageId::from_parts(left_package.producer(), left_package.output()),
        left_package
    );
    assert_eq!(
        ActivationId::from_u128(left_activation.as_u128()),
        left_activation
    );

    let unchanged = snapshot(&right);
    assert_eq!(
        kernel.activate(
            &mut right,
            ActivationProposal::package(left_package, payload(b"result:review")),
        ),
        Err(Reject::UnknownPackage {
            package_id: left_package,
        })
    );
    assert_eq!(snapshot(&right), unchanged);
}

#[test]
fn cloned_states_share_their_past_but_not_divergent_occurrences() {
    let fixture = make_fixture();
    let root_authority = authority([fixture.evidence, fixture.revise.clone()]);
    let child_authority = authority([fixture.revise]);
    let transition =
        AuthorityTransitionRule::new("review", root_authority.clone(), child_authority.clone())
            .expect("transition");
    let kernel = make_kernel([transition], [source_root(root_authority.clone())]);
    let mut common = kernel.empty_state();
    let mut root = ActivationProposal::root("source", root_authority, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:common"),
    ));
    kernel.activate(&mut common, root).expect("root");
    let common_package = only_package_id(&common);
    let mut left = common.clone();
    let mut right = common;

    for (state, value) in [
        (&mut left, b"request:left".as_slice()),
        (&mut right, b"request:right"),
    ] {
        let mut review = ActivationProposal::package(common_package, payload(b"result:reviewed"));
        review.emit(Emission::new(
            "review.source",
            OutputAuthority::Transition(child_authority.clone()),
            payload(value),
        ));
        kernel.activate(state, review).expect("review");
    }

    assert!(left.package(common_package).is_some());
    assert!(right.package(common_package).is_some());
    let left_output = *left.positions().keys().next().expect("left output");
    let right_output = *right.positions().keys().next().expect("right output");
    let left_activation = left.package_producer(left_output).expect("left producer");
    let right_activation = right
        .package_producer(right_output)
        .expect("right producer");
    assert_ne!(left_activation, right_activation);
    assert_eq!(
        left.package(left_output).expect("left package").authority(),
        right
            .package(right_output)
            .expect("right package")
            .authority()
    );
    assert_ne!(left_output, right_output);
    assert!(right.package(left_output).is_none());

    let unchanged = snapshot(&right);
    assert!(matches!(
        kernel.activate(
            &mut right,
            ActivationProposal::package(left_output, payload(b"result:source")),
        ),
        Err(Reject::UnknownPackage { package_id }) if package_id == left_output
    ));
    assert_eq!(snapshot(&right), unchanged);
}

#[test]
fn state_can_only_be_advanced_by_its_definition_identity() {
    let source = make_kernel([], [source_root(Authority::default())]);
    let other = make_kernel_with_id(
        definition_id("other"),
        [],
        [source_root(Authority::default())],
    );
    let mut state = source.empty_state();
    let unchanged = snapshot(&state);

    assert!(matches!(
        other.activate(
            &mut state,
            ActivationProposal::root("source", Authority::default(), payload(b"result:root"),),
        ),
        Err(Reject::StateMismatch {
            expected_id,
            actual_id,
            ..
        }) if expected_id == definition_id("other")
            && actual_id == definition_id("fixture")
    ));
    assert_eq!(snapshot(&state), unchanged);
}

#[test]
fn equal_definition_ids_do_not_hide_structural_mismatches() {
    let source = make_kernel([], [source_root(Authority::default())]);
    let mismatched = make_kernel_with_id(definition_id("fixture"), [], []);
    let mut state = source.empty_state();
    let unchanged = snapshot(&state);

    assert!(matches!(
        mismatched.activate(
            &mut state,
            ActivationProposal::root("source", Authority::default(), payload(b"result:root")),
        ),
        Err(Reject::StateMismatch {
            expected_id,
            actual_id,
            expected_fingerprint,
            actual_fingerprint,
        }) if expected_id == definition_id("fixture")
            && actual_id == definition_id("fixture")
            && expected_fingerprint != actual_fingerprint
    ));
    assert_eq!(snapshot(&state), unchanged);
}

#[test]
fn equivalent_kernel_instance_with_the_same_definition_id_can_advance_state() {
    let source = make_kernel([], [source_root(Authority::default())]);
    let reconstructed = make_kernel([], [source_root(Authority::default())]);
    let mut state = source.empty_state();

    reconstructed
        .activate(
            &mut state,
            ActivationProposal::root("source", Authority::default(), payload(b"result:root")),
        )
        .expect("stable definition identity");

    assert_eq!(state.definition_id(), source.id());
    assert_eq!(state.activations().len(), 1);
}

#[test]
fn definition_fingerprint_is_stable_structural_and_round_trippable() {
    let first = make_kernel([], [source_root(Authority::default())]);
    let equivalent = make_kernel_with_id(
        definition_id("fixture-alias"),
        [],
        [source_root(Authority::default())],
    );
    let mismatched = make_kernel_with_id(definition_id("fixture"), [], []);
    let mut fixture = make_fixture();
    fixture.edge_definitions[0] = EdgeDefinition::new(
        "source.review",
        ["EvidenceSubmission", "Audited"],
        ["Source"],
        ["Review"],
        "evidence",
        [fixture.evidence.clone()],
    )
    .expect("changed edge definition");
    let edge_mismatched = Kernel::admit(
        definition_id("fixture"),
        fixture.schema,
        fixture.graph,
        fixture.contracts,
        fixture.definitions,
        fixture.edge_definitions,
        [],
        [source_root(Authority::default())],
    )
    .expect("changed kernel");
    let mut fixture = make_fixture();
    fixture.edge_definitions[0] = fixture.edge_definitions[0]
        .clone()
        .with_authority_match(AuthorityMatch::AllOf);
    let match_mismatched = Kernel::admit(
        definition_id("fixture"),
        fixture.schema,
        fixture.graph,
        fixture.contracts,
        fixture.definitions,
        fixture.edge_definitions,
        [],
        [source_root(Authority::default())],
    )
    .expect("changed authority match");

    assert_eq!(first.fingerprint(), equivalent.fingerprint());
    assert_ne!(first.fingerprint(), mismatched.fingerprint());
    assert_ne!(first.fingerprint(), edge_mismatched.fingerprint());
    assert_ne!(first.fingerprint(), match_mismatched.fingerprint());

    let bytes = *first.fingerprint().as_bytes();
    assert_eq!(DefinitionFingerprint::from_bytes(bytes).as_bytes(), &bytes);
}

#[test]
fn state_round_trips_through_parts_and_an_equivalent_reconstructed_kernel() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let source = make_kernel([], [source_root(evidence.clone())]);
    let mut state = source.empty_state();
    let mut root = ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:persisted"),
    ));
    source.activate(&mut state, root).expect("root");
    let package_id = only_package_id(&state);
    let definition_id = state.definition_id().clone();
    let fingerprint = *state.definition_fingerprint();
    let expected = state.clone();
    let parts = state.into_parts().expect("fixed-graph history");
    drop(source);

    let reconstructed = make_kernel([], [source_root(evidence)]);
    let mut restored = reconstructed
        .restore_state(parts, &payload_evidence!(b"evidence:persisted"))
        .expect("reconstruct state");
    assert_eq!(restored.definition_id(), &definition_id);
    assert_eq!(restored.definition_fingerprint(), &fingerprint);
    assert_eq!(restored, expected);

    reconstructed
        .activate(
            &mut restored,
            ActivationProposal::package(package_id, payload(b"result:reviewed")),
        )
        .expect("continue from reconstructed state");
    assert!(restored.is_quiescent());
}

#[test]
fn deep_static_cycle_restores_as_a_linear_occurrence_history() {
    let fixture = make_fixture();
    let capacity = authority([fixture.evidence, fixture.revise]);
    let kernel = make_kernel([], [source_root(capacity.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", capacity, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:initial"),
    ));
    let root_id = kernel.activate(&mut state, root).expect("root");
    let mut next = state
        .activation(root_id)
        .expect("root activation")
        .outputs()
        .next()
        .expect("root output");

    for _ in 0..512 {
        let package = state.package(next).expect("pending package");
        let (edge, message) = match package.holder() {
            "review" => ("review.source", b"request:return".as_slice()),
            "source" => ("source.review", b"evidence:again".as_slice()),
            node => panic!("unexpected cycle node {node}"),
        };
        let mut proposal = ActivationProposal::package(next, payload(b"result:step"));
        proposal.emit(Emission::new(
            edge,
            OutputAuthority::Carry,
            payload(message),
        ));
        let activation_id = kernel.activate(&mut state, proposal).expect("cycle step");
        next = state
            .activation(activation_id)
            .expect("step activation")
            .outputs()
            .next()
            .expect("step output");
    }

    let expected = state.clone();
    let restored = kernel
        .restore_state(
            state.into_parts().expect("fixed-graph history"),
            &payload_evidence!(b"evidence:initial", b"request:return", b"evidence:again",),
        )
        .expect("deep history restores");
    assert_eq!(restored, expected);
    assert_eq!(
        restored
            .positions()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([next])
    );
}

#[test]
#[ignore = "wide-fan-out scalability probe; run explicitly in release mode"]
fn wide_fan_out_restoration_probe() {
    const WIDTH: usize = 50_000;

    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    for _ in 0..WIDTH {
        root.emit(Emission::new(
            "source.review",
            OutputAuthority::Carry,
            payload(b"evidence:wide"),
        ));
    }
    kernel.activate(&mut state, root).expect("wide root");

    let restored = kernel
        .restore_state(
            state.into_parts().expect("fixed-graph history"),
            &payload_evidence!(b"evidence:wide"),
        )
        .expect("wide history restores");
    assert_eq!(restored.activations().len(), 1);
    assert_eq!(restored.packages().len(), WIDTH);
    assert_eq!(restored.positions().len(), WIDTH);
}

#[test]
fn restoration_rejects_equal_definition_ids_with_different_fingerprints() {
    let source = make_kernel([], [source_root(Authority::default())]);
    let state = source.empty_state();
    let mismatched = make_kernel([], []);

    assert!(matches!(
        mismatched.restore_state(
            state.into_parts().expect("fixed-graph history"),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::DefinitionMismatch {
            expected_id,
            actual_id,
            expected_fingerprint,
            actual_fingerprint,
        }) if expected_id == actual_id && expected_fingerprint != actual_fingerprint
    ));
}

#[test]
fn restoration_rejects_package_ids_owned_by_another_activation() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:owned"),
    ));
    let activation_id = kernel.activate(&mut state, root).expect("root");
    let record = state.activation(activation_id).expect("activation");
    let (package_id, output) = record.package_outputs().iter().next().expect("output");
    let other = ActivationId::from_u128(activation_id.as_u128() ^ 1);
    let forged_package_id = PackageId::from_parts(other, package_id.output());
    let forged = Activation::new(
        record.node_id(),
        record.trigger().clone(),
        Arc::clone(record.result()),
        BTreeMap::from([(forged_package_id, output.clone())]),
    );

    assert!(matches!(
        kernel.restore_state(
            state_parts_with(
                &kernel,
                BTreeMap::from([(activation_id, forged)]),
            ),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id: invalid,
            source,
        }) if invalid == activation_id
            && matches!(
                &*source,
                Reject::InvalidPackageIdentity {
                    package_id,
                    activation_id: owner,
                } if *owner == activation_id && *package_id == forged_package_id
            )
    ));
}

#[test]
fn restoration_rejects_a_trigger_with_a_missing_producer() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence)]);
    let producer_id = ActivationId::from_u128(101);
    let child_id = ActivationId::from_u128(102);
    let package_id = PackageId::from_parts(producer_id, 1);
    let child = Activation::new(
        "review",
        Trigger::Pkgs {
            package_ids: BTreeSet::from([package_id]),
        },
        payload(b"result:child"),
        BTreeMap::new(),
    );

    assert!(matches!(
        kernel.restore_state(
            state_parts_with(&kernel, BTreeMap::from([(child_id, child)])),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id,
            source,
        }) if activation_id == child_id
            && matches!(&*source, Reject::UnknownPackage { package_id: unknown } if *unknown == package_id)
    ));
}

#[test]
fn restoration_rejects_a_trigger_missing_from_its_existing_producer() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let producer_id = ActivationId::from_u128(201);
    let child_id = ActivationId::from_u128(202);
    let package_id = PackageId::from_parts(producer_id, 1);
    let producer = Activation::new(
        "source",
        Trigger::Orig {
            node_id: Arc::from("source"),
            authority: evidence,
        },
        payload(b"result:root"),
        BTreeMap::new(),
    );
    let child = Activation::new(
        "review",
        Trigger::Pkgs {
            package_ids: BTreeSet::from([package_id]),
        },
        payload(b"result:child"),
        BTreeMap::new(),
    );

    assert!(matches!(
        kernel.restore_state(
            state_parts_with(
                &kernel,
                BTreeMap::from([(producer_id, producer), (child_id, child)]),
            ),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id,
            source,
        }) if activation_id == child_id
            && matches!(&*source, Reject::UnknownPackage { package_id: unknown } if *unknown == package_id)
    ));
}

#[test]
fn restoration_rejects_invalid_carried_authority() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence.clone()]);
    let deploy = authority([fixture.deploy]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:authority"),
    ));
    let activation_id = kernel.activate(&mut state, root).expect("root");
    let record = state.activation(activation_id).expect("activation");
    let (package_id, output) = record.package_outputs().iter().next().expect("output");

    let forged_output = Output::new(
        output.edge_id().expect("delivered edge"),
        output.object_type(),
        deploy,
        output.content_digest(),
    );
    let forged = Activation::new(
        record.node_id(),
        record.trigger().clone(),
        Arc::clone(record.result()),
        BTreeMap::from([(*package_id, forged_output)]),
    );
    assert!(matches!(
        kernel.restore_state(
            state_parts_with(
                &kernel,
                BTreeMap::from([(activation_id, forged)]),
            ),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id: invalid,
            source,
        }) if invalid == activation_id
            && matches!(&*source, Reject::UnauthorizedAuthorityTransition { .. })
    ));
}

#[test]
fn restoration_rejects_duplicate_consumers_and_causal_cycles() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:shared"),
    ));
    let root_id = kernel.activate(&mut state, root).expect("root");
    let package_id = only_package_id(&state);
    let first = ActivationId::from_u128(root_id.as_u128() ^ 1);
    let second = ActivationId::from_u128(root_id.as_u128() ^ 2);
    let consumer = |id| {
        (
            id,
            Activation::new(
                "review",
                Trigger::Pkgs {
                    package_ids: BTreeSet::from([package_id]),
                },
                payload(b"result:reviewed"),
                BTreeMap::new(),
            ),
        )
    };
    let mut duplicate = state.activations().clone();
    duplicate.extend([consumer(first), consumer(second)]);
    assert!(matches!(
        kernel.restore_state(
            state_parts_with(&kernel, duplicate),
            &payload_evidence!(b"evidence:shared"),
        ),
        Err(StateRestoreError::DuplicateConsumer { package_id: duplicate })
            if duplicate == package_id
    ));

    let left = ActivationId::from_u128(101);
    let right = ActivationId::from_u128(202);
    let left_package = PackageId::from_parts(left, 1);
    let right_package = PackageId::from_parts(right, 1);
    let left_record = Activation::new(
        "review",
        Trigger::Pkgs {
            package_ids: BTreeSet::from([right_package]),
        },
        payload(b"result:left"),
        BTreeMap::from([(
            left_package,
            Output::new(
                "source.review",
                "Evidence",
                Authority::default(),
                digest(b"evidence:left"),
            ),
        )]),
    );
    let right_record = Activation::new(
        "review",
        Trigger::Pkgs {
            package_ids: BTreeSet::from([left_package]),
        },
        payload(b"result:right"),
        BTreeMap::from([(
            right_package,
            Output::new(
                "source.review",
                "Evidence",
                Authority::default(),
                digest(b"evidence:right"),
            ),
        )]),
    );
    assert!(matches!(
        kernel.restore_state(
            state_parts_with(
                &kernel,
                BTreeMap::from([(left, left_record), (right, right_record)]),
            ),
            &BTreeMap::new(),
        ),
        Err(StateRestoreError::CausalCycle { .. })
    ));
}

#[test]
fn restoration_revalidates_package_edge_payloads() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:valid"),
    ));
    let activation_id = kernel.activate(&mut state, root).expect("root");
    let record = state.activation(activation_id).expect("activation");
    let (package_id, output) = record.package_outputs().iter().next().expect("output");
    let invalid_output = Output::new(
        output.edge_id().expect("delivered edge"),
        output.object_type(),
        output.authority().clone(),
        digest(b"not-evidence"),
    );
    let forged = Activation::new(
        record.node_id(),
        record.trigger().clone(),
        Arc::clone(record.result()),
        BTreeMap::from([(*package_id, invalid_output)]),
    );

    assert!(matches!(
        kernel.restore_state(
            state_parts_with(
                &kernel,
                BTreeMap::from([(activation_id, forged)]),
            ),
            &payload_evidence!(b"not-evidence"),
        ),
        Err(StateRestoreError::InvalidActivation {
            activation_id: invalid,
            source,
        }) if invalid == activation_id
            && matches!(&*source, Reject::PayloadContract { .. })
    ));
}

#[test]
fn restoration_requires_bytes_matching_each_package_commitment() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:external"),
    ));
    kernel.activate(&mut state, root).expect("root");
    let package_id = only_package_id(&state);
    let expected = digest(b"evidence:external");
    let parts = state.into_parts().expect("fixed-graph history");

    assert_eq!(
        kernel.restore_state(parts.clone(), &BTreeMap::new()),
        Err(StateRestoreError::MissingPayloadEvidence {
            package_id,
            content_digest: expected,
        })
    );

    let wrong_payload = payload(b"evidence:different");
    let actual = ContentDigest::compute(&wrong_payload);
    assert_eq!(
        kernel.restore_state(parts.clone(), &BTreeMap::from([(expected, wrong_payload)])),
        Err(StateRestoreError::PayloadEvidenceMismatch {
            package_id,
            expected,
            actual,
        })
    );

    let restored = kernel
        .restore_state(parts, &payload_evidence!(b"evidence:external"))
        .expect("matching external evidence restores");
    assert_eq!(
        restored
            .package(package_id)
            .expect("package")
            .content_digest(),
        expected
    );
}

#[test]
fn restoration_rejects_a_recorded_node_that_disagrees_with_its_trigger() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut root = ActivationProposal::root("source", evidence, payload(b"result:root"));
    root.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"evidence:node"),
    ));
    let root_id = kernel.activate(&mut state, root).expect("root");
    let package_id = only_package_id(&state);
    let review_id = kernel
        .activate(
            &mut state,
            ActivationProposal::package(package_id, payload(b"result:reviewed")),
        )
        .expect("review");
    let payloads = payload_evidence!(b"evidence:node");
    assert_eq!(
        kernel
            .restore_state(state.to_parts().expect("fixed-graph history"), &payloads)
            .expect("untampered history restores"),
        state
    );

    // A root's trigger names its node; a package trigger implies its inputs'
    // receiver. Each recorded node is checked against the implied one.
    for (activation_id, declared, actual) in [
        (root_id, "review", "source"),
        (review_id, "source", "review"),
    ] {
        let mut activations = state.activations().clone();
        let record = &activations[&activation_id];
        let forged = Activation::new(
            declared,
            record.trigger().clone(),
            Arc::clone(record.result()),
            record.package_outputs().clone(),
        );
        activations.insert(activation_id, forged);
        assert_eq!(
            kernel.restore_state(state_parts_with(&kernel, activations), &payloads),
            Err(StateRestoreError::InvalidActivation {
                activation_id,
                source: Box::new(Reject::ExecutionNodeMismatch {
                    declared: Arc::from(declared),
                    actual: Arc::from(actual),
                }),
            })
        );
    }
}

#[test]
fn live_and_restored_records_share_the_same_rejection_reason() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence]);
    let kernel = make_kernel([], [source_root(evidence.clone())]);
    let mut state = kernel.empty_state();
    let mut proposal =
        ActivationProposal::root("source", evidence.clone(), payload(b"result:root"));
    proposal.emit(Emission::new(
        "source.review",
        OutputAuthority::Carry,
        payload(b"not-evidence"),
    ));
    let live_rejection = kernel
        .activate(&mut state, proposal)
        .expect_err("live payload is invalid");

    let activation_id = ActivationId::from_u128(77);
    let package_id = PackageId::from_parts(activation_id, 1);
    let record = Activation::new(
        "source",
        Trigger::Orig {
            node_id: Arc::from("source"),
            authority: evidence.clone(),
        },
        payload(b"result:root"),
        BTreeMap::from([(
            package_id,
            Output::new(
                "source.review",
                "Evidence",
                evidence,
                digest(b"not-evidence"),
            ),
        )]),
    );
    let restored_rejection = kernel
        .restore_state(
            state_parts_with(&kernel, BTreeMap::from([(activation_id, record)])),
            &payload_evidence!(b"not-evidence"),
        )
        .expect_err("restored payload is invalid");

    assert!(matches!(
        restored_rejection,
        StateRestoreError::InvalidActivation {
            activation_id: invalid,
            source,
        } if invalid == activation_id && *source == live_rejection
    ));
}

#[test]
fn authority_transition_rules_are_sorted_and_deduplicated() {
    let fixture = make_fixture();
    let evidence = authority([fixture.evidence.clone()]);
    let deploy = authority([fixture.deploy.clone()]);
    let amplify = AuthorityTransitionRule::new("source", evidence.clone(), deploy.clone())
        .expect("transition");
    let attenuate = AuthorityTransitionRule::new("source", deploy, evidence).expect("transition");
    let fixture = make_fixture();
    let kernel = Kernel::admit(
        definition_id("canonical"),
        fixture.schema,
        fixture.graph,
        fixture.contracts,
        fixture.definitions,
        fixture.edge_definitions,
        [amplify.clone(), attenuate.clone(), amplify.clone()],
        [],
    )
    .expect("definition");

    let mut expected = vec![amplify, attenuate];
    expected.sort_unstable();
    assert_eq!(kernel.authority_transitions(), expected);
}

#[test]
fn contract_rejection_and_panic_leave_activation_atomic() {
    let ordered_output_calls = Arc::new(AtomicUsize::new(0));
    let observed_output_calls = Arc::clone(&ordered_output_calls);
    let schema = Schema::new(
        ["Source", "Target"],
        ["Result", "Item"],
        [
            authority_tag("Source", "Item", "Target"),
            authority_tag("Target", "Item", "Source"),
        ],
    )
    .expect("schema");
    let graph = Graph::new(
        [
            Node::new("source").expect("source"),
            Node::new("target").expect("target"),
        ],
        [
            Edge::new("route", "source", "target").expect("route edge"),
            Edge::new("return", "target", "source").expect("return edge"),
        ],
    )
    .expect("graph");
    let contracts = [
        Contract::new("result", "Result", |bytes| {
            assert_ne!(bytes, b"panic-result", "result panic");
            Ok(())
        })
        .expect("result"),
        Contract::new("item", "Item", move |bytes| {
            assert_ne!(bytes, b"panic-output", "output panic");
            if bytes.starts_with(b"ordered-output-")
                && observed_output_calls.fetch_add(1, Ordering::SeqCst) == 1
            {
                panic!("later output panic");
            }
            Ok(())
        })
        .expect("item"),
    ];
    let definitions = [
        NodeDefinition::new("source", ["Source"], "result").expect("source"),
        NodeDefinition::new("target", ["Target"], "result").expect("target"),
    ];
    let edge_definitions = [
        EdgeDefinition::new(
            "route",
            ["Item"],
            ["Source"],
            ["Target"],
            "item",
            [authority_tag("Source", "Item", "Target")],
        )
        .expect("route definition"),
        EdgeDefinition::new(
            "return",
            ["Item"],
            ["Target"],
            ["Source"],
            "item",
            [authority_tag("Target", "Item", "Source")],
        )
        .expect("return definition"),
    ];
    let route = authority([
        authority_tag("Source", "Item", "Target"),
        authority_tag("Target", "Item", "Source"),
    ]);
    let kernel = Kernel::admit(
        definition_id("panic-contract"),
        schema,
        graph,
        contracts,
        definitions,
        edge_definitions,
        [],
        [source_root(route.clone())],
    )
    .expect("kernel");
    let mut state = kernel.empty_state();
    let unchanged = snapshot(&state);

    let result_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = kernel.activate(
            &mut state,
            ActivationProposal::root("source", route.clone(), payload(b"panic-result")),
        );
    }));
    assert!(result_panic.is_err());
    assert_eq!(snapshot(&state), unchanged);

    let mut proposal =
        ActivationProposal::root("source", route.clone(), payload(b"result:accepted"));
    proposal.emit(Emission::new(
        "route",
        OutputAuthority::Carry,
        payload(b"valid"),
    ));
    proposal.emit(Emission::new(
        "route",
        OutputAuthority::Carry,
        payload(b"panic-output"),
    ));
    let output_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = kernel.activate(&mut state, proposal);
    }));
    assert!(output_panic.is_err());
    assert_eq!(snapshot(&state), unchanged);

    let mut root = ActivationProposal::root("source", route, payload(b"result:accepted-root"));
    root.emit(Emission::new(
        "route",
        OutputAuthority::Carry,
        payload(b"valid-package"),
    ));
    kernel.activate(&mut state, root).expect("accepted root");
    let package_id = *state.positions().keys().next().expect("pending package");
    let unchanged = snapshot(&state);

    let result_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = kernel.activate(
            &mut state,
            ActivationProposal::package(package_id, payload(b"panic-result")),
        );
    }));
    assert!(result_panic.is_err());
    assert_eq!(snapshot(&state), unchanged);

    let mut proposal = ActivationProposal::package(package_id, payload(b"result:accepted-package"));
    proposal.emit(Emission::new(
        "return",
        OutputAuthority::Carry,
        payload(b"ordered-output-1"),
    ));
    proposal.emit(Emission::new(
        "return",
        OutputAuthority::Carry,
        payload(b"ordered-output-2"),
    ));
    let output_panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = kernel.activate(&mut state, proposal);
    }));
    assert!(output_panic.is_err());
    assert_eq!(ordered_output_calls.load(Ordering::SeqCst), 2);
    assert_eq!(snapshot(&state), unchanged);
}
