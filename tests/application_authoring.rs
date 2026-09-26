//! Declaration rules shared by the builder and both declarative formats.

use std::collections::BTreeMap;
use std::path::Path;
use std::sync::Arc;

use ontography::project::{
    BoundComponent, ComponentBindings, ComponentDescription, ComponentProvider, ProjectComponent,
    ProjectError, ProjectRegistry,
};
use ontography::{
    ApplicationConfig, ApplicationConfigError, ApplicationContext, ApplicationError,
    ApplicationRegistry, Authority, AuthorityMatch, AuthorityTag, Contract, IngressMode,
};
use serde_json::Value;

struct IdleComponent;

impl ProjectComponent for IdleComponent {
    fn description(&self) -> ComponentDescription {
        ComponentDescription {
            identity: "idle".into(),
            description: "does nothing".into(),
            types: vec!["Node".into()],
            result_contract: "result".into(),
            inputs: BTreeMap::from([("in".to_owned(), "result".to_owned())]),
            outputs: BTreeMap::from([("out".to_owned(), "result".to_owned())]),
            dynamic_inputs: false,
            dynamic_outputs: false,
            ingress_modes: vec![IngressMode::Any, IngressMode::All],
            configuration_schema: None,
        }
    }

    fn bind(&self, config: Value, _: &ComponentBindings) -> Result<BoundComponent, String> {
        Ok(BoundComponent {
            kind: "idle".into(),
            config,
        })
    }
}

struct IdleProvider;

impl ComponentProvider for IdleProvider {
    fn load(
        &self,
        specs: &BTreeMap<String, Value>,
        _: &Path,
        _: &mut ApplicationRegistry,
    ) -> Result<BTreeMap<String, Arc<dyn ProjectComponent>>, String> {
        Ok(specs
            .keys()
            .map(|alias| {
                (
                    alias.clone(),
                    Arc::new(IdleComponent) as Arc<dyn ProjectComponent>,
                )
            })
            .collect())
    }
}

fn registry() -> ApplicationRegistry {
    let mut registry = ApplicationRegistry::new();
    registry
        .register_contract(Contract::new("result", "Result", |_| Ok(())).unwrap())
        .unwrap();
    registry
        .register_node_implementation("idle", |_: Value| {
            Ok::<_, String>(|_: ApplicationContext| async { Ok(()) })
        })
        .unwrap();
    registry
}

fn projects() -> ProjectRegistry {
    let mut projects = ProjectRegistry::new(registry());
    projects
        .register_provider("test", Arc::new(IdleProvider))
        .unwrap();
    projects
}

#[test]
fn root_authority_outside_the_entry_is_rejected_by_both_declarative_formats() {
    let native = r#"{
        "id":"native", "entry":"a",
        "node_definitions":{"rooted":{
            "types":["Node"], "result_contract":"result", "root_authority":[],
            "implementation":{"kind":"idle"}
        }},
        "edge_definitions":{},
        "nodes":{"a":{"definition":"rooted"}, "b":{"definition":"rooted"}},
        "edges":{}
    }"#;
    let error = registry()
        .build(ApplicationConfig::from_json(native).unwrap())
        .unwrap_err();
    assert!(matches!(
        &error,
        ApplicationConfigError::RootAuthorityOutsideEntry { node_id, definition }
            if node_id == "b" && definition == "rooted"
    ));

    let project = r#"{
        "id":"project", "entry":"a",
        "components":{"idle":{"provider":"test"}},
        "nodes":{
            "a":{"component":"idle", "root_authority":[]},
            "b":{"component":"idle", "root_authority":[]}
        },
        "connections":[]
    }"#;
    let root = tempfile::tempdir().unwrap();
    let error = projects().prepare(project, root.path()).unwrap_err();
    assert!(matches!(
        &error,
        ProjectError::Application(ApplicationConfigError::RootAuthorityOutsideEntry {
            node_id,
            definition,
        }) if node_id == "b" && definition == "node:b"
    ));
}

#[test]
fn project_entry_without_root_authority_fails_through_the_builder() {
    let project = r#"{
        "id":"project", "entry":"a",
        "components":{"idle":{"provider":"test"}},
        "nodes":{"a":{"component":"idle"}},
        "connections":[]
    }"#;
    let root = tempfile::tempdir().unwrap();
    let error = projects().prepare(project, root.path()).unwrap_err();
    assert!(matches!(
        error,
        ProjectError::Application(ApplicationConfigError::Application(
            ApplicationError::MissingRootAuthority
        ))
    ));
}

#[test]
fn project_vocabulary_compiles_through_the_shared_native_syntax() {
    let project = r#"{
        "id":"project", "entry":"a",
        "components":{"idle":{"provider":"test"}},
        "nodes":{
            "a":{"component":"idle", "root_authority":["run"], "ingress_mode":"all",
                 "authority_transitions":[{"from":["run"], "add":["extra"]}]},
            "b":{"component":"idle", "config":{"depth":1}}
        },
        "connections":[{
            "id":"flow", "from":["a","out"], "to":["b","in"],
            "authority_tags":["run","extra"], "authority_match":"all_of"
        }]
    }"#;
    let root = tempfile::tempdir().unwrap();
    let prepared = projects().prepare(project, root.path()).unwrap();
    let kernel = prepared.application.kernel();
    assert_eq!(
        kernel.node_definition("a").unwrap().ingress_mode(),
        IngressMode::All
    );
    assert_eq!(
        kernel.edge_definition("flow").unwrap().authority_match(),
        AuthorityMatch::AllOf
    );
    let transition = &kernel.authority_transitions()[0];
    assert_eq!(transition.node_id(), "a");
    assert_eq!(
        *transition.to(),
        Authority::new([
            AuthorityTag::new("run").unwrap(),
            AuthorityTag::new("extra").unwrap()
        ])
    );
    let expanded: Value = serde_json::from_str(&prepared.application_json).unwrap();
    assert_eq!(
        expanded["node_definitions"]["node:a"]["ingress_mode"],
        "all"
    );
    assert_eq!(
        expanded["edge_definitions"]["edge:flow"]["authority_match"],
        "all_of"
    );
    assert_eq!(
        expanded["node_definitions"]["node:b"]["implementation"]["config"]["depth"],
        1
    );

    let duplicated = project.replace(r#"{"depth":1}"#, r#"{"depth":1,"depth":2}"#);
    let error = projects().prepare(&duplicated, root.path()).unwrap_err();
    assert!(
        error.to_string().contains("duplicate JSON key \"depth\""),
        "{error}"
    );
}
