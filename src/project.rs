//! Component discovery and concise project declarations compiled to native applications.
//!
//! Providers adapt implementation families to the existing registry. This module
//! resolves declarations and bindings; it does not install environments, run
//! components, infer authority, or impose a payload protocol on implementations.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use serde::de::{MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::{Value, json};
use thiserror::Error;

use crate::config::deserialize_unique_string_map;
use crate::{
    Application, ApplicationConfig, ApplicationConfigError, ApplicationRegistry, IngressMode,
};

/// Inspectable facts about one component, supplied by its trusted provider.
///
/// A contract ID names a registry contract, which may use arbitrary trusted Rust
/// validation. Optional JSON schemas are descriptive and do not replace those
/// validators. A connection with two dynamic ports requires an explicit contract.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct ComponentDescription {
    /// Provider-defined component identity; this is not necessarily a code pin.
    pub identity: String,
    /// Human-readable behavior and purpose.
    pub description: String,
    /// Native type annotations assigned to every placement of this component.
    pub types: Vec<String>,
    /// Registered contract for activation results.
    pub result_contract: String,
    /// Declared incoming port names and their exact registered contract IDs.
    pub inputs: BTreeMap<String, String>,
    /// Declared outgoing port names and their exact registered contract IDs.
    pub outputs: BTreeMap<String, String>,
    /// Whether additional input port names are supported.
    pub dynamic_inputs: bool,
    /// Whether additional output port names are supported.
    pub dynamic_outputs: bool,
    /// Ingress modes the implementation actually supports.
    #[serde(
        serialize_with = "serialize_ingress_modes",
        deserialize_with = "deserialize_ingress_modes"
    )]
    pub ingress_modes: Vec<IngressMode>,
    /// Optional descriptive configuration schema.
    pub configuration_schema: Option<Value>,
}

/// Concrete graph connections passed to an implementation's binder.
#[derive(Clone, Debug)]
pub struct ComponentBindings {
    /// Concrete node placement identity.
    pub node_id: String,
    /// Incoming named ports mapped to concrete edge IDs.
    pub inputs: BTreeMap<String, Vec<String>>,
    /// Outgoing named ports mapped to concrete edge IDs.
    pub outputs: BTreeMap<String, Vec<String>>,
    /// Explicitly selected native ingress mode.
    pub ingress_mode: IngressMode,
    /// Whether this placement is the application's entry.
    pub is_entry: bool,
}

/// Native executable selection and its configuration after graph binding.
#[derive(Clone, Debug)]
pub struct BoundComponent {
    /// Trusted registry implementation kind.
    pub kind: String,
    /// Opaque configuration understood by that implementation.
    pub config: Value,
}

/// A loaded component that can describe and bind its implementation.
pub trait ProjectComponent: Send + Sync {
    /// Returns inspectable component facts without launching the component.
    fn description(&self) -> ComponentDescription;

    /// Converts user configuration and graph connections to native configuration.
    ///
    /// # Errors
    ///
    /// Returns an actionable explanation when configuration or bindings are
    /// unsupported. This operation must not launch workloads or prepare state.
    fn bind(&self, config: Value, bindings: &ComponentBindings) -> Result<BoundComponent, String>;
}

/// Trusted adapter for a family of components.
pub trait ComponentProvider: Send + Sync {
    /// Loads and registers the requested component specifications as one batch.
    ///
    /// Keys are project component aliases. Specifications retain their `provider`
    /// field; the provider validates all of its remaining fields and resolves
    /// relative resources against `project_root`. Shared contracts can be
    /// registered once for the whole batch. The registry is isolated to this
    /// preparation and is discarded if any component fails.
    ///
    /// # Errors
    ///
    /// Returns an explanation for an invalid specification or unavailable
    /// component. Loading must not start workloads or install dependencies.
    fn load(
        &self,
        specs: &BTreeMap<String, Value>,
        project_root: &Path,
        registry: &mut ApplicationRegistry,
    ) -> Result<BTreeMap<String, Arc<dyn ProjectComponent>>, String>;
}

/// One concise project, before implementation resolution.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectConfig {
    /// Native application definition identity.
    pub id: String,
    /// Concrete entry node; only this node receives root authority and input.
    pub entry: String,
    /// Component aliases and provider-owned specifications.
    #[serde(deserialize_with = "deserialize_unique_string_map")]
    pub components: BTreeMap<String, Value>,
    /// Configured node placements.
    #[serde(deserialize_with = "deserialize_unique_string_map")]
    pub nodes: BTreeMap<String, ProjectNode>,
    /// Explicit port-to-port connections, each declared once.
    pub connections: Vec<ProjectConnection>,
}

impl ProjectConfig {
    /// Parses a closed project declaration, rejecting duplicate keys at any depth.
    ///
    /// # Errors
    ///
    /// Returns a parse error for unknown declaration fields, duplicate JSON keys,
    /// malformed endpoints, or an invalid field shape.
    pub fn from_json(document: &str) -> Result<Self, ProjectError> {
        // Value-based component specs would otherwise silently lose duplicate
        // keys before a provider can validate its own closed specification.
        let _: UniqueJson = serde_json::from_str(document)?;
        Ok(serde_json::from_str(document)?)
    }
}

/// A component instance with its explicit application policy.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectNode {
    /// Alias in the project's component map.
    pub component: String,
    /// Implementation-owned user configuration.
    #[serde(default)]
    pub config: Value,
    /// Host-enforced context selection, exploration, and resource access.
    #[serde(default)]
    pub context: crate::ContextPolicy,
    /// Explicit root authority for the entry node. Other nodes cannot set this.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub root_authority: Option<Vec<String>>,
    /// Selected ingress semantics; defaults to singleton processing.
    #[serde(
        default,
        deserialize_with = "deserialize_ingress",
        serialize_with = "serialize_ingress"
    )]
    pub ingress_mode: IngressMode,
    /// Explicit authority transformations this placement may perform.
    #[serde(default)]
    pub authority_transitions: Vec<ProjectAuthorityTransition>,
}

/// One exact authority transition, using the native declaration's syntax.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectAuthorityTransition {
    /// Exact starting authority.
    pub from: Vec<String>,
    /// Exact replacement authority; mutually exclusive with add and remove.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub to: Option<Vec<String>>,
    /// Tags added to from; mutually exclusive with to and remove.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub add: Option<Vec<String>>,
    /// Tags removed from from; mutually exclusive with to and add.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub remove: Option<Vec<String>>,
}

/// A connection between two named component ports.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProjectConnection {
    /// Concrete edge identity.
    pub id: String,
    /// Source node and its output port.
    pub from: [String; 2],
    /// Target node and its input port.
    pub to: [String; 2],
    /// Explicit admission authority; no tags or grants are inferred.
    pub authority_tags: Vec<String>,
    /// How the native edge compares authority tags.
    #[serde(default)]
    pub authority_match: ProjectAuthorityMatch,
    /// Exact contract ID, required when both endpoints are dynamic.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub contract: Option<String>,
}

/// Native edge authority matching syntax in a project declaration.
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ProjectAuthorityMatch {
    /// At least one allowed tag must be carried.
    #[default]
    AnyOf,
    /// All allowed tags must be carried.
    AllOf,
}

/// A fully resolved and validated application, with inspectable preparation data.
#[derive(Debug)]
pub struct PreparedProject {
    /// Admitted native application and retained executable factories.
    pub application: Application,
    /// Deterministic, expanded native application declaration.
    pub application_json: String,
    /// Descriptions keyed by project component alias.
    pub components: BTreeMap<String, ComponentDescription>,
    /// Original provider specifications; these are references, not version locks.
    pub component_specs: BTreeMap<String, Value>,
    /// Canonical base directory against which providers resolved resources.
    pub project_root: PathBuf,
}

/// A project failed to parse, resolve, bind, or pass native validation.
#[derive(Debug, Error)]
pub enum ProjectError {
    /// The authored JSON is malformed or violates the closed project shape.
    #[error("invalid project JSON: {0}")]
    Json(#[from] serde_json::Error),
    /// A component or connection declaration could not be prepared.
    #[error("{0}")]
    Invalid(String),
    /// The expanded application failed ordinary registry or kernel validation.
    #[error(transparent)]
    Application(#[from] ApplicationConfigError),
}

/// Trusted providers plus a native registry, reusable across isolated preparations.
#[derive(Clone)]
pub struct ProjectRegistry {
    registry: ApplicationRegistry,
    providers: BTreeMap<String, Arc<dyn ComponentProvider>>,
    native_resolver: Option<Arc<NativeResolver>>,
}

type NativeResolver =
    dyn Fn(&str, &mut ApplicationRegistry) -> Result<(), String> + Send + Sync + 'static;

impl fmt::Debug for ProjectRegistry {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ProjectRegistry")
            .field("registry", &self.registry)
            .field("providers", &self.providers.keys())
            .field("native_resolver", &self.native_resolver.is_some())
            .finish()
    }
}

impl ProjectRegistry {
    /// Wraps a native registry without altering its existing build behavior.
    #[must_use]
    pub fn new(registry: ApplicationRegistry) -> Self {
        Self {
            registry,
            providers: BTreeMap::new(),
            native_resolver: None,
        }
    }

    /// Registers one trusted provider, once for this host.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty or already registered provider name.
    pub fn register_provider(
        &mut self,
        name: impl Into<String>,
        provider: Arc<dyn ComponentProvider>,
    ) -> Result<(), ProjectError> {
        let name = name.into();
        if name.trim().is_empty() {
            return Err(ProjectError::Invalid(
                "provider name cannot be empty".into(),
            ));
        }
        if self.providers.contains_key(&name) {
            return Err(ProjectError::Invalid(format!(
                "provider {name:?} is already registered"
            )));
        }
        self.providers.insert(name, provider);
        Ok(())
    }

    /// Sets an application-owned compatibility resolver for expanded native files.
    ///
    /// The callback receives a fresh clone of the base registry and can register
    /// implementations referenced by a legacy application. Concise projects use
    /// their declared providers instead and never invoke this callback. Resolution
    /// must only load descriptions and factories, not launch workloads.
    pub fn set_native_resolver<F>(&mut self, resolver: F)
    where
        F: Fn(&str, &mut ApplicationRegistry) -> Result<(), String> + Send + Sync + 'static,
    {
        self.native_resolver = Some(Arc::new(resolver));
    }

    /// Builds an ordinary expanded application through the same native validators.
    ///
    /// # Errors
    ///
    /// Returns native configuration and graph admission errors unchanged.
    pub fn build_native(&self, document: &str) -> Result<Application, ApplicationConfigError> {
        let config = ApplicationConfig::from_json(document)?;
        let mut registry = self.registry.clone();
        if let Some(resolve) = &self.native_resolver {
            resolve(document, &mut registry).map_err(ApplicationConfigError::NativeResolution)?;
        }
        registry.build(config)
    }

    /// Loads component descriptions without binding or launching a workflow.
    ///
    /// # Errors
    ///
    /// Returns errors for malformed projects or components that cannot be resolved.
    pub fn describe(
        &self,
        document: &str,
        project_root: &Path,
    ) -> Result<BTreeMap<String, ComponentDescription>, ProjectError> {
        let config = ProjectConfig::from_json(document)?;
        let root = canonical_root(project_root)?;
        let (_, components) = self.load(&config, &root)?;
        Ok(components
            .into_iter()
            .map(|(alias, component)| (alias, component.description()))
            .collect())
    }

    /// Resolves, binds, and validates a concise project before any worker launch.
    ///
    /// # Errors
    ///
    /// Returns a contextual declaration error or the ordinary native build error.
    pub fn prepare(
        &self,
        document: &str,
        project_root: &Path,
    ) -> Result<PreparedProject, ProjectError> {
        let config = ProjectConfig::from_json(document)?;
        let project_root = canonical_root(project_root)?;
        let (registry, components) = self.load(&config, &project_root)?;
        let descriptions = components
            .iter()
            .map(|(alias, component)| (alias.clone(), component.description()))
            .collect::<BTreeMap<_, _>>();
        let application_json = compile(&config, &components, &descriptions)?;
        let application = registry.build(ApplicationConfig::from_json(&application_json)?)?;
        Ok(PreparedProject {
            application,
            application_json,
            components: descriptions,
            component_specs: config.components,
            project_root,
        })
    }

    fn load(
        &self,
        config: &ProjectConfig,
        project_root: &Path,
    ) -> Result<LoadedComponents, ProjectError> {
        let mut groups = BTreeMap::<&str, BTreeMap<String, Value>>::new();
        for (alias, spec) in &config.components {
            nonempty(alias, "component alias")?;
            let provider = spec
                .get("provider")
                .and_then(Value::as_str)
                .ok_or_else(|| {
                    ProjectError::Invalid(format!("component {alias:?} requires a string provider"))
                })?;
            if !self.providers.contains_key(provider) {
                return Err(ProjectError::Invalid(format!(
                    "component {alias:?} references unregistered provider {provider:?}"
                )));
            }
            groups
                .entry(provider)
                .or_default()
                .insert(alias.clone(), spec.clone());
        }
        let mut registry = self.registry.clone();
        let mut components = BTreeMap::new();
        for (name, specs) in groups {
            let loaded = self.providers[name]
                .load(&specs, project_root, &mut registry)
                .map_err(|message| {
                    ProjectError::Invalid(format!("provider {name:?}: {message}"))
                })?;
            if !loaded.keys().eq(specs.keys()) {
                return Err(ProjectError::Invalid(format!(
                    "provider {name:?} must return exactly the requested component aliases"
                )));
            }
            components.extend(loaded);
        }
        Ok((registry, components))
    }
}

type LoadedComponents = (
    ApplicationRegistry,
    BTreeMap<String, Arc<dyn ProjectComponent>>,
);

fn canonical_root(path: &Path) -> Result<PathBuf, ProjectError> {
    let root = path.canonicalize().map_err(|error| {
        ProjectError::Invalid(format!(
            "cannot resolve project root {}: {error}",
            path.display()
        ))
    })?;
    if !root.is_dir() {
        return Err(ProjectError::Invalid(format!(
            "project root {} is not a directory",
            root.display()
        )));
    }
    Ok(root)
}

fn nonempty(value: &str, label: &str) -> Result<(), ProjectError> {
    if value.trim().is_empty() {
        Err(ProjectError::Invalid(format!("{label} cannot be empty")))
    } else {
        Ok(())
    }
}

fn compile(
    config: &ProjectConfig,
    components: &BTreeMap<String, Arc<dyn ProjectComponent>>,
    descriptions: &BTreeMap<String, ComponentDescription>,
) -> Result<String, ProjectError> {
    if !config.nodes.contains_key(&config.entry) {
        return Err(ProjectError::Invalid(format!(
            "entry node {:?} is not placed",
            config.entry
        )));
    }
    let mut bindings = BTreeMap::new();
    for (node_id, node) in &config.nodes {
        nonempty(node_id, "node identity")?;
        let description = descriptions.get(&node.component).ok_or_else(|| {
            ProjectError::Invalid(format!(
                "node {node_id:?} references unknown component {:?}",
                node.component
            ))
        })?;
        if !description.ingress_modes.contains(&node.ingress_mode) {
            return Err(ProjectError::Invalid(format!(
                "node {node_id:?}: component {:?} does not support {:?} ingress",
                node.component, node.ingress_mode
            )));
        }
        let is_entry = node_id == &config.entry;
        if is_entry && node.root_authority.is_none() {
            return Err(ProjectError::Invalid(format!(
                "entry node {node_id:?} requires explicit root_authority (which may be empty)"
            )));
        }
        if !is_entry && node.root_authority.is_some() {
            return Err(ProjectError::Invalid(format!(
                "node {node_id:?}: root_authority is supported only on entry {:?}",
                config.entry
            )));
        }
        bindings.insert(
            node_id.clone(),
            ComponentBindings {
                node_id: node_id.clone(),
                inputs: BTreeMap::new(),
                outputs: BTreeMap::new(),
                ingress_mode: node.ingress_mode,
                is_entry,
            },
        );
    }
    let mut edge_definitions = BTreeMap::new();
    let mut edges = BTreeMap::new();
    for connection in &config.connections {
        nonempty(&connection.id, "connection identity")?;
        if edges.contains_key(&connection.id) {
            return Err(ProjectError::Invalid(format!(
                "duplicate connection identity {:?}",
                connection.id
            )));
        }
        let (source, source_contract) = endpoint(config, descriptions, connection, true)?;
        let (target, target_contract) = endpoint(config, descriptions, connection, false)?;
        let contract = connection_contract(connection, source_contract, target_contract)?;
        let definition_id = format!("edge:{}", connection.id);
        edge_definitions.insert(
            definition_id.clone(),
            json!({
                "types": ["Connection"], "source_requirements": source.types,
                "target_requirements": target.types, "package_contract": contract,
                "authority_tags": connection.authority_tags,
                "authority_match": connection.authority_match,
            }),
        );
        edges.insert(connection.id.clone(), json!({
            "definition": definition_id, "source": connection.from[0], "target": connection.to[0],
        }));
        bindings
            .get_mut(&connection.from[0])
            .expect("validated source")
            .outputs
            .entry(connection.from[1].clone())
            .or_default()
            .push(connection.id.clone());
        bindings
            .get_mut(&connection.to[0])
            .expect("validated target")
            .inputs
            .entry(connection.to[1].clone())
            .or_default()
            .push(connection.id.clone());
    }
    let mut node_definitions = BTreeMap::new();
    let mut nodes = BTreeMap::new();
    for (node_id, node) in &config.nodes {
        let description = &descriptions[&node.component];
        let binding = bindings.get_mut(node_id).expect("initialized placement");
        for edges in binding
            .inputs
            .values_mut()
            .chain(binding.outputs.values_mut())
        {
            edges.sort();
        }
        let bound = components[&node.component]
            .bind(node.config.clone(), binding)
            .map_err(|message| {
                ProjectError::Invalid(format!(
                    "node {node_id:?} using component {:?}: {message}",
                    node.component
                ))
            })?;
        let definition_id = format!("node:{node_id}");
        node_definitions.insert(definition_id.clone(), json!({
            "types": description.types, "result_contract": description.result_contract,
            "ingress_mode": ingress_name(node.ingress_mode), "root_authority": node.root_authority,
            "context": node.context,
            "authority_transitions": node.authority_transitions,
            "implementation": {"kind": bound.kind, "config": bound.config},
        }));
        nodes.insert(node_id.clone(), json!({"definition": definition_id}));
    }
    Ok(serde_json::to_string_pretty(&json!({
        "id": config.id, "entry": config.entry, "node_definitions": node_definitions,
        "edge_definitions": edge_definitions, "nodes": nodes, "edges": edges,
    }))?)
}

fn endpoint<'a>(
    config: &ProjectConfig,
    descriptions: &'a BTreeMap<String, ComponentDescription>,
    connection: &ProjectConnection,
    outgoing: bool,
) -> Result<(&'a ComponentDescription, Option<&'a str>), ProjectError> {
    let endpoint = if outgoing {
        &connection.from
    } else {
        &connection.to
    };
    let direction = if outgoing { "output" } else { "input" };
    let node = config.nodes.get(&endpoint[0]).ok_or_else(|| {
        ProjectError::Invalid(format!(
            "connection {:?} references unknown node {:?}",
            connection.id, endpoint[0]
        ))
    })?;
    let description = &descriptions[&node.component];
    nonempty(
        &endpoint[1],
        &format!("connection {:?} {direction} port", connection.id),
    )?;
    let (ports, dynamic) = if outgoing {
        (&description.outputs, description.dynamic_outputs)
    } else {
        (&description.inputs, description.dynamic_inputs)
    };
    if let Some(contract) = ports.get(&endpoint[1]) {
        return Ok((description, Some(contract)));
    }
    if dynamic {
        return Ok((description, None));
    }
    Err(ProjectError::Invalid(format!(
        "connection {:?}: node {:?} has no {direction} port {:?}",
        connection.id, endpoint[0], endpoint[1]
    )))
}

fn connection_contract<'a>(
    connection: &'a ProjectConnection,
    source: Option<&'a str>,
    target: Option<&'a str>,
) -> Result<&'a str, ProjectError> {
    if let (Some(source), Some(target)) = (source, target) {
        if source != target {
            return Err(ProjectError::Invalid(format!(
                "connection {:?} supplies contract {source:?} but its target expects {target:?}",
                connection.id
            )));
        }
    } else if source.is_none() && target.is_none() && connection.contract.is_none() {
        return Err(ProjectError::Invalid(format!(
            "connection {:?} requires an explicit contract because both endpoints are dynamic",
            connection.id
        )));
    }
    let contract = connection
        .contract
        .as_deref()
        .or(source)
        .or(target)
        .expect("fixed ports or explicit dynamic contract");
    nonempty(
        contract,
        &format!("connection {:?} contract", connection.id),
    )?;
    if source.is_some_and(|expected| expected != contract)
        || target.is_some_and(|expected| expected != contract)
    {
        return Err(ProjectError::Invalid(format!(
            "connection {:?}: explicit contract {contract:?} does not match its declared port contracts",
            connection.id
        )));
    }
    Ok(contract)
}

const fn ingress_name(mode: IngressMode) -> &'static str {
    match mode {
        IngressMode::Any => "any",
        IngressMode::All => "all",
    }
}

// Serde's serialize_with callback receives the field by reference.
#[allow(clippy::trivially_copy_pass_by_ref)]
fn serialize_ingress<S: Serializer>(mode: &IngressMode, serializer: S) -> Result<S::Ok, S::Error> {
    serializer.serialize_str(ingress_name(*mode))
}

fn deserialize_ingress<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<IngressMode, D::Error> {
    parse_ingress(&String::deserialize(deserializer)?)
}

fn parse_ingress<E: serde::de::Error>(value: &str) -> Result<IngressMode, E> {
    match value {
        "any" => Ok(IngressMode::Any),
        "all" => Ok(IngressMode::All),
        other => Err(serde::de::Error::unknown_variant(other, &["any", "all"])),
    }
}

fn serialize_ingress_modes<S: Serializer>(
    modes: &[IngressMode],
    serializer: S,
) -> Result<S::Ok, S::Error> {
    modes
        .iter()
        .map(|mode| ingress_name(*mode))
        .collect::<Vec<_>>()
        .serialize(serializer)
}

fn deserialize_ingress_modes<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Vec<IngressMode>, D::Error> {
    Vec::<String>::deserialize(deserializer)?
        .into_iter()
        .map(|mode| parse_ingress(&mode))
        .collect()
}

struct UniqueJson;

impl<'de> Deserialize<'de> for UniqueJson {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(UniqueJsonVisitor)
    }
}

struct UniqueJsonVisitor;

impl<'de> Visitor<'de> for UniqueJsonVisitor {
    type Value = UniqueJson;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("JSON with unique object keys")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut keys = BTreeSet::new();
        while let Some(key) = map.next_key::<String>()? {
            if !keys.insert(key.clone()) {
                return Err(serde::de::Error::custom(format!(
                    "duplicate JSON key {key:?}"
                )));
            }
            let _ = map.next_value::<UniqueJson>()?;
        }
        Ok(UniqueJson)
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        while seq.next_element::<UniqueJson>()?.is_some() {}
        Ok(UniqueJson)
    }

    fn visit_bool<E: serde::de::Error>(self, _: bool) -> Result<Self::Value, E> {
        Ok(UniqueJson)
    }
    fn visit_i64<E: serde::de::Error>(self, _: i64) -> Result<Self::Value, E> {
        Ok(UniqueJson)
    }
    fn visit_u64<E: serde::de::Error>(self, _: u64) -> Result<Self::Value, E> {
        Ok(UniqueJson)
    }
    fn visit_f64<E: serde::de::Error>(self, _: f64) -> Result<Self::Value, E> {
        Ok(UniqueJson)
    }
    fn visit_str<E: serde::de::Error>(self, _: &str) -> Result<Self::Value, E> {
        Ok(UniqueJson)
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<Self::Value, E> {
        Ok(UniqueJson)
    }
}
