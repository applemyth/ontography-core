//! Declarative application configuration resolved through trusted Rust registries.

use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::future::Future;
use std::marker::PhantomData;
use std::sync::Arc;

use serde::de::{MapAccess, SeqAccess, Visitor};
use serde::{Deserialize, Deserializer, Serialize};
use serde_json::Value;
use thiserror::Error;

use crate::application::NodeExecutable;
use crate::{
    Application, ApplicationBuilder, ApplicationContext, ApplicationError, EdgeConfig,
    NodeComponent, NodeConfig,
};
use ontography_calculus::{Authority, AuthorityMatch, AuthorityTag, Contract, IngressMode, Kernel};
use ontography_runtime::ExecutionFailure;

type Text = Arc<str>;
type NodeFactory = dyn Fn(Value) -> Result<NodeExecutable, String> + Send + Sync + 'static;
type NodeValidator = dyn Fn(&Kernel, &str, &Value) -> Result<(), String> + Send + Sync + 'static;

/// The duplicate-key check for the map-typed and opaque objects of both
/// authoring formats. Typed objects rely on the serde derive, which rejects a
/// repeated field on its own; every map-typed field and every opaque value is
/// deserialized through this visitor, because a map or `Value` would
/// otherwise keep the last duplicate silently.
struct UniqueMapVisitor<V>(PhantomData<fn() -> V>);

impl<'de, V> Visitor<'de> for UniqueMapVisitor<V>
where
    V: Deserialize<'de>,
{
    type Value = BTreeMap<String, V>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("an object with unique keys")
    }

    fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
    where
        M: MapAccess<'de>,
    {
        let mut values = BTreeMap::new();
        while let Some(key) = access.next_key::<String>()? {
            let value = access.next_value()?;
            match values.entry(key) {
                Entry::Vacant(entry) => {
                    entry.insert(value);
                }
                Entry::Occupied(entry) => {
                    return Err(serde::de::Error::custom(format!(
                        "duplicate JSON key {:?}",
                        entry.key()
                    )));
                }
            }
        }
        Ok(values)
    }
}

/// Deserializes a typed object whose keys must be unique.
pub(crate) fn deserialize_unique_string_map<'de, D, V>(
    deserializer: D,
) -> Result<BTreeMap<String, V>, D::Error>
where
    D: Deserializer<'de>,
    V: Deserialize<'de>,
{
    deserializer.deserialize_map(UniqueMapVisitor(PhantomData))
}

/// Opaque JSON whose objects reject duplicate keys at every depth.
struct UniqueValue(Value);

impl<'de> Deserialize<'de> for UniqueValue {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        deserializer.deserialize_any(UniqueValueVisitor)
    }
}

struct UniqueValueVisitor;

impl<'de> Visitor<'de> for UniqueValueVisitor {
    type Value = UniqueValue;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("JSON with unique object keys")
    }

    fn visit_map<A: MapAccess<'de>>(self, access: A) -> Result<Self::Value, A::Error> {
        let entries = UniqueMapVisitor::<UniqueValue>(PhantomData).visit_map(access)?;
        Ok(UniqueValue(Value::Object(
            entries
                .into_iter()
                .map(|(key, UniqueValue(value))| (key, value))
                .collect(),
        )))
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<Self::Value, A::Error> {
        let mut items = Vec::new();
        while let Some(UniqueValue(item)) = seq.next_element()? {
            items.push(item);
        }
        Ok(UniqueValue(Value::Array(items)))
    }

    fn visit_bool<E: serde::de::Error>(self, value: bool) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Bool(value)))
    }
    fn visit_i64<E: serde::de::Error>(self, value: i64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::from(value)))
    }
    fn visit_u64<E: serde::de::Error>(self, value: u64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::from(value)))
    }
    fn visit_f64<E: serde::de::Error>(self, value: f64) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::from(value)))
    }
    fn visit_str<E: serde::de::Error>(self, value: &str) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::String(value.to_owned())))
    }
    fn visit_unit<E: serde::de::Error>(self) -> Result<Self::Value, E> {
        Ok(UniqueValue(Value::Null))
    }
}

/// Deserializes opaque configuration, rejecting duplicate keys at every depth.
pub(crate) fn deserialize_unique_value<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<Value, D::Error> {
    UniqueValue::deserialize(deserializer).map(|UniqueValue(value)| value)
}

/// Deserializes a map of opaque values, rejecting duplicate keys at every depth.
pub(crate) fn deserialize_unique_value_map<'de, D: Deserializer<'de>>(
    deserializer: D,
) -> Result<BTreeMap<String, Value>, D::Error> {
    deserialize_unique_string_map::<D, UniqueValue>(deserializer).map(|values| {
        values
            .into_iter()
            .map(|(key, UniqueValue(value))| (key, value))
            .collect()
    })
}

/// A complete JSON-declarable application awaiting trusted implementation resolution.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ApplicationConfig {
    id: String,
    entry: String,
    #[serde(deserialize_with = "deserialize_unique_string_map")]
    node_definitions: BTreeMap<String, NodeDefinitionConfig>,
    #[serde(deserialize_with = "deserialize_unique_string_map")]
    edge_definitions: BTreeMap<String, EdgeDefinitionConfig>,
    #[serde(deserialize_with = "deserialize_unique_string_map")]
    nodes: BTreeMap<String, NodePlacementConfig>,
    #[serde(deserialize_with = "deserialize_unique_string_map")]
    edges: BTreeMap<String, EdgePlacementConfig>,
}

impl ApplicationConfig {
    /// Parses one complete application declaration from JSON.
    ///
    /// Duplicate object keys are rejected at every depth, including inside
    /// opaque implementation configuration. The derived [`Deserialize`]
    /// implementation applies the same rule.
    ///
    /// # Errors
    ///
    /// Returns an error when the JSON is malformed or does not match the closed
    /// declarative configuration shape.
    pub fn from_json(json: &str) -> Result<Self, ApplicationConfigError> {
        Ok(serde_json::from_str(json)?)
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NodeDefinitionConfig {
    types: Vec<String>,
    result_contract: String,
    #[serde(default)]
    ingress_mode: IngressModeConfig,
    #[serde(default)]
    context: ontography_runtime::ContextPolicy,
    #[serde(default)]
    root_authority: Option<Vec<String>>,
    #[serde(default)]
    authority_transitions: Vec<AuthorityTransitionConfig>,
    implementation: ImplementationConfig,
}

/// Serialized [`IngressMode`] shared by both authoring formats.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub(crate) enum IngressModeConfig {
    #[default]
    Any,
    All,
}

impl From<IngressModeConfig> for IngressMode {
    fn from(value: IngressModeConfig) -> Self {
        match value {
            IngressModeConfig::Any => Self::Any,
            IngressModeConfig::All => Self::All,
        }
    }
}

impl From<IngressMode> for IngressModeConfig {
    fn from(value: IngressMode) -> Self {
        match value {
            IngressMode::Any => Self::Any,
            IngressMode::All => Self::All,
        }
    }
}

/// One exact authority transition, in the syntax shared by both authoring
/// formats: exactly one of `to`, `add`, or `remove` selects the change.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AuthorityTransitionConfig {
    /// Exact starting authority.
    pub from: Vec<String>,
    /// Exact replacement authority; mutually exclusive with `add` and `remove`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub to: Option<Vec<String>>,
    /// Tags added to `from`; mutually exclusive with `to` and `remove`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub add: Option<Vec<String>>,
    /// Tags removed from `from`; mutually exclusive with `to` and `add`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub remove: Option<Vec<String>>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct ImplementationConfig {
    kind: String,
    #[serde(default, deserialize_with = "deserialize_unique_value")]
    config: Value,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct EdgeDefinitionConfig {
    types: Vec<String>,
    #[serde(default)]
    source_requirements: Vec<String>,
    #[serde(default)]
    target_requirements: Vec<String>,
    package_contract: String,
    authority_tags: Vec<String>,
    #[serde(default)]
    authority_match: AuthorityMatchConfig,
}

/// Serialized edge authority matching shared by both authoring formats.
#[derive(Clone, Copy, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthorityMatchConfig {
    /// At least one allowed tag must be carried.
    #[default]
    AnyOf,
    /// All allowed tags must be carried.
    AllOf,
}

impl From<AuthorityMatchConfig> for AuthorityMatch {
    fn from(value: AuthorityMatchConfig) -> Self {
        match value {
            AuthorityMatchConfig::AnyOf => Self::AnyOf,
            AuthorityMatchConfig::AllOf => Self::AllOf,
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct NodePlacementConfig {
    definition: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct EdgePlacementConfig {
    definition: String,
    source: String,
    target: String,
}

/// Failure while parsing or resolving a declarative application.
#[derive(Debug, Error)]
pub enum ApplicationConfigError {
    /// The JSON document does not match the application configuration shape.
    #[error("invalid application JSON: {0}")]
    Json(#[from] serde_json::Error),
    /// A registry identifier is empty.
    #[error("invalid empty {0}")]
    EmptyIdentifier(&'static str),
    /// A trusted contract was registered more than once.
    #[error("contract {0:?} is already registered")]
    DuplicateContract(Text),
    /// A trusted node implementation was registered more than once.
    #[error("node implementation {0:?} is already registered")]
    DuplicateImplementation(Text),
    /// A validation hook was registered more than once for one implementation.
    #[error("node validator for implementation {0:?} is already registered")]
    DuplicateValidator(Text),
    /// A referenced contract has no trusted registry entry.
    #[error("contract {0:?} is not registered")]
    MissingContract(String),
    /// A referenced node implementation has no trusted registry entry.
    #[error("node implementation {0:?} is not registered")]
    MissingImplementation(String),
    /// A node placement references an unknown reusable definition.
    #[error("node {node_id:?} references unknown definition {definition:?}")]
    MissingNodeDefinition {
        /// Concrete node identity.
        node_id: String,
        /// Missing reusable definition identity.
        definition: String,
    },
    /// An edge placement references an unknown reusable definition.
    #[error("edge {edge_id:?} references unknown definition {definition:?}")]
    MissingEdgeDefinition {
        /// Concrete edge identity.
        edge_id: String,
        /// Missing reusable definition identity.
        definition: String,
    },
    /// The entry identity does not name a placed node.
    #[error("entry node {0:?} is not placed")]
    MissingEntry(String),
    /// A definition declaring `root_authority` was placed as a non-entry node.
    #[error(
        "node {node_id:?} places definition {definition:?}, which declares root_authority, but only the entry may"
    )]
    RootAuthorityOutsideEntry {
        /// Concrete node identity.
        node_id: String,
        /// Reusable node-definition identity declaring the root authority.
        definition: String,
    },
    /// A configured authority tag is invalid.
    #[error("invalid authority tag {tag:?} in {location}: {message}")]
    InvalidAuthorityTag {
        /// Rejected authority tag.
        tag: String,
        /// Configuration location containing the tag.
        location: String,
        /// Kernel identifier-validation failure.
        message: String,
    },
    /// An authority transition does not select one exact change operation.
    #[error(
        "authority transition {index} on node definition {definition:?} requires exactly one of to, add, or remove"
    )]
    AmbiguousAuthorityTransition {
        /// Reusable node-definition identity.
        definition: String,
        /// Zero-based transition index.
        index: usize,
    },
    /// A trusted implementation rejected its opaque configuration.
    #[error("node implementation {kind:?} rejected definition {definition:?}: {message}")]
    Implementation {
        /// Reusable node-definition identity.
        definition: String,
        /// Trusted implementation registry key.
        kind: String,
        /// Stable implementation-provided explanation.
        message: String,
    },
    /// A trusted implementation rejected a placement in the completed graph.
    #[error("node {node_id:?} using implementation {kind:?} failed validation: {message}")]
    PlacementValidation {
        /// Concrete node identity.
        node_id: String,
        /// Trusted implementation registry key.
        kind: String,
        /// Implementation-provided explanation.
        message: String,
    },
    /// Native application construction or kernel admission failed.
    #[error(transparent)]
    Application(#[from] ApplicationError),
}

/// Trusted contracts and executable factories used to resolve application JSON.
#[derive(Clone)]
pub struct ApplicationRegistry {
    contracts: BTreeMap<Text, Contract>,
    implementations: BTreeMap<Text, Arc<NodeFactory>>,
    validators: BTreeMap<Text, Arc<NodeValidator>>,
}

impl fmt::Debug for ApplicationRegistry {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter
            .debug_struct("ApplicationRegistry")
            .field("contracts", &self.contracts.keys())
            .field("implementations", &self.implementations.keys())
            .field("validators", &self.validators.keys())
            .finish()
    }
}

impl Default for ApplicationRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl ApplicationRegistry {
    /// Creates an empty trusted registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            contracts: BTreeMap::new(),
            implementations: BTreeMap::new(),
            validators: BTreeMap::new(),
        }
    }

    /// Registers one trusted payload contract by its exact contract ID.
    ///
    /// # Errors
    ///
    /// Returns an error when that contract ID is already registered.
    pub fn register_contract(&mut self, contract: Contract) -> Result<(), ApplicationConfigError> {
        let id = Arc::from(contract.id());
        if self.contracts.contains_key(&id) {
            return Err(ApplicationConfigError::DuplicateContract(id));
        }
        self.contracts.insert(id, contract);
        Ok(())
    }

    /// Registers a trusted node implementation factory under `kind`.
    ///
    /// The factory receives only the opaque JSON value nested under
    /// `implementation.config` and returns executable behavior. The generic
    /// loader remains the sole composer of kernel node semantics.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty or duplicate implementation key.
    pub fn register_node_implementation<F, X, Fut, E>(
        &mut self,
        kind: impl Into<Text>,
        factory: F,
    ) -> Result<(), ApplicationConfigError>
    where
        F: Fn(Value) -> Result<X, E> + Send + Sync + 'static,
        X: Fn(ApplicationContext) -> Fut + Send + Sync + 'static,
        Fut: Future<Output = Result<(), ExecutionFailure>> + Send + 'static,
        E: fmt::Display,
    {
        let kind = kind.into();
        if kind.is_empty() {
            return Err(ApplicationConfigError::EmptyIdentifier(
                "node implementation kind",
            ));
        }
        if self.implementations.contains_key(&kind) {
            return Err(ApplicationConfigError::DuplicateImplementation(kind));
        }
        self.implementations.insert(
            kind,
            Arc::new(move |value| {
                factory(value)
                    .map(NodeExecutable::new)
                    .map_err(|error| error.to_string())
            }),
        );
        Ok(())
    }

    /// Registers a placement validator for a trusted implementation.
    ///
    /// Every configured placement is checked against the completed kernel before
    /// [`Self::build`] returns. Validators must only inspect configuration and
    /// graph bindings; they must not launch workloads or create runtime state.
    ///
    /// # Errors
    ///
    /// Returns an error for an empty kind or a duplicate validator. The
    /// implementation may be registered before or after its validator.
    pub fn register_node_validator<F>(
        &mut self,
        kind: impl Into<Text>,
        validator: F,
    ) -> Result<(), ApplicationConfigError>
    where
        F: Fn(&Kernel, &str, &Value) -> Result<(), String> + Send + Sync + 'static,
    {
        let kind = kind.into();
        if kind.is_empty() {
            return Err(ApplicationConfigError::EmptyIdentifier(
                "node validator kind",
            ));
        }
        if self.validators.contains_key(&kind) {
            return Err(ApplicationConfigError::DuplicateValidator(kind));
        }
        self.validators.insert(kind, Arc::new(validator));
        Ok(())
    }

    /// Resolves one declarative application through the trusted registry and
    /// admits it through the normal [`crate::ApplicationBuilder`] path.
    ///
    /// # Errors
    ///
    /// Returns an error for unresolved names, invalid authority syntax, a
    /// rejected implementation configuration, or native kernel admission.
    pub fn build(&self, config: ApplicationConfig) -> Result<Application, ApplicationConfigError> {
        if !config.nodes.contains_key(&config.entry) {
            return Err(ApplicationConfigError::MissingEntry(config.entry));
        }

        let placement_checks = config
            .nodes
            .iter()
            .filter_map(|(node_id, placement)| {
                let definition = config.node_definitions.get(&placement.definition)?;
                let implementation = &definition.implementation;
                self.validators
                    .get(implementation.kind.as_str())
                    .map(|validator| {
                        (
                            node_id.clone(),
                            implementation.kind.clone(),
                            implementation.config.clone(),
                            Arc::clone(validator),
                        )
                    })
            })
            .collect::<Vec<_>>();

        let mut components = BTreeMap::new();
        for (definition_id, definition) in config.node_definitions {
            let result_contract = self
                .contracts
                .get(definition.result_contract.as_str())
                .cloned()
                .ok_or_else(|| {
                    ApplicationConfigError::MissingContract(definition.result_contract.clone())
                })?;
            let node_config = NodeConfig::new(definition.types, result_contract)?
                .with_ingress_mode(definition.ingress_mode.into())
                .with_context_policy(definition.context);
            let implementation = self
                .implementations
                .get(definition.implementation.kind.as_str())
                .ok_or_else(|| {
                    ApplicationConfigError::MissingImplementation(
                        definition.implementation.kind.clone(),
                    )
                })?;
            let executable =
                implementation(definition.implementation.config).map_err(|message| {
                    ApplicationConfigError::Implementation {
                        definition: definition_id.clone(),
                        kind: definition.implementation.kind,
                        message,
                    }
                })?;
            let mut component = NodeComponent::from_executable(node_config, executable);
            if let Some(root_authority) = definition.root_authority {
                component = component.with_root_authority(parse_authority(
                    root_authority,
                    format!("node definition {definition_id:?} root_authority"),
                )?);
            }
            for (index, transition) in definition.authority_transitions.into_iter().enumerate() {
                let (from, to) = lower_transition(&definition_id, index, transition)?;
                component = component.with_authority_transition(from, to);
            }
            components.insert(definition_id, component);
        }

        let mut edge_configs = BTreeMap::new();
        for (definition_id, definition) in config.edge_definitions {
            let package_contract = self
                .contracts
                .get(definition.package_contract.as_str())
                .cloned()
                .ok_or_else(|| {
                    ApplicationConfigError::MissingContract(definition.package_contract.clone())
                })?;
            let authority_tags = parse_tags(
                definition.authority_tags,
                format!("edge definition {definition_id:?} authority_tags"),
            )?;
            let edge = EdgeConfig::new(
                definition.types,
                definition.source_requirements,
                definition.target_requirements,
                package_contract,
                authority_tags,
            )?
            .with_authority_match(definition.authority_match.into());
            edge_configs.insert(definition_id, edge);
        }

        let mut builder = ApplicationBuilder::new(config.id)?;
        for (node_id, placement) in config.nodes {
            let component = components
                .get(&placement.definition)
                .cloned()
                .ok_or_else(|| ApplicationConfigError::MissingNodeDefinition {
                    node_id: node_id.clone(),
                    definition: placement.definition.clone(),
                })?;
            if node_id == config.entry {
                builder.entry(node_id, component)?;
            } else if component.root_authority().is_some() {
                return Err(ApplicationConfigError::RootAuthorityOutsideEntry {
                    node_id,
                    definition: placement.definition,
                });
            } else {
                builder.node(node_id, component)?;
            }
        }
        for (edge_id, placement) in config.edges {
            let config = edge_configs
                .get(&placement.definition)
                .cloned()
                .ok_or_else(|| ApplicationConfigError::MissingEdgeDefinition {
                    edge_id: edge_id.clone(),
                    definition: placement.definition.clone(),
                })?;
            builder.connect(edge_id, &placement.source, config, &placement.target)?;
        }
        let application = builder.build()?;
        for (node_id, kind, config, validator) in placement_checks {
            validator(application.kernel(), &node_id, &config).map_err(|message| {
                ApplicationConfigError::PlacementValidation {
                    node_id,
                    kind,
                    message,
                }
            })?;
        }
        Ok(application)
    }
}

fn lower_transition(
    definition: &str,
    index: usize,
    transition: AuthorityTransitionConfig,
) -> Result<(Authority, Authority), ApplicationConfigError> {
    let operation_count = usize::from(transition.to.is_some())
        + usize::from(transition.add.is_some())
        + usize::from(transition.remove.is_some());
    if operation_count != 1 {
        return Err(ApplicationConfigError::AmbiguousAuthorityTransition {
            definition: definition.to_owned(),
            index,
        });
    }

    let location = format!("node definition {definition:?} authority transition {index}");
    let from_tags = parse_tags(transition.from, format!("{location} from"))?;
    let to_tags = if let Some(to) = transition.to {
        parse_tags(to, format!("{location} to"))?
    } else if let Some(add) = transition.add {
        let mut target = from_tags.clone();
        target.extend(parse_tags(add, format!("{location} add"))?);
        target
    } else {
        let mut target = from_tags.clone();
        let removed = parse_tags(
            transition
                .remove
                .expect("operation count guarantees remove"),
            format!("{location} remove"),
        )?;
        target.retain(|tag| !removed.contains(tag));
        target
    };
    Ok((Authority::new(from_tags), Authority::new(to_tags)))
}

fn parse_authority(
    tags: Vec<String>,
    location: String,
) -> Result<Authority, ApplicationConfigError> {
    Ok(Authority::new(parse_tags(tags, location)?))
}

fn parse_tags(
    tags: Vec<String>,
    location: String,
) -> Result<BTreeSet<AuthorityTag>, ApplicationConfigError> {
    tags.into_iter()
        .map(|tag| {
            AuthorityTag::new(tag.clone()).map_err(|error| {
                ApplicationConfigError::InvalidAuthorityTag {
                    tag,
                    location: location.clone(),
                    message: error.to_string(),
                }
            })
        })
        .collect()
}
