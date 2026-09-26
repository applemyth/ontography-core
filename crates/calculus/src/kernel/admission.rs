//! Activation admission: live proposals and fixed-graph replay.
//!
//! Both paths evaluate the same rules through one output-proof loop and
//! produce a [`Transition`]; only the source of payload bytes differs.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::graph::{Authority, ContentDigest, Contract, Edge, IngressMode, Payload};

use super::admission_api::{
    ActivationProposal, EmissionDestination, OutputAuthority, Reject, StateRestoreError,
    TriggerWitness,
};
use super::checkpoint::consumption_order;
use super::definition::Kernel;
use super::frontier::Delivery;
use super::occurrence::{
    Activation, ActivationId, Output, PackageId, PackageRecord, PackageStatus, State, StateParts,
    Trigger,
};
use super::transition::{Binding, PackageView, Transition, TransitionKind};

/// Read each input once. The proof and the sealed transition bind the same
/// records even when an external view changes its answers during evaluation.
struct InputView {
    binding: Binding,
    records: BTreeMap<PackageId, PackageRecord>,
}

impl InputView {
    fn capture(view: &dyn PackageView, inputs: Option<&BTreeSet<PackageId>>) -> Self {
        Self {
            binding: view.binding(),
            records: inputs
                .into_iter()
                .flatten()
                .filter_map(|id| view.record(*id).map(|record| (*id, record)))
                .collect(),
        }
    }
}

impl PackageView for InputView {
    fn record(&self, package: PackageId) -> Option<PackageRecord> {
        self.records.get(&package).cloned()
    }
    fn activation_known(&self, _: ActivationId) -> bool {
        false
    }
    fn binding(&self) -> Binding {
        self.binding.clone()
    }
}

/// A live, delivered package as seen by a join.
struct PendingInput {
    edge_id: Arc<str>,
    node_id: Arc<str>,
    authority: Authority,
}

/// The facts a legal package trigger establishes.
struct ValidatedInputs {
    node_id: Arc<str>,
    governing_authority: Authority,
    ingress_mode: IngressMode,
    incoming_edge_ids: BTreeSet<Arc<str>>,
    realized_edge_ids: BTreeSet<Arc<str>>,
}

struct OutputProofContext<'a> {
    activation_id: ActivationId,
    node_id: &'a Arc<str>,
    governing_authority: &'a Authority,
}

/// The bytes behind one proposed output: supplied now, or committed earlier
/// and supplied on demand as evidence.
enum OutputContent<'a> {
    Bytes(&'a Payload),
    Committed {
        digest: ContentDigest,
        declared_type: &'a Arc<str>,
    },
}

/// One output request in the shape shared by live and restored admission.
struct OutputCandidate<'a> {
    edge_id: Option<&'a Arc<str>>,
    outbound_type: Option<&'a Arc<str>>,
    authority: Authority,
    explicit_transition: bool,
    content: OutputContent<'a>,
}

fn pending_input(view: &dyn PackageView, package_id: PackageId) -> Result<PendingInput, Reject> {
    let Some(record) = view.record(package_id) else {
        return Err(Reject::UnknownPackage { package_id });
    };
    match record.status {
        PackageStatus::Consumed(activation_id) => Err(Reject::AlreadyActivated {
            package_id,
            activation_id,
        }),
        PackageStatus::Retired(_) => Err(Reject::PackageRetired { package_id }),
        PackageStatus::Live => match record.delivery {
            None => Err(Reject::PackageNotDelivered { package_id }),
            Some(delivery) => Ok(PendingInput {
                edge_id: delivery.edge_id,
                node_id: delivery.receiver,
                authority: record.authority,
            }),
        },
    }
}

impl Kernel {
    /// Restores accepted activation records under one fixed graph definition.
    ///
    /// This API does not restore graph rewrites, explicit transfers, retirements,
    /// or vocabulary extensions. Exporting such a state through
    /// [`State::to_parts`] is rejected. Restoration topologically replays the
    /// realized occurrence graph. Every activation, package edge, payload
    /// contract, carried authority, and static edge projection is revalidated
    /// against this kernel. Package payload bytes are supplied as external
    /// evidence keyed by their accepted content digests; the restored state
    /// retains only those digests.
    ///
    /// # Errors
    ///
    /// Returns [`StateRestoreError`] when persisted records are incompatible
    /// with this kernel, violate a runtime graph invariant, lack payload
    /// evidence, or disagree with supplied evidence.
    ///
    /// # Panics
    ///
    /// Propagates a panic from trusted contract code.
    pub fn restore_state(
        &self,
        parts: StateParts,
        payload_evidence: &BTreeMap<ContentDigest, Payload>,
    ) -> Result<State, StateRestoreError> {
        let StateParts {
            definition_id,
            definition_fingerprint,
            mut activations,
        } = parts;

        if self.id() != &definition_id || self.fingerprint() != &definition_fingerprint {
            return Err(StateRestoreError::DefinitionMismatch {
                expected_id: self.id().clone(),
                actual_id: definition_id,
                expected_fingerprint: *self.fingerprint(),
                actual_fingerprint: definition_fingerprint,
            });
        }

        let order = Self::restoration_order(&activations)?;
        let mut state = self.empty_state();
        let mut checked_payloads = BTreeSet::new();
        let mut payload_proofs = BTreeSet::new();

        for activation_id in order {
            let activation = activations
                .remove(&activation_id)
                .expect("topological order contains known activations");
            let transition = self.evaluate_recorded(
                &state,
                activation_id,
                activation,
                &mut payload_proofs,
                |package_id, expected| {
                    let payload = payload_evidence.get(&expected).ok_or(
                        StateRestoreError::MissingPayloadEvidence {
                            package_id,
                            content_digest: expected,
                        },
                    )?;
                    if checked_payloads.insert(expected) {
                        let actual = ContentDigest::compute(payload);
                        if actual != expected {
                            return Err(StateRestoreError::PayloadEvidenceMismatch {
                                package_id,
                                expected,
                                actual,
                            });
                        }
                    }
                    Ok(payload.as_ref())
                },
            )?;
            state
                .apply(self, &transition)
                .expect("a transition evaluated against a state applies to it");
        }
        debug_assert!(activations.is_empty());
        Ok(state)
    }

    fn restoration_order(
        activations: &BTreeMap<ActivationId, Activation>,
    ) -> Result<Vec<ActivationId>, StateRestoreError> {
        let mut consumed = BTreeSet::new();

        for (activation_id, activation) in activations {
            for package_id in activation.outputs.keys() {
                if package_id.producer() != *activation_id {
                    return Err(StateRestoreError::invalid(
                        *activation_id,
                        Reject::InvalidPackageIdentity {
                            package_id: *package_id,
                            activation_id: *activation_id,
                        },
                    ));
                }
            }

            if let Trigger::Pkgs { package_ids } = activation.trigger() {
                if package_ids.is_empty() {
                    return Err(StateRestoreError::invalid(
                        *activation_id,
                        Reject::EmptyPackageTrigger,
                    ));
                }
                for package_id in package_ids {
                    let known = activations
                        .get(&package_id.producer())
                        .is_some_and(|producer| {
                            producer.package_outputs().contains_key(package_id)
                        });
                    if !known {
                        return Err(StateRestoreError::invalid(
                            *activation_id,
                            Reject::UnknownPackage {
                                package_id: *package_id,
                            },
                        ));
                    }
                    if !consumed.insert(*package_id) {
                        return Err(StateRestoreError::DuplicateConsumer {
                            package_id: *package_id,
                        });
                    }
                }
            }
        }
        consumption_order(activations)
            .map_err(|activation_id| StateRestoreError::CausalCycle { activation_id })
    }

    /// Validates and snapshots one exact package-trigger candidate without
    /// reserving, consuming, or otherwise changing the state.
    ///
    /// The witness is point-in-time evidence only: another activation may
    /// consume an input after preparation. Callers must still submit an
    /// [`ActivationProposal`] through [`Self::activate`], which revalidates
    /// every trigger premise against the then-current state.
    ///
    /// # Errors
    ///
    /// Returns [`Reject`] when the view belongs to another definition or the
    /// package set is not currently a legal trigger under the target node's
    /// ingress mode.
    pub fn prepare_trigger<I>(
        &self,
        view: &dyn PackageView,
        package_ids: I,
    ) -> Result<TriggerWitness, Reject>
    where
        I: IntoIterator<Item = PackageId>,
    {
        let package_ids = package_ids.into_iter().collect::<BTreeSet<_>>();
        let view = InputView::capture(view, Some(&package_ids));
        let binding = view.binding();
        self.check_binding(&binding)?;
        let validated = self.validate_package_inputs(&view, &package_ids)?;
        Ok(TriggerWitness {
            definition_id: binding.definition_id,
            definition_fingerprint: binding.definition_fingerprint,
            package_ids,
            packages: view.records,
            node_id: validated.node_id,
            authority: validated.governing_authority,
            ingress_mode: validated.ingress_mode,
            incoming_edge_ids: validated.incoming_edge_ids,
            realized_edge_ids: validated.realized_edge_ids,
        })
    }

    fn validate_package_inputs(
        &self,
        view: &dyn PackageView,
        package_ids: &BTreeSet<PackageId>,
    ) -> Result<ValidatedInputs, Reject> {
        let first_id = package_ids
            .first()
            .copied()
            .ok_or(Reject::EmptyPackageTrigger)?;
        let first = pending_input(view, first_id)?;
        let node_id = Arc::clone(&first.node_id);
        let governing_authority = first.authority.clone();
        let mut edge_ids = BTreeSet::new();

        let rest = package_ids
            .iter()
            .skip(1)
            .map(|package_id| pending_input(view, *package_id).map(|input| (*package_id, input)));
        for entry in std::iter::once(Ok((first_id, first))).chain(rest) {
            let (package_id, input) = entry?;
            let package_id = &package_id;
            if input.node_id != node_id {
                return Err(Reject::JoinTargetMismatch {
                    package_id: *package_id,
                    expected: Arc::clone(&node_id),
                    actual: input.node_id,
                });
            }
            if input.authority != governing_authority {
                return Err(Reject::JoinAuthorityMismatch {
                    package_id: *package_id,
                    expected: governing_authority.clone(),
                    actual: input.authority,
                });
            }
            if !edge_ids.insert(Arc::clone(&input.edge_id)) {
                return Err(Reject::DuplicateJoinEdge {
                    node_id: Arc::clone(&node_id),
                    edge_id: input.edge_id,
                });
            }
        }

        let node = self
            .node_definition(&node_id)
            .ok_or_else(|| Reject::UnknownNode {
                node_id: Arc::clone(&node_id),
            })?;
        let ingress_mode = node.ingress_mode();
        let incoming_edge_ids = self.incoming_edge_ids(&node_id);
        match ingress_mode {
            IngressMode::Any if package_ids.len() != 1 => {
                return Err(Reject::JoinNotAllowed {
                    node_id,
                    input_count: package_ids.len(),
                });
            }
            IngressMode::All => {
                if &edge_ids != incoming_edge_ids {
                    return Err(Reject::JoinEdgeMismatch {
                        node_id,
                        expected: incoming_edge_ids.clone(),
                        actual: edge_ids,
                    });
                }
            }
            IngressMode::Any => {}
        }

        Ok(ValidatedInputs {
            node_id,
            governing_authority,
            ingress_mode,
            incoming_edge_ids: incoming_edge_ids.clone(),
            realized_edge_ids: edge_ids,
        })
    }

    fn validate_activation_header(
        &self,
        view: &dyn PackageView,
        trigger: &Trigger,
        result: &[u8],
    ) -> Result<(Arc<str>, Authority), Reject> {
        let (node_id, governing_authority) = match trigger {
            Trigger::Orig { node_id, authority } => {
                let node = self
                    .graph()
                    .node(node_id)
                    .ok_or_else(|| Reject::UnknownNode {
                        node_id: Arc::clone(node_id),
                    })?;
                if !self.schema().admits_authority(authority) {
                    return Err(Reject::AuthorityOutsideSchema {
                        node_id: Arc::clone(node_id),
                        authority: authority.clone(),
                    });
                }
                let ceiling = self
                    .root_ceiling(node_id)
                    .ok_or_else(|| Reject::RootNotAllowed {
                        node_id: Arc::clone(node_id),
                    })?;
                if !authority.is_subset_of(ceiling) {
                    return Err(Reject::RootAuthorityExceeded {
                        node_id: Arc::clone(node_id),
                        requested: authority.clone(),
                        ceiling: ceiling.clone(),
                    });
                }
                (node.id_arc(), authority.clone())
            }
            Trigger::Pkgs { package_ids } => {
                let validated = self.validate_package_inputs(view, package_ids)?;
                (validated.node_id, validated.governing_authority)
            }
        };

        let node = self
            .node_definition(&node_id)
            .expect("executing node has admitted annotations");
        let result_contract = self
            .contract(node.result_contract())
            .expect("node result contract is admitted");
        result_contract
            .validate(result)
            .map_err(|source| Reject::ResultContract {
                node_id: Arc::clone(&node_id),
                contract_id: Arc::from(result_contract.id()),
                source,
            })?;

        Ok((node_id, governing_authority))
    }

    fn validate_birth_authority(
        &self,
        context: &OutputProofContext<'_>,
        package_id: PackageId,
        authority: &Authority,
        explicit_transition: bool,
    ) -> Result<(), Reject> {
        if package_id.producer() != context.activation_id {
            return Err(Reject::InvalidPackageIdentity {
                package_id,
                activation_id: context.activation_id,
            });
        }
        if !self.schema().admits_authority(authority) {
            return Err(Reject::AuthorityOutsideSchema {
                node_id: Arc::clone(context.node_id),
                authority: authority.clone(),
            });
        }
        if (explicit_transition || authority != context.governing_authority)
            && !self.allows_authority_transition(
                context.node_id,
                context.governing_authority,
                authority,
            )
        {
            return Err(Reject::UnauthorizedAuthorityTransition {
                node_id: Arc::clone(context.node_id),
                from: context.governing_authority.clone(),
                to: authority.clone(),
            });
        }
        Ok(())
    }

    fn validate_output_metadata<'a>(
        &'a self,
        context: &OutputProofContext<'_>,
        package_id: PackageId,
        edge_id: &Arc<str>,
        authority: &Authority,
        explicit_transition: bool,
    ) -> Result<(&'a Edge, usize, &'a Contract), Reject> {
        self.validate_birth_authority(context, package_id, authority, explicit_transition)?;
        let (edge, definition, contract_key, contract) =
            self.admitted_edge(edge_id)
                .ok_or_else(|| Reject::UnknownEdge {
                    edge_id: Arc::clone(edge_id),
                })?;
        if edge.source() != &**context.node_id {
            return Err(Reject::WrongSource {
                edge_id: edge.id_arc(),
                expected: Arc::clone(context.node_id),
                actual: Arc::from(edge.source()),
            });
        }
        if !definition.matches_authority(authority) {
            return Err(Reject::EdgeAuthorityMismatch {
                edge_id: edge.id_arc(),
                required: definition.authority_tags().clone(),
                authority_match: definition.authority_match(),
                authority: authority.clone(),
            });
        }
        Ok((edge, contract_key, contract))
    }

    fn prove_payload_contract(
        edge: &Edge,
        contract_key: usize,
        contract: &Contract,
        content_digest: ContentDigest,
        payload: &[u8],
        proofs: &mut BTreeSet<(usize, ContentDigest)>,
    ) -> Result<(), Reject> {
        contract
            .validate(payload)
            .map_err(|source| Reject::PayloadContract {
                edge: edge.id_arc(),
                target_node: edge.target_arc(),
                contract_id: Arc::from(contract.id()),
                source,
            })?;
        proofs.insert((contract_key, content_digest));
        Ok(())
    }

    /// Proves one output and produces its accepted output and live record.
    ///
    /// `bytes` supplies payload bytes when the proof needs them: always for an
    /// outbound birth (its commitment must be witnessed) and, for a delivered
    /// output, only when no proof of the same contract and digest exists yet.
    fn admit_output<'e, E>(
        &self,
        context: &OutputProofContext<'_>,
        package_id: PackageId,
        candidate: OutputCandidate<'_>,
        proofs: &mut BTreeSet<(usize, ContentDigest)>,
        mut bytes: impl FnMut(PackageId, ContentDigest) -> Result<&'e [u8], E>,
        wrap: impl Fn(Reject) -> E,
    ) -> Result<(Output, PackageRecord), E> {
        let content_digest = match candidate.content {
            OutputContent::Bytes(payload) => ContentDigest::compute(payload),
            OutputContent::Committed { digest, .. } => digest,
        };
        let (edge_id, object_type, delivery) = match (candidate.edge_id, candidate.outbound_type) {
            (Some(edge_id), _) => {
                let (edge, contract_key, contract) = self
                    .validate_output_metadata(
                        context,
                        package_id,
                        edge_id,
                        &candidate.authority,
                        candidate.explicit_transition,
                    )
                    .map_err(&wrap)?;
                if let OutputContent::Committed { declared_type, .. } = &candidate.content
                    && declared_type.as_ref() != contract.object_type()
                {
                    return Err(wrap(Reject::PackageTypeMismatch {
                        package_id,
                        expected: Arc::from(contract.object_type()),
                        actual: Arc::clone(declared_type),
                    }));
                }
                if !proofs.contains(&(contract_key, content_digest)) {
                    let payload = bytes(package_id, content_digest)?;
                    Self::prove_payload_contract(
                        edge,
                        contract_key,
                        contract,
                        content_digest,
                        payload,
                        proofs,
                    )
                    .map_err(&wrap)?;
                }
                (
                    Some(edge.id_arc()),
                    Arc::from(contract.object_type()),
                    Some(Delivery {
                        edge_id: edge.id_arc(),
                        receiver: edge.target_arc(),
                    }),
                )
            }
            (None, Some(object_type)) => {
                self.validate_birth_authority(
                    context,
                    package_id,
                    &candidate.authority,
                    candidate.explicit_transition,
                )
                .map_err(&wrap)?;
                if !self.schema().admits_object_type(object_type) {
                    return Err(wrap(Reject::UnknownObjectType {
                        object_type: Arc::clone(object_type),
                    }));
                }
                // An outbound birth has no edge contract yet, but its retained
                // commitment must still be witnessed by bytes.
                bytes(package_id, content_digest)?;
                (None, Arc::clone(object_type), None)
            }
            (None, None) => unreachable!("an output is delivered or names its type"),
        };
        let output = Output {
            edge_id,
            object_type: Arc::clone(&object_type),
            authority: candidate.authority.clone(),
            content_digest,
        };
        let record = PackageRecord {
            object_type,
            authority: candidate.authority,
            content_digest,
            producer_node: Arc::clone(context.node_id),
            delivery,
            status: PackageStatus::Live,
        };
        Ok((output, record))
    }

    /// Evaluates one persisted activation record against `view`.
    fn evaluate_recorded<'e>(
        &self,
        view: &dyn PackageView,
        activation_id: ActivationId,
        mut activation: Activation,
        proofs: &mut BTreeSet<(usize, ContentDigest)>,
        mut payload_for: impl FnMut(PackageId, ContentDigest) -> Result<&'e [u8], StateRestoreError>,
    ) -> Result<Transition, StateRestoreError> {
        let wrap = |reject| StateRestoreError::invalid(activation_id, reject);
        let view = InputView::capture(view, activation.inputs());
        let (node_id, governing_authority) = self
            .validate_activation_header(&view, activation.trigger(), activation.result())
            .map_err(wrap)?;
        if activation.node_id != node_id {
            return Err(wrap(Reject::ExecutionNodeMismatch {
                declared: activation.node_id.clone(),
                actual: node_id,
            }));
        }
        activation.node_id = Arc::clone(&node_id);
        if let Trigger::Orig {
            node_id: trigger_node_id,
            ..
        } = &mut activation.trigger
        {
            *trigger_node_id = Arc::clone(&node_id);
        }
        let context = OutputProofContext {
            activation_id,
            node_id: &node_id,
            governing_authority: &governing_authority,
        };
        let mut outputs = BTreeMap::new();
        let mut records = Vec::with_capacity(activation.outputs.len());
        for (package_id, recorded) in &activation.outputs {
            let candidate = OutputCandidate {
                edge_id: recorded.edge_id.as_ref(),
                outbound_type: recorded.edge_id.is_none().then_some(&recorded.object_type),
                authority: recorded.authority.clone(),
                explicit_transition: false,
                content: OutputContent::Committed {
                    digest: recorded.content_digest,
                    declared_type: &recorded.object_type,
                },
            };
            let (output, record) = self.admit_output(
                &context,
                *package_id,
                candidate,
                proofs,
                &mut payload_for,
                wrap,
            )?;
            outputs.insert(*package_id, output);
            records.push((*package_id, record));
        }
        activation.outputs = outputs;
        Ok(Transition {
            base: view.binding(),
            kind: TransitionKind::Activation {
                id: activation_id,
                activation,
                outputs: records,
                inputs: view.records,
            },
        })
    }

    /// Evaluates one live proposal against `view` without mutating anything.
    ///
    /// `activation_id` must be fresh in the state behind `view`; [`State::apply`]
    /// rejects a reused identity.
    ///
    /// # Errors
    ///
    /// Returns [`Reject`] when any premise fails.
    ///
    /// # Panics
    ///
    /// Propagates a panic from trusted contract code.
    pub fn evaluate_activation(
        &self,
        view: &dyn PackageView,
        activation_id: ActivationId,
        proposal: ActivationProposal,
    ) -> Result<Transition, Reject> {
        let ActivationProposal {
            mut trigger,
            result,
            emissions,
        } = proposal;
        let view = InputView::capture(view, trigger.inputs());
        let binding = view.binding();
        self.check_binding(&binding)?;
        let (node_id, governing_authority) =
            self.validate_activation_header(&view, &trigger, &result)?;
        if let Trigger::Orig {
            node_id: trigger_node_id,
            ..
        } = &mut trigger
        {
            *trigger_node_id = Arc::clone(&node_id);
        }
        let context = OutputProofContext {
            activation_id,
            node_id: &node_id,
            governing_authority: &governing_authority,
        };
        let mut outputs = BTreeMap::new();
        let mut records = Vec::with_capacity(emissions.len());
        let mut proofs = BTreeSet::new();
        for (local_id, emission) in (0_u128..).zip(&emissions) {
            let package_id = PackageId::from_parts(activation_id, local_id);
            let (authority, explicit_transition) = match &emission.authority {
                OutputAuthority::Carry => (governing_authority.clone(), false),
                OutputAuthority::Transition(authority) => (authority.clone(), true),
            };
            let (edge_id, outbound_type) = match &emission.destination {
                EmissionDestination::Delivered(edge_id) => (Some(edge_id), None),
                EmissionDestination::Outbound(object_type) => (None, Some(object_type)),
            };
            let candidate = OutputCandidate {
                edge_id,
                outbound_type,
                authority,
                explicit_transition,
                content: OutputContent::Bytes(&emission.payload),
            };
            let (output, record) = self.admit_output(
                &context,
                package_id,
                candidate,
                &mut proofs,
                |_, _| Ok(emission.payload.as_ref()),
                |reject| reject,
            )?;
            outputs.insert(package_id, output);
            records.push((package_id, record));
        }
        Ok(Transition {
            base: binding,
            kind: TransitionKind::Activation {
                id: activation_id,
                activation: Activation {
                    node_id,
                    trigger,
                    result,
                    outputs,
                },
                outputs: records,
                inputs: view.records,
            },
        })
    }

    /// Admits one root or package-triggered activation atomically.
    ///
    /// # Errors
    ///
    /// Returns [`Reject`] without changing `state` when any premise fails.
    ///
    /// # Panics
    ///
    /// Propagates a panic from trusted contract code or failure of the system
    /// randomness source used for occurrence identities.
    pub fn activate(
        &self,
        state: &mut State,
        proposal: ActivationProposal,
    ) -> Result<ActivationId, Reject> {
        let activation_id = loop {
            let candidate = ActivationId::fresh();
            if state.activation(candidate).is_none() {
                break candidate;
            }
        };
        let transition = self.evaluate_activation(state, activation_id, proposal)?;
        state
            .apply(self, &transition)
            .expect("a transition evaluated against a state applies to it");
        Ok(activation_id)
    }
}
