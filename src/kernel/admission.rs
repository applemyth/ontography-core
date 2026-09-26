//! Atomic live and restored admission proof.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::graph::{Authority, ContentDigest, Contract, Edge, IngressMode, Payload};

use super::admission_api::{
    ActivationProposal, EmissionDestination, OutputAuthority, Reject, StateRestoreError,
    TriggerRequest, TriggerWitness,
};
use super::definition::Kernel;
use super::frontier::{Delivery, Phase};
use super::occurrence::{
    Activation, ActivationId, AdmissionDelta, Output, PackageId, State, StateParts, Trigger,
};

struct ValidatedPackageInputs<'a> {
    node_id: Arc<str>,
    governing_authority: Authority,
    ingress_mode: IngressMode,
    incoming_edge_ids: &'a BTreeSet<Arc<str>>,
    realized_edge_ids: BTreeSet<Arc<str>>,
}

struct OutputProofContext<'a> {
    activation_id: ActivationId,
    node_id: &'a Arc<str>,
    governing_authority: &'a Authority,
}

#[derive(Clone, Copy)]
pub(crate) struct PendingInput<'a> {
    pub(crate) edge_id: &'a Arc<str>,
    pub(crate) node_id: &'a Arc<str>,
    pub(crate) authority: &'a Authority,
}

pub(crate) enum PackageObservation<'a> {
    Missing,
    Pending(PendingInput<'a>),
    Consumed(ActivationId),
    Retired,
    Outbound,
}

pub(crate) trait AdmissionView {
    fn package(&self, package_id: PackageId) -> PackageObservation<'_>;
}

impl AdmissionView for State {
    fn package(&self, package_id: PackageId) -> PackageObservation<'_> {
        let Some(package) = self.package(package_id) else {
            return PackageObservation::Missing;
        };
        if let Some(consumer) = self.package_consumer(package_id) {
            return PackageObservation::Consumed(consumer);
        }
        let Some(position) = self.positions.get(&package_id) else {
            debug_assert!(
                self.retirements.contains_key(&package_id),
                "an unconsumed package without a position has a retirement record"
            );
            return PackageObservation::Retired;
        };
        if position.phase != Phase::In {
            return PackageObservation::Outbound;
        }
        let Some(delivery) = self.deliveries.get(&package_id) else {
            return PackageObservation::Outbound;
        };
        PackageObservation::Pending(PendingInput {
            edge_id: &delivery.edge_id,
            node_id: &position.holder,
            authority: package.authority(),
        })
    }
}

fn pending_input(
    state: &dyn AdmissionView,
    package_id: PackageId,
) -> Result<PendingInput<'_>, Reject> {
    match state.package(package_id) {
        PackageObservation::Missing => Err(Reject::UnknownPackage { package_id }),
        PackageObservation::Consumed(activation_id) => Err(Reject::AlreadyActivated {
            package_id,
            activation_id,
        }),
        PackageObservation::Pending(input) => Ok(input),
        PackageObservation::Retired => Err(Reject::PackageRetired { package_id }),
        PackageObservation::Outbound => Err(Reject::PackageNotDelivered { package_id }),
    }
}

impl Kernel {
    /// Restores accepted activation records under one fixed graph definition.
    ///
    /// This API does not restore graph rewrites, explicit transfers, retirements,
    /// or vocabulary extensions. Exporting
    /// such a state through [`State::to_parts`] is rejected. Restoration
    /// topologically replays the realized occurrence graph. Every
    /// activation, package edge, payload contract, carried authority, and
    /// static edge projection is revalidated against this kernel. Package
    /// payload bytes are supplied as external evidence keyed by their accepted
    /// content digests; the restored state retains only those digests.
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
            let admitted = self.validate_restored_activation(
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
            state.commit(admitted);
        }
        debug_assert!(activations.is_empty());
        Ok(state)
    }

    /// Validates and snapshots one exact package-trigger candidate without
    /// reserving, consuming, or otherwise changing the state.
    ///
    /// The returned [`TriggerWitness`] binds the package identities to immutable
    /// package snapshots, their common target and authority, and the target's
    /// admitted ingress facts. It is point-in-time evidence only: another
    /// activation may consume an input after preparation. Callers must still
    /// submit an [`ActivationProposal`] through [`Self::activate`], which
    /// revalidates every trigger premise against the then-current state.
    ///
    /// # Errors
    ///
    /// Returns [`Reject`] when the state belongs to another definition or the
    /// package set is not currently a legal trigger under the target node's
    /// ingress mode.
    pub fn prepare_trigger<I>(
        &self,
        state: &State,
        package_ids: I,
    ) -> Result<TriggerWitness, Reject>
    where
        I: IntoIterator<Item = PackageId>,
    {
        self.check_state(state)?;
        let package_ids = package_ids.into_iter().collect::<BTreeSet<_>>();
        let validated = self.validate_package_inputs(state, &package_ids)?;
        let packages = package_ids
            .iter()
            .map(|package_id| -> Result<_, Reject> {
                let package = state.package(*package_id).ok_or(Reject::UnknownPackage {
                    package_id: *package_id,
                })?;
                Ok((*package_id, package.clone()))
            })
            .collect::<Result<_, _>>()?;

        Ok(TriggerWitness {
            definition_id: self.id().clone(),
            definition_fingerprint: *self.fingerprint(),
            package_ids,
            packages,
            node_id: validated.node_id,
            authority: validated.governing_authority,
            ingress_mode: validated.ingress_mode,
            incoming_edge_ids: BTreeSet::clone(validated.incoming_edge_ids),
            realized_edge_ids: validated.realized_edge_ids,
        })
    }

    fn restoration_order(
        activations: &BTreeMap<ActivationId, Activation>,
    ) -> Result<Vec<ActivationId>, StateRestoreError> {
        let mut children = BTreeMap::<ActivationId, Vec<ActivationId>>::new();
        let mut indegree = BTreeMap::<ActivationId, usize>::new();
        let mut ready = BTreeSet::new();
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

            match activation.trigger() {
                Trigger::Orig { .. } => {
                    indegree.insert(*activation_id, 0);
                    ready.insert(*activation_id);
                }
                Trigger::Pkgs { package_ids } => {
                    if package_ids.is_empty() {
                        return Err(StateRestoreError::invalid(
                            *activation_id,
                            Reject::EmptyPackageTrigger,
                        ));
                    }

                    let mut parent_count = 0;
                    let mut previous_parent = None;
                    for package_id in package_ids {
                        let parent = package_id.producer();
                        let producer = activations.get(&parent).ok_or_else(|| {
                            StateRestoreError::invalid(
                                *activation_id,
                                Reject::UnknownPackage {
                                    package_id: *package_id,
                                },
                            )
                        })?;
                        if !producer.package_outputs().contains_key(package_id) {
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
                        if previous_parent != Some(parent) {
                            // PackageId ordering groups a trigger's packages by producer.
                            children.entry(parent).or_default().push(*activation_id);
                            parent_count += 1;
                            previous_parent = Some(parent);
                        }
                    }

                    indegree.insert(*activation_id, parent_count);
                }
            }
        }

        let mut order = Vec::with_capacity(activations.len());
        while let Some(activation_id) = ready.pop_first() {
            order.push(activation_id);
            if let Some(dependents) = children.get(&activation_id) {
                for dependent in dependents {
                    let degree = indegree
                        .get_mut(dependent)
                        .expect("dependent activation has an indegree");
                    *degree -= 1;
                    if *degree == 0 {
                        ready.insert(*dependent);
                    }
                }
            }
        }

        if order.len() != activations.len() {
            let activation_id = indegree
                .iter()
                .find_map(|(activation_id, degree)| (*degree != 0).then_some(*activation_id))
                .expect("an incomplete traversal leaves an activation");
            return Err(StateRestoreError::CausalCycle { activation_id });
        }
        Ok(order)
    }

    fn validate_package_inputs<'a>(
        &'a self,
        state: &dyn AdmissionView,
        package_ids: &BTreeSet<PackageId>,
    ) -> Result<ValidatedPackageInputs<'a>, Reject> {
        let first_id = package_ids
            .first()
            .copied()
            .ok_or(Reject::EmptyPackageTrigger)?;
        let first = pending_input(state, first_id)?;
        let node_id = Arc::clone(first.node_id);
        let governing_authority = first.authority.clone();
        let mut edge_ids = BTreeSet::new();

        for package_id in package_ids {
            let input = if *package_id == first_id {
                first
            } else {
                pending_input(state, *package_id)?
            };
            if input.node_id.as_ref() != node_id.as_ref() {
                return Err(Reject::JoinTargetMismatch {
                    package_id: *package_id,
                    expected: Arc::clone(&node_id),
                    actual: Arc::clone(input.node_id),
                });
            }
            if input.authority != &governing_authority {
                return Err(Reject::JoinAuthorityMismatch {
                    package_id: *package_id,
                    expected: governing_authority.clone(),
                    actual: input.authority.clone(),
                });
            }
            if !edge_ids.insert(Arc::clone(input.edge_id)) {
                return Err(Reject::DuplicateJoinEdge {
                    node_id: Arc::clone(&node_id),
                    edge_id: Arc::clone(input.edge_id),
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
                        expected: BTreeSet::clone(incoming_edge_ids),
                        actual: edge_ids,
                    });
                }
            }
            IngressMode::Any => {}
        }

        Ok(ValidatedPackageInputs {
            node_id,
            governing_authority,
            ingress_mode,
            incoming_edge_ids,
            realized_edge_ids: edge_ids,
        })
    }

    fn validate_activation_header(
        &self,
        state: &dyn AdmissionView,
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
                let validated = self.validate_package_inputs(state, package_ids)?;
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
        let inserted = proofs.insert((contract_key, content_digest));
        debug_assert!(inserted, "payload contract proof was previously absent");
        Ok(())
    }

    fn validate_restored_activation<'evidence>(
        &self,
        state: &State,
        activation_id: ActivationId,
        mut activation: Activation,
        payload_proofs: &mut BTreeSet<(usize, ContentDigest)>,
        mut payload_for: impl FnMut(
            PackageId,
            ContentDigest,
        ) -> Result<&'evidence [u8], StateRestoreError>,
    ) -> Result<AdmissionDelta, StateRestoreError> {
        let (node_id, governing_authority) = self
            .validate_activation_header(state, activation.trigger(), activation.result())
            .map_err(|source| StateRestoreError::invalid(activation_id, source))?;
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

        let mut package_targets = Vec::with_capacity(activation.package_outputs().len());
        let mut deliveries = BTreeMap::new();
        for (package_id, output) in &mut activation.outputs {
            let content_digest = output.content_digest();
            if let Some(edge_id) = &output.edge_id {
                let (edge, contract_key, contract) = self
                    .validate_output_metadata(
                        &context,
                        *package_id,
                        edge_id,
                        output.authority(),
                        false,
                    )
                    .map_err(|source| StateRestoreError::invalid(activation_id, source))?;
                if output.object_type() != contract.object_type() {
                    return Err(StateRestoreError::invalid(
                        activation_id,
                        Reject::PackageTypeMismatch {
                            package_id: *package_id,
                            expected: Arc::from(contract.object_type()),
                            actual: output.object_type.clone(),
                        },
                    ));
                }
                if !payload_proofs.contains(&(contract_key, content_digest)) {
                    let payload = payload_for(*package_id, content_digest)?;
                    Self::prove_payload_contract(
                        edge,
                        contract_key,
                        contract,
                        content_digest,
                        payload,
                        payload_proofs,
                    )
                    .map_err(|source| StateRestoreError::invalid(activation_id, source))?;
                }
                output.edge_id = Some(edge.id_arc());
                package_targets.push((*package_id, edge.target_arc()));
                deliveries.insert(
                    *package_id,
                    Delivery {
                        edge_id: edge.id_arc(),
                        source: Arc::clone(&node_id),
                        receiver: edge.target_arc(),
                    },
                );
            } else {
                self.validate_birth_authority(&context, *package_id, output.authority(), false)
                    .map_err(|source| StateRestoreError::invalid(activation_id, source))?;
                let object_type = &output.object_type;
                if !self.schema().admits_object_type(object_type) {
                    return Err(StateRestoreError::invalid(
                        activation_id,
                        Reject::UnknownObjectType {
                            object_type: object_type.clone(),
                        },
                    ));
                }
                // Outbound births have no edge contract yet, but their retained
                // payload commitment still requires matching evidence.
                payload_for(*package_id, content_digest)?;
                package_targets.push((*package_id, Arc::clone(&node_id)));
            }
        }

        Ok(AdmissionDelta {
            id: activation_id,
            node_id,
            package_targets,
            deliveries,
            activation,
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
        self.check_state(state)?;
        if state.revision == u64::MAX {
            return Err(Reject::RevisionExhausted);
        }
        let admitted = self.evaluate_against(state, proposal, || {
            loop {
                let candidate = ActivationId::fresh();
                if state.activation(candidate).is_none() {
                    break candidate;
                }
            }
        })?;
        Ok(state.commit(admitted))
    }

    /// Evaluates without mutation; the owner must conditionally commit the delta.
    pub(crate) fn evaluate(
        &self,
        state: &dyn AdmissionView,
        activation_id: ActivationId,
        proposal: ActivationProposal,
    ) -> Result<AdmissionDelta, Reject> {
        self.evaluate_against(state, proposal, || activation_id)
    }

    fn evaluate_against(
        &self,
        state: &dyn AdmissionView,
        proposal: ActivationProposal,
        activation_id: impl FnOnce() -> ActivationId,
    ) -> Result<AdmissionDelta, Reject> {
        let ActivationProposal {
            trigger,
            result,
            emissions,
        } = proposal;
        let mut trigger = match trigger {
            TriggerRequest::Root { node_id, authority } => Trigger::Orig { node_id, authority },
            TriggerRequest::Packages(package_ids) => Trigger::Pkgs { package_ids },
        };
        let (node_id, governing_authority) =
            self.validate_activation_header(state, &trigger, &result)?;
        if let Trigger::Orig {
            node_id: trigger_node_id,
            ..
        } = &mut trigger
        {
            *trigger_node_id = Arc::clone(&node_id);
        }

        let activation_id = activation_id();
        let mut outputs = BTreeMap::new();
        let mut package_targets = Vec::with_capacity(emissions.len());
        let mut deliveries = BTreeMap::new();
        let mut payload_proofs = BTreeSet::new();
        let context = OutputProofContext {
            activation_id,
            node_id: &node_id,
            governing_authority: &governing_authority,
        };
        for (local_id, emission) in (0_u128..).zip(emissions) {
            let package_id = PackageId::from_parts(activation_id, local_id);
            let (authority, explicit_transition) = match emission.authority {
                OutputAuthority::Carry => (governing_authority.clone(), false),
                OutputAuthority::Transition(authority) => (authority, true),
            };
            let payload = emission.payload;
            let content_digest = ContentDigest::compute(&payload);
            let (edge_id, object_type, holder) = match emission.destination {
                EmissionDestination::Delivered(edge_id) => {
                    let (edge, contract_key, contract) = self.validate_output_metadata(
                        &context,
                        package_id,
                        &edge_id,
                        &authority,
                        explicit_transition,
                    )?;
                    if !payload_proofs.contains(&(contract_key, content_digest)) {
                        Self::prove_payload_contract(
                            edge,
                            contract_key,
                            contract,
                            content_digest,
                            &payload,
                            &mut payload_proofs,
                        )?;
                    }
                    deliveries.insert(
                        package_id,
                        Delivery {
                            edge_id: edge.id_arc(),
                            source: Arc::clone(&node_id),
                            receiver: edge.target_arc(),
                        },
                    );
                    (
                        Some(edge.id_arc()),
                        Arc::from(contract.object_type()),
                        edge.target_arc(),
                    )
                }
                EmissionDestination::Outbound(object_type) => {
                    self.validate_birth_authority(
                        &context,
                        package_id,
                        &authority,
                        explicit_transition,
                    )?;
                    if !self.schema().admits_object_type(&object_type) {
                        return Err(Reject::UnknownObjectType { object_type });
                    }
                    (None, object_type, Arc::clone(&node_id))
                }
            };
            let previous = outputs.insert(
                package_id,
                Output {
                    edge_id,
                    object_type,
                    authority,
                    content_digest,
                },
            );
            debug_assert!(previous.is_none());
            package_targets.push((package_id, holder));
        }

        Ok(AdmissionDelta {
            id: activation_id,
            node_id,
            activation: Activation {
                trigger,
                result,
                outputs,
            },
            package_targets,
            deliveries,
        })
    }

    fn check_state(&self, state: &State) -> Result<(), Reject> {
        if self.id() == state.definition_id()
            && self.fingerprint() == state.definition_fingerprint()
        {
            return Ok(());
        }
        Err(Reject::StateMismatch {
            expected_id: self.id().clone(),
            actual_id: state.definition_id().clone(),
            expected_fingerprint: *self.fingerprint(),
            actual_fingerprint: *state.definition_fingerprint(),
        })
    }
}
