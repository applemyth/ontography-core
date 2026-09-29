//! The kernel against its Lean model. Runs of the in-memory kernel over a few
//! fixed definitions are recorded as traces (`formal/TRACE_FORMAT.md`)
//! holding the kernel's outcome, current definition, and canonical state
//! after every operation. The Lean oracle
//! (`formal/Oracle`) replays each trace with the model's `sysStep`; acceptance,
//! the definition, and the state must agree at every step. Error variants are
//! not compared, since the model's rules carry no rejection reason.
//!
//! Operations are activations, transfers, explicit retirements, rewrites
//! (`prepare_rewrite` and `commit_rewrite` of a graph edit), and extensions
//! (`prepare_extension` and `commit_extension`). Every trace runs under the
//! same edit policy, which refuses exactly the principal `"denied"`. Random
//! edits are shaped from the current graph's own node and edge kinds. A
//! required prefix pins the rare cases before random exploration: the
//! scenarios of `formal/Ontography/Examples.lean`, each its own run, and on
//! each fixture the fixed-graph cases and, on the coverage fixture, every way
//! a rewrite or extension can fail. A plan committed after its state changed must be
//! refused as stale, which the harness checks against the kernel alone,
//! because the model has no plans. Random choices index packages in birth
//! order, so a seed fixes the operation sequence even though the kernel draws
//! activation identities at random.
//!
//! The oracle is the executable named by `ONTOGRAPHY_LEAN_ORACLE`, by default
//! `formal/.lake/build/bin/oracle` (`cd formal && lake build oracle`). Without
//! it the tests skip loudly, or fail when `ONTOGRAPHY_REQUIRE_LEAN_ORACLE=1`.
//! `ONTOGRAPHY_LEAN_ORACLE_SEEDS` adds seeds, as in `7,40..60`. A disagreement
//! writes its trace to `target/lean-oracle/<seed>.json`. The hand-written
//! regression traces in `tests/lean_traces/` replay on every run, and
//! `tests/lean_traces/disagreements/` keeps minimized known disagreements.

#[path = "lean_oracle/examples.rs"]
mod examples;
#[path = "lean_oracle/explore.rs"]
mod explore;
#[path = "lean_oracle/fixtures.rs"]
mod fixtures;
#[path = "lean_oracle/format.rs"]
mod format;
#[path = "lean_oracle/oracle.rs"]
mod oracle;
#[path = "lean_oracle/run.rs"]
mod run;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use crate::explore::{Rng, random_step};
use crate::fixtures::FIXTURES;
use crate::format::KnownDisagreement;
use crate::oracle::{
    check, committed_traces, describe, first_mismatch, oracle, replay_in_kernel, replay_in_model,
    write_artifact,
};
use crate::run::Run;

/// The fixed seeds; `ONTOGRAPHY_LEAN_ORACLE_SEEDS` adds more.
const SEEDS: std::ops::RangeInclusive<u64> = 1..=18;

/// Random operations after each run's required prefix.
const RANDOM_STEPS: usize = 150;

fn random_run(seed: u64) -> Run {
    let fixture = &FIXTURES[usize::try_from(seed % 3).unwrap()];
    let setup = (fixture.setup)();
    let mut run = Run::new(
        format!("{}-{seed}", fixture.name),
        Some(seed),
        setup.definition.clone(),
        setup.all_validators(),
    );
    (fixture.prefix)(&mut run);
    let mut rng = Rng::new(seed);
    for _ in 0..RANDOM_STEPS {
        random_step(&mut run, &mut rng, true);
    }
    run
}

fn seeds() -> BTreeSet<u64> {
    let mut seeds: BTreeSet<u64> = SEEDS.collect();
    let Ok(extra) = std::env::var("ONTOGRAPHY_LEAN_ORACLE_SEEDS") else {
        return seeds;
    };
    let parse = |text: &str| -> u64 {
        text.trim().parse().unwrap_or_else(|_| {
            panic!("ONTOGRAPHY_LEAN_ORACLE_SEEDS: {text:?} is not a seed; use a list like 7,40..60")
        })
    };
    for item in extra.split(',').filter(|item| !item.trim().is_empty()) {
        if let Some((start, end)) = item.split_once("..=") {
            seeds.extend(parse(start)..=parse(end));
        } else if let Some((start, end)) = item.split_once("..") {
            seeds.extend(parse(start)..parse(end));
        } else {
            seeds.insert(parse(item));
        }
    }
    seeds
}

#[derive(Default)]
struct Tally {
    traces: usize,
    ops: usize,
    stale: usize,
    kinds: BTreeMap<&'static str, (usize, usize)>,
}

impl Tally {
    fn add(&mut self, run: &Run) {
        self.traces += 1;
        self.stale += run.stale;
        for (op, outcome) in run.ops.iter().zip(&run.outcomes) {
            self.ops += 1;
            let (accepted, rejected) = self.kinds.entry(op.kind()).or_default();
            if outcome.accepted {
                *accepted += 1;
            } else {
                *rejected += 1;
            }
        }
    }

    fn report(&self) -> String {
        let mut report = format!(
            "the kernel and the Lean model agree on {} traces of {} ops:\n",
            self.traces, self.ops
        );
        for (kind, (accepted, rejected)) in &self.kinds {
            writeln!(
                report,
                "  {kind:<9} {accepted:>6} accepted {rejected:>6} rejected"
            )
            .unwrap();
        }
        writeln!(
            report,
            "  and the kernel refused {} stale plans, which the model does not have",
            self.stale
        )
        .unwrap();
        report
    }
}

#[test]
fn kernel_and_lean_model_agree_on_random_traces() {
    let Some(oracle) = oracle() else {
        return;
    };
    let mut tally = Tally::default();
    for run in examples::runs() {
        check(&oracle, &run);
        tally.add(&run);
    }
    for seed in seeds() {
        let run = random_run(seed);
        check(&oracle, &run);
        tally.add(&run);
    }
    println!("{}", tally.report());
    for kind in ["activate", "transfer", "retire", "rewrite", "extend"] {
        let (accepted, rejected) = tally.kinds.get(kind).copied().unwrap_or_default();
        assert!(
            accepted > 0 && rejected > 0,
            "{kind}: {accepted} accepted and {rejected} rejected; both must occur"
        );
    }
    assert!(tally.stale > 0, "no stale plan was refused");
}

#[test]
fn kernel_and_lean_model_agree_on_regression_traces() {
    let traces = committed_traces("tests/lean_traces");
    assert!(
        !traces.is_empty(),
        "no regression traces in tests/lean_traces"
    );
    let runs: Vec<Run> = traces
        .iter()
        .map(|trace| {
            assert!(
                trace.known_disagreement.is_none(),
                "{}: a known disagreement belongs in tests/lean_traces/disagreements",
                trace.name
            );
            replay_in_kernel(trace)
        })
        .collect();
    let Some(oracle) = oracle() else {
        return;
    };
    for run in &runs {
        check(&oracle, run);
    }
}

#[test]
fn known_disagreements_still_reproduce() {
    let traces = committed_traces("tests/lean_traces/disagreements");
    if traces.is_empty() {
        return;
    }
    let runs: Vec<(Run, KnownDisagreement)> = traces
        .iter()
        .map(|trace| {
            let known = trace.known_disagreement.clone().unwrap_or_else(|| {
                panic!(
                    "{}: a trace in tests/lean_traces/disagreements names its known_disagreement",
                    trace.name
                )
            });
            (replay_in_kernel(trace), known)
        })
        .collect();
    let Some(oracle) = oracle() else {
        return;
    };
    for (run, known) in &runs {
        let model = replay_in_model(&oracle, run).unwrap_or_else(|failure| panic!("{failure}"));
        let Some(mismatch) = first_mismatch(run, &model) else {
            panic!(
                "{}: the known disagreement no longer reproduces; the kernel and the model \
                 now agree, so move the trace to tests/lean_traces without known_disagreement",
                run.name
            );
        };
        if mismatch.step != known.step {
            let artifact = write_artifact(run);
            panic!(
                "{}: the known disagreement moved from step {}\n{}",
                run.name,
                known.step,
                describe(run, &mismatch, &artifact)
            );
        }
    }
}
