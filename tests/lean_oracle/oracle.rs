//! The Lean oracle: running it on a trace, comparing its states with the
//! kernel's, and replaying committed traces.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use ontography::{ContentDigest, PackageId};
use serde_json::{Value, json};

use crate::format::{FORMAT, Trace, TraceOp, TriggerSpec, parse_package, unhex};
use crate::run::{Identity, Run, verdict};

/// At most this many differing state paths are reported for one step.
const DIFFERENCE_LIMIT: usize = 16;

/// The oracle executable, or `None` after a loud skip notice when it is
/// absent and not required.
pub fn oracle() -> Option<PathBuf> {
    let path = std::env::var_os("ONTOGRAPHY_LEAN_ORACLE").map_or_else(
        || Path::new(env!("CARGO_MANIFEST_DIR")).join("formal/.lake/build/bin/oracle"),
        PathBuf::from,
    );
    if path.is_file() {
        return Some(path);
    }
    assert!(
        std::env::var("ONTOGRAPHY_REQUIRE_LEAN_ORACLE").as_deref() != Ok("1"),
        "ONTOGRAPHY_REQUIRE_LEAN_ORACLE=1, but the Lean oracle {} does not exist; \
         build it with `cd formal && lake build oracle`",
        path.display()
    );
    eprintln!(
        "\n\
         ************************************************************************\n\
         SKIPPED: the Lean oracle {} does not exist, so the kernel is NOT being\n\
         checked against the Lean model. Build it with `cd formal && lake build\n\
         oracle`, or set ONTOGRAPHY_REQUIRE_LEAN_ORACLE=1 to fail instead.\n\
         ************************************************************************\n",
        path.display()
    );
    None
}

/// Replays a run's trace with the oracle: acceptance and canonical state per
/// step, or why the oracle did not produce them.
pub fn replay_in_model(oracle: &Path, run: &Run) -> Result<Vec<(bool, Value)>, String> {
    let trace = run.trace();
    let mut child = Command::new(oracle)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("cannot run the Lean oracle {}: {error}", oracle.display()))?;
    let input = serde_json::to_vec(&trace).unwrap();
    let written = child
        .stdin
        .take()
        .expect("the oracle's stdin is piped")
        .write_all(&input);
    let output = child
        .wait_with_output()
        .map_err(|error| format!("the Lean oracle did not finish: {error}"))?;
    if written.is_err() || !output.status.success() {
        return Err(format!(
            "the Lean oracle failed on trace {} ({}, {written:?}): {}",
            trace.name,
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let stdout = String::from_utf8(output.stdout).map_err(|error| error.to_string())?;
    let steps = stdout
        .lines()
        .enumerate()
        .map(|(step, line)| {
            let mut result: Value = serde_json::from_str(line)
                .map_err(|error| format!("oracle line {step} is not JSON: {error}"))?;
            if result["step"] != json!(step) {
                return Err(format!(
                    "oracle line {step} reports step {}",
                    result["step"]
                ));
            }
            let accepted = result["accepted"]
                .as_bool()
                .ok_or_else(|| format!("oracle line {step} reports no acceptance"))?;
            Ok((accepted, result["state"].take()))
        })
        .collect::<Result<Vec<_>, String>>()?;
    if steps.len() != trace.ops.len() {
        return Err(format!(
            "the oracle replayed {} of the {} ops of trace {}",
            steps.len(),
            trace.ops.len(),
            trace.name
        ));
    }
    Ok(steps)
}

pub struct Mismatch {
    pub step: usize,
    kernel_accepted: bool,
    model_accepted: bool,
    differences: Vec<String>,
}

/// The first step at which the kernel's outcome or state differs from the
/// model's.
pub fn first_mismatch(run: &Run, model: &[(bool, Value)]) -> Option<Mismatch> {
    run.outcomes
        .iter()
        .zip(model)
        .enumerate()
        .find(|(_, (kernel, (accepted, state)))| {
            kernel.accepted != *accepted || !kernel.state.matches(state)
        })
        .map(|(step, (kernel, (accepted, state)))| {
            let mut differences = Vec::new();
            difference(
                "state",
                Some(&kernel.state.to_value()),
                Some(state),
                &mut differences,
            );
            Mismatch {
                step,
                kernel_accepted: kernel.accepted,
                model_accepted: *accepted,
                differences,
            }
        })
}

/// Entries keyed by their identity, when every element of an array has one.
fn keyed(items: &[Value]) -> Option<BTreeMap<String, &Value>> {
    let keyed: BTreeMap<String, &Value> = items
        .iter()
        .map(|item| {
            ["id", "node", "edge"]
                .iter()
                .find_map(|field| item.get(*field))
                .map(|id| (id.to_string(), item))
        })
        .collect::<Option<_>>()?;
    (keyed.len() == items.len()).then_some(keyed)
}

fn show(value: Option<&Value>) -> String {
    value.map_or_else(|| "absent".to_owned(), Value::to_string)
}

/// Appends the paths at which two canonical values differ.
fn difference(path: &str, kernel: Option<&Value>, model: Option<&Value>, out: &mut Vec<String>) {
    if kernel == model || out.len() >= DIFFERENCE_LIMIT {
        return;
    }
    match (kernel, model) {
        (Some(Value::Object(kernel)), Some(Value::Object(model))) => {
            let keys: BTreeSet<&String> = kernel.keys().chain(model.keys()).collect();
            for key in keys {
                difference(
                    &format!("{path}.{key}"),
                    kernel.get(key),
                    model.get(key),
                    out,
                );
            }
        }
        (Some(Value::Array(kernel)), Some(Value::Array(model))) => {
            if let (Some(kernel), Some(model)) = (keyed(kernel), keyed(model)) {
                let keys: BTreeSet<&String> = kernel.keys().chain(model.keys()).collect();
                for key in keys {
                    difference(
                        &format!("{path}[{key}]"),
                        kernel.get(key).copied(),
                        model.get(key).copied(),
                        out,
                    );
                }
            } else {
                for index in 0..kernel.len().max(model.len()) {
                    difference(
                        &format!("{path}[{index}]"),
                        kernel.get(index),
                        model.get(index),
                        out,
                    );
                }
            }
        }
        _ => out.push(format!(
            "{path}: kernel {}, model {}",
            show(kernel),
            show(model)
        )),
    }
}

/// Writes the run's trace, with the kernel's outcome and state after every
/// op, to `target/lean-oracle/<seed>.json`, or `<name>.json` without a seed.
pub fn write_artifact(run: &Run) -> PathBuf {
    let stem = run
        .seed
        .map_or_else(|| run.name.clone(), |seed| seed.to_string());
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("target/lean-oracle")
        .join(format!("{stem}.json"));
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(
        &path,
        serde_json::to_string_pretty(&run.annotated()).unwrap(),
    )
    .unwrap();
    path
}

pub fn describe(run: &Run, mismatch: &Mismatch, artifact: &Path) -> String {
    let op = serde_json::to_string(&run.ops[mismatch.step]).unwrap();
    let mut message = format!(
        "the kernel and the Lean model disagree on trace {} at step {}\n  op: {op}\n",
        run.name, mismatch.step
    );
    if mismatch.kernel_accepted != mismatch.model_accepted {
        writeln!(
            message,
            "  the kernel {} it and the model {} it",
            verdict(mismatch.kernel_accepted),
            verdict(mismatch.model_accepted)
        )
        .unwrap();
    }
    for difference in &mismatch.differences {
        writeln!(message, "  {difference}").unwrap();
    }
    writeln!(message, "  trace written to {}", artifact.display()).unwrap();
    message
}

/// Replays the run in the model and requires agreement at every step.
pub fn check(oracle: &Path, run: &Run) {
    let model = replay_in_model(oracle, run).unwrap_or_else(|failure| {
        let artifact = write_artifact(run);
        panic!("{failure}\n  trace written to {}", artifact.display())
    });
    if let Some(mismatch) = first_mismatch(run, &model) {
        let artifact = write_artifact(run);
        panic!("{}", describe(run, &mismatch, &artifact));
    }
}

pub fn committed_traces(directory: &str) -> Vec<Trace> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join(directory);
    let Ok(entries) = std::fs::read_dir(&directory) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .map(|entry| entry.unwrap().path())
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "json")
        })
        .collect();
    paths.sort();
    paths
        .iter()
        .map(|path| {
            let text = std::fs::read_to_string(path).unwrap();
            serde_json::from_str(&text)
                .unwrap_or_else(|error| panic!("{} is not a trace: {error}", path.display()))
        })
        .collect()
}

/// Replays a committed trace on the kernel under its recorded identities,
/// checking its digest table and every expectation it states.
pub fn replay_in_kernel(file: &Trace) -> Run {
    assert_eq!(file.format, FORMAT, "{}: unsupported format", file.name);
    for (payload, digest) in &file.digests {
        assert_eq!(
            &ContentDigest::compute(&unhex(payload)).to_string(),
            digest,
            "{}: the digest table entry for {payload} is not ContentDigest::compute",
            file.name
        );
    }
    let mut run = Run::new(
        file.name.clone(),
        file.seed,
        file.definition.clone(),
        file.grammar.clone(),
        file.validators.clone(),
    );
    for (step, op) in file.ops.iter().enumerate() {
        if let TraceOp::Activate {
            trigger: TriggerSpec::Pkgs(inputs),
            ..
        } = op
        {
            let distinct: BTreeSet<PackageId> = inputs.iter().map(parse_package).collect();
            assert_eq!(
                distinct.len(),
                inputs.len(),
                "{}: step {step} repeats an input; a trigger names a set",
                file.name
            );
        }
        let accepted = run.record(op.clone(), Identity::Recorded);
        if let Some(expect) = op.expect() {
            assert_eq!(
                accepted,
                expect.accepted,
                "{}: the kernel {} step {step}, which the trace expects to be {}",
                file.name,
                verdict(accepted),
                verdict(expect.accepted)
            );
            if let Some(state) = &expect.state {
                assert!(
                    run.outcomes[step].state.matches(state),
                    "{}: the kernel's state after step {step} differs from the trace's",
                    file.name
                );
            }
        }
    }
    for payload in run.digests.keys() {
        assert!(
            file.digests.contains_key(payload),
            "{}: payload {payload} has no entry in the digest table",
            file.name
        );
    }
    run.digests.clone_from(&file.digests);
    run
}
