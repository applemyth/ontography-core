import Oracle.Canonical
import Oracle.Trace

/-!
# The trace oracle

Reads one trace (`TRACE_FORMAT.md`) from standard input and replays its
operations with the model's `step`, starting from `State.initial`. After each
operation it writes one line of JSON: the step index, whether `step` accepted
the operation, and the canonical encoding of the resulting state, which is
the predecessor when the operation is rejected.

The oracle adds no rule of its own: the validators and the commitment
function come from the trace, and every decision is `step`'s.

Exit status: 0 after replaying every operation, 2 for a malformed trace.
-/

open Lean (Json)
open Ontography

def main : IO UInt32 := do
  let input ← (← IO.getStdin).readToEnd
  match Oracle.decodeTrace input with
  | .error e =>
    IO.eprintln s!"oracle: malformed trace: {e}"
    return 2
  | .ok trace =>
    let stdout ← IO.getStdout
    let mut state := State.initial trace.definition
    for (op, index) in trace.ops.zipIdx do
      let (accepted, next) :=
        match step trace.accepts trace.commit trace.definition state op with
        | some next => (true, next)
        | none => (false, state)
      state := next
      stdout.putStrLn <| Json.compress <| Json.mkObj [
        ("step", Oracle.jnat index),
        ("accepted", .bool accepted),
        ("state", Oracle.encodeState state)]
    stdout.flush
    return 0
