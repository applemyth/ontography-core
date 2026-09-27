import Ontography.System

/-!
# Examples

Kernel regression tests from `tests/frontier_rewrite.rs`, replayed in the model. Each
`#guard` evaluates the model when this file builds, so a change to the law that alters one of
these outcomes fails the build. The fixtures mirror the tests' shared support: every node has
type `n`, result contract `result`, and a root rule with authority `{run}`; edges carry
contract `payload`, `deny`, or `other`.
-/

namespace Ontography.Examples

def payload : Bytes := [1, 2, 3]

/-- `result` and `other` accept everything, `payload` accepts exactly `payload`, and `deny`
accepts nothing. -/
def accepts : ContractId → Bytes → Bool := fun c b =>
  c == "result" || c == "other" || (c == "payload" && b == payload)

/-- A stand-in commitment; only equality of commitments matters to the rules. -/
def commit : Bytes → Digest := fun b => toString b

def evidence : List (Digest × Bytes) := [(commit payload, payload)]

def kernel (nodes : List NodeId) (edges : List (EdgeId × NodeId × NodeId × ContractId))
    (ingress : NodeId → Ingress := fun _ => .any) : Definition where
  schema := ⟨["n"], ["t", "other"], ["run", "other"]⟩
  contracts := [⟨"result", "t"⟩, ⟨"payload", "t"⟩, ⟨"deny", "t"⟩, ⟨"other", "other"⟩]
  nodes := nodes
  edges := edges.map fun (e, s, t, _) => ⟨e, s, t⟩
  nodeDefs := nodes.map fun v => ⟨v, ["n"], "result", ingress v⟩
  edgeDefs := edges.map fun (e, _, _, c) => ⟨e, ["flow"], ["n"], ["n"], c, ["run"], .anyOf⟩
  transitions := []
  roots := nodes.map fun v => ⟨v, ["run"]⟩

def fragment (Δ : Definition) : Fragment :=
  ⟨Δ.nodes, Δ.edges, Δ.nodeDefs, Δ.edgeDefs, Δ.transitions, Δ.roots⟩

/-- A production from `L` to `R` with interface `K`, and the identity-symbol match of it. -/
def rule (id : String) (L R : Definition) (kn : List NodeId) (ke : List EdgeId) :
    Production × RewriteRequest :=
  (⟨id, fragment L, kn, ke, fragment R⟩,
    ⟨id, ⟨L.nodes.map fun v => (v, v), L.edges.map fun e => (e.id, e.id),
      (R.nodes.filter (· ∉ kn)).map fun v => (v, v),
      ((R.edges.map (·.id)).filter (· ∉ ke)).map fun e => (e, e)⟩⟩)

def run (Δ : Definition) (S : State) (op : Op) : State :=
  (step accepts commit Δ S op).getD S

def outbound (Δ : Definition) (S : State) (a : ActivationId) (v : NodeId) : State :=
  run Δ S (.activate a ⟨.orig v ["run"], payload, [⟨.outbound "t", .carry, payload⟩]⟩)

def delivered (Δ : Definition) (S : State) (a : ActivationId) (e : EdgeId) : State :=
  match Δ.edge? e with
  | some edge =>
    run Δ S (.activate a ⟨.orig edge.source ["run"], payload, [⟨.delivered e, .carry, payload⟩]⟩)
  | none => S

/-- The outcome of a rewrite: its nodes, its edges, the statuses of `ps`, and the revision. -/
def outcome (grammar : List Production) (Δ : Definition) (S : State) (req : RewriteRequest)
    (ev : List (Digest × Bytes)) (ps : List PackageId) :
    Option (List NodeId × List Edge × List (Option Status) × Nat) :=
  (rewrite accepts commit grammar Δ S req ev).map fun (Δ', S') =>
    (Δ'.nodes, Δ'.edges, ps.map fun p => (S'.packages p).map (·.status), S'.revision)

def retired (reason : Reason) (revision : Nat) : Option Status :=
  some (.retired ⟨reason, revision, none⟩)

/-! ## A receipt at an `All` join retires when its route is removed; at `Any` it waits -/

def allAt (b : NodeId) : NodeId → Ingress := fun v => if v == b then .all else .any

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")] (allAt "B")
  let (pr, req) := rule "disconnect" Δ (kernel ["A", "B"] [] (allAt "B")) ["A", "B"] []
  outcome [pr] Δ (delivered Δ (State.initial Δ) 1 "ab") req [] [⟨1, 0⟩] =
    some (["A", "B"], [], [retired .routeRemoved 2], 2)

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  let (pr, req) := rule "disconnect" Δ (kernel ["A", "B"] []) ["A", "B"] []
  outcome [pr] Δ (delivered Δ (State.initial Δ) 1 "ab") req [] [⟨1, 0⟩] =
    some (["A", "B"], [], [some .live], 2)

/-! ## Deleting a node retires both phases, and its identity cannot be reused -/

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  let A := kernel ["A"] []
  let grammar := [(rule "remove-b" Δ A ["A"] []).1, (rule "recreate-b" A Δ ["A"] []).1]
  let S := outbound Δ (delivered Δ (State.initial Δ) 1 "ab") 2 "B"
  outcome grammar Δ S (rule "remove-b" Δ A ["A"] []).2 [] [⟨1, 0⟩, ⟨2, 0⟩] =
    some (["A"], [], [retired .holderRemoved 3, retired .holderRemoved 3], 3)

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  let A := kernel ["A"] []
  let grammar := [(rule "remove-b" Δ A ["A"] []).1, (rule "recreate-b" A Δ ["A"] []).1]
  let S := outbound Δ (delivered Δ (State.initial Δ) 1 "ab") 2 "B"
  ((rewrite accepts commit grammar Δ S (rule "remove-b" Δ A ["A"] []).2 []).bind fun (Δ', S') =>
    rewrite accepts commit grammar Δ' S' (rule "recreate-b" A Δ ["A"] []).2 evidence).isNone

/-! ## A deleted node may not keep an unmatched incident edge -/

#guard
  let Δ := kernel ["A", "B", "U"] [("ab", "A", "B", "payload"), ("ub", "U", "B", "payload")]
  let (pr, req) :=
    rule "dangling" (kernel ["A", "B"] [("ab", "A", "B", "payload")]) (kernel ["A"] []) ["A"] []
  (outcome [pr] Δ (State.initial Δ) req evidence []).isNone

/-! ## A preserved node keeps its local policy -/

#guard
  let Δ := kernel ["A"] []
  let pr : Production := ⟨"policy", fragment Δ, ["A"], [], { fragment Δ with roots := [] }⟩
  let req : RewriteRequest := ⟨"policy", ⟨[("A", "A")], [], [], []⟩⟩
  (outcome [pr] Δ (State.initial Δ) req evidence []).isNone

#guard
  let Δ := kernel ["A"] []
  let pr : Production := ⟨"policy", fragment Δ, ["A"], [], fragment Δ⟩
  let req : RewriteRequest := ⟨"policy", ⟨[("A", "A")], [], [], []⟩⟩
  outcome [pr] Δ (State.initial Δ) req evidence [] = some (["A"], [], [], 1)

/-! ## Rule symbols bind exactly, injectively, and to fresh identities -/

def symbols : Production :=
  ⟨"symbols", fragment (kernel ["X", "Y"] [("xy", "X", "Y", "payload")]), ["X", "Y"], [],
    fragment (kernel ["X", "Y", "Z"] [("xz", "X", "Z", "payload"), ("zy", "Z", "Y", "payload")])⟩

def symbolMatch (nodes fresh : List (String × String)) : RewriteRequest :=
  ⟨"symbols", ⟨nodes, [("xy", "ab")], fresh, [("xz", "ac"), ("zy", "cb")]⟩⟩

def line : Definition := kernel ["A", "B"] [("ab", "A", "B", "payload")]

#guard outcome [symbols] line (State.initial line)
    (symbolMatch [("X", "A"), ("Y", "B")] [("Z", "C")]) [] [] =
  some (["A", "B", "C"], [⟨"ac", "A", "C"⟩, ⟨"cb", "C", "B"⟩], [], 1)

#guard (outcome [symbols] line (State.initial line)
    (symbolMatch [("X", "A")] [("Z", "C")]) [] []).isNone

#guard (outcome [symbols] line (State.initial line)
    (symbolMatch [("X", "A"), ("Y", "A")] [("Z", "C")]) [] []).isNone

#guard (outcome [symbols] line (State.initial line)
    (symbolMatch [("X", "A"), ("Y", "B")] [("Z", "B")]) [] []).isNone

/-! ## Commutation needs disjoint affected holders

Two waiting packages, at `A` and at `C`. One rewrite adds an accepting edge from `A`, the
other a rejecting edge from a chosen source. From `C`, the holders are disjoint and both
orders agree up to stamps. From `A`, both rewrites affect `A`, and the order decides whether
`A`'s package is retired. -/

def square : Definition := kernel ["A", "B", "C", "D"] []

def waiting : State := outbound square (outbound square (State.initial square) 1 "A") 2 "C"

def twoRewrites (source : NodeId) (acceptFirst : Bool) :
    Option (List Edge × List (Option Status)) :=
  let accept := rule "accept" square (kernel ["A", "B", "C", "D"] [("ab", "A", "B", "payload")])
    ["A", "B", "C", "D"] []
  let reject := rule "reject" square (kernel ["A", "B", "C", "D"] [("reject", source, "D", "deny")])
    ["A", "B", "C", "D"] []
  let (first, second) := if acceptFirst then (accept.2, reject.2) else (reject.2, accept.2)
  (rewrite accepts commit [accept.1, reject.1] square waiting first evidence).bind fun (Δ, S) =>
    (rewrite accepts commit [accept.1, reject.1] Δ S second evidence).map fun (Δ', S') =>
      (Δ'.edges, [⟨1, 0⟩, ⟨2, 0⟩].map fun (p : PackageId) => (S'.packages p).map (·.status))

#guard twoRewrites "C" true =
  some ([⟨"ab", "A", "B"⟩, ⟨"reject", "C", "D"⟩], [some .live, retired .noAcceptingEdge 4])

#guard twoRewrites "C" false =
  some ([⟨"reject", "C", "D"⟩, ⟨"ab", "A", "B"⟩], [some .live, retired .noAcceptingEdge 3])

#guard twoRewrites "A" true =
  some ([⟨"ab", "A", "B"⟩, ⟨"reject", "A", "D"⟩], [some .live, some .live])

#guard twoRewrites "A" false =
  some ([⟨"reject", "A", "D"⟩, ⟨"ab", "A", "B"⟩], [retired .noAcceptingEdge 3, some .live])

end Ontography.Examples
