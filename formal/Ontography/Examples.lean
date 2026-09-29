import Ontography.System

/-!
# Examples

Kernel rewrite regression scenarios, replayed in the model. Each `#guard` evaluates the model
when this file builds, so a change to the law that alters one of these outcomes fails the
build. The fixtures mirror the kernel tests' shared support: every node has type `n`, result
contract `result`, and a root rule with authority `{run}`; edges carry contract `payload`,
`deny`, or `other`.
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

def nothing : Fragment := ⟨[], [], [], [], [], []⟩

/-- The edit taking `Δ` to `Δ'`: remove the nodes and edges `Δ'` lacks, and add the ones `Δ`
lacks with their annotations and policies in `Δ'`. -/
def diff (Δ Δ' : Definition) : Edit :=
  let nodes := Δ'.nodes.filter (· ∉ Δ.nodes)
  let edges := Δ'.edges.filter (·.id ∉ Δ.edges.map (·.id))
  { removeNodes := Δ.nodes.filter (· ∉ Δ'.nodes)
    removeEdges := (Δ.edges.map (·.id)).filter (· ∉ Δ'.edges.map (·.id))
    add := ⟨nodes, edges, Δ'.nodeDefs.filter (·.node ∈ nodes),
      Δ'.edgeDefs.filter (·.edge ∈ edges.map (·.id)), Δ'.transitions.filter (·.node ∈ nodes),
      Δ'.roots.filter (·.node ∈ nodes)⟩ }

/-- Every edit is permitted. -/
def permitAll : Policy := fun _ _ _ _ _ => true

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
def outcome (permits : Policy) (Δ : Definition) (S : State) (req : RewriteRequest)
    (ev : List (Digest × Bytes)) (ps : List PackageId) :
    Option (List NodeId × List Edge × List (Option Status) × Nat) :=
  (rewrite accepts commit permits Δ S req ev).map fun (Δ', S') =>
    (Δ'.nodes, Δ'.edges, ps.map fun p => (S'.packages p).map (·.status), S'.revision)

/-- A request by the manager. -/
def manager (e : Edit) : RewriteRequest := ⟨"manager", e⟩

def retired (reason : Reason) (revision : Nat) : Option Status :=
  some (.retired ⟨reason, revision, none⟩)

/-! ## A receipt at an `All` join retires when its route is removed; at `Any` it waits -/

def allAt (b : NodeId) : NodeId → Ingress := fun v => if v == b then .all else .any

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")] (allAt "B")
  outcome permitAll Δ (delivered Δ (State.initial Δ) 1 "ab")
      (manager (diff Δ (kernel ["A", "B"] [] (allAt "B")))) [] [⟨1, 0⟩] =
    some (["A", "B"], [], [retired .routeRemoved 2], 2)

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  outcome permitAll Δ (delivered Δ (State.initial Δ) 1 "ab")
      (manager (diff Δ (kernel ["A", "B"] []))) [] [⟨1, 0⟩] =
    some (["A", "B"], [], [some .live], 2)

/-! ## Deleting a node retires both phases, and its identity cannot be reused -/

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  let S := outbound Δ (delivered Δ (State.initial Δ) 1 "ab") 2 "B"
  outcome permitAll Δ S (manager (diff Δ (kernel ["A"] []))) [] [⟨1, 0⟩, ⟨2, 0⟩] =
    some (["A"], [], [retired .holderRemoved 3, retired .holderRemoved 3], 3)

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  let A := kernel ["A"] []
  let S := outbound Δ (delivered Δ (State.initial Δ) 1 "ab") 2 "B"
  ((rewrite accepts commit permitAll Δ S (manager (diff Δ A)) []).bind fun (Δ', S') =>
    rewrite accepts commit permitAll Δ' S' (manager (diff A Δ)) evidence).isNone

/-! ## A removed node takes every edge at it with it -/

def fork : Definition :=
  kernel ["A", "B", "U"] [("ab", "A", "B", "payload"), ("ub", "U", "B", "payload")]

#guard (outcome permitAll fork (State.initial fork) (manager ⟨["B"], ["ab"], nothing⟩) [] []).isNone

#guard outcome permitAll fork (State.initial fork) (manager ⟨["B"], ["ab", "ub"], nothing⟩) [] [] =
  some (["A", "U"], [], [], 1)

/-! ## A surviving node keeps its definition and policies -/

#guard
  let Δ := kernel ["A"] []
  (outcome permitAll Δ (State.initial Δ)
    (manager ⟨[], [], { nothing with transitions := [⟨"A", ["run"], ["other"]⟩] }⟩) [] []).isNone

#guard
  let Δ := { kernel ["A"] [] with roots := [] }
  (outcome permitAll Δ (State.initial Δ)
    (manager ⟨[], [], { nothing with roots := [⟨"A", ["run"]⟩] }⟩) [] []).isNone

#guard
  let Δ := kernel ["A"] []
  outcome permitAll Δ (State.initial Δ) (manager ⟨[], [], nothing⟩) [] [] =
    some (["A"], [], [], 1)

/-! ## An edit removes current identities and allocates only unused ones -/

def line : Definition := kernel ["A", "B"] [("ab", "A", "B", "payload")]

def inserted : Definition :=
  kernel ["A", "B", "C"] [("ac", "A", "C", "payload"), ("cb", "C", "B", "payload")]

#guard outcome permitAll line (State.initial line) (manager (diff line inserted)) [] [] =
  some (["A", "B", "C"], [⟨"ac", "A", "C"⟩, ⟨"cb", "C", "B"⟩], [], 1)

/-- Replace `ab` by a reversed edge named `id`. -/
def reverse (id : EdgeId) : Edit :=
  ⟨[], ["ab"], { nothing with
    edges := [⟨id, "B", "A"⟩]
    edgeDefs := [⟨id, ["flow"], ["n"], ["n"], "payload", ["run"], .anyOf⟩] }⟩

#guard outcome permitAll line (State.initial line) (manager (reverse "ba")) [] [] =
  some (["A", "B"], [⟨"ba", "B", "A"⟩], [], 1)

-- An edge identity leaves with its edge and is never reallocated, even by the same edit.
#guard (outcome permitAll line (State.initial line) (manager (reverse "ab")) [] []).isNone

#guard (outcome permitAll line (State.initial line)
    (manager ⟨["C"], [], nothing⟩) [] []).isNone

#guard (outcome permitAll line (State.initial line)
    (manager ⟨["A", "A"], [], nothing⟩) [] []).isNone

/-! ## The policy sees the principal, the edit, and the retirements its cleanup makes -/

def deny (who : Principal) : Policy := fun p _ _ _ _ => p != who

def retiresNothing : Policy := fun _ _ _ _ retired => retired.isEmpty

#guard
  let Δ := kernel ["A", "B"] []
  (rewrite accepts commit (deny "worker") Δ (State.initial Δ)
    ⟨"worker", diff Δ line⟩ []).isNone

#guard
  let Δ := kernel ["A", "B"] []
  outcome (deny "worker") Δ (State.initial Δ) (manager (diff Δ line)) [] [] =
    some (["A", "B"], [⟨"ab", "A", "B"⟩], [], 1)

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")] (allAt "B")
  (outcome retiresNothing Δ (delivered Δ (State.initial Δ) 1 "ab")
    (manager (diff Δ (kernel ["A", "B"] [] (allAt "B")))) [] [⟨1, 0⟩]).isNone

#guard
  let Δ := kernel ["A", "B"] [("ab", "A", "B", "payload")]
  outcome retiresNothing Δ (delivered Δ (State.initial Δ) 1 "ab")
      (manager (diff Δ (kernel ["A", "B"] []))) [] [⟨1, 0⟩] =
    some (["A", "B"], [], [some .live], 2)

/-! ## Commutation needs disjoint affected holders

Two waiting packages, at `A` and at `C`. One rewrite adds an accepting edge from `A`, the
other a rejecting edge from a chosen source. From `C`, the holders are disjoint and both
orders agree up to stamps. From `A`, both rewrites affect `A`, and the order decides whether
`A`'s package is retired. -/

def square : Definition := kernel ["A", "B", "C", "D"] []

def waiting : State := outbound square (outbound square (State.initial square) 1 "A") 2 "C"

def twoRewrites (source : NodeId) (acceptFirst : Bool) :
    Option (List Edge × List (Option Status)) :=
  let accept := diff square (kernel ["A", "B", "C", "D"] [("ab", "A", "B", "payload")])
  let reject := diff square (kernel ["A", "B", "C", "D"] [("reject", source, "D", "deny")])
  let (first, second) := if acceptFirst then (accept, reject) else (reject, accept)
  (rewrite accepts commit permitAll square waiting (manager first) evidence).bind fun (Δ, S) =>
    (rewrite accepts commit permitAll Δ S (manager second) evidence).map fun (Δ', S') =>
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
