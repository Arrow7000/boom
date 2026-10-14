import TriageRuleProperties
import TriageInspection

/-!
An executable, wire-ID-free model of the netties reducer. It allocates fresh
agent IDs, replaces an active pair by its exported RHS template, and follows
alternating old/new interface wires to splice the surrounding graph. The
model is deliberately small enough to execute in Lean; preservation and
simulation theorems are still to be established.
-/

namespace TriageConcrete
open TriageRuleModel TriageRules TriageRuleProperties TriageMachine

inductive End where
  | agent : Nat → Nat → End
  | free : Nat → End
  deriving Repr, DecidableEq

abbrev Wire := End × End

structure Net where
  agents : List (Nat × Kind) := []
  wires : List Wire := []
  nextId : Nat := 1
  deriving Repr, DecidableEq

def Net.kind? (net : Net) (id : Nat) : Option Kind :=
  (net.agents.find? fun entry => entry.1 == id).map Prod.snd

def neighborIn : List Wire → End → Option End
  | [], _ => none
  | (a, b) :: rest, end_ =>
      if end_ = a then some b
      else if end_ = b then some a
      else neighborIn rest end_

def Net.neighbor (net : Net) (end_ : End) : Option End :=
  neighborIn net.wires end_

def Net.expected (net : Net) : List End :=
  (net.agents.flatMap fun (id, kind) =>
    (List.range (kind.arity + 1)).map (End.agent id)) ++ [.free 0]

def Net.used (net : Net) : List End :=
  net.wires.flatMap fun (a, b) => [a, b]

/-- Every live port, including the one external result port, appears in
exactly one wire, and all allocated agent IDs are distinct. -/
def Net.wellFormed (net : Net) : Bool :=
  decide (net.agents.map Prod.fst).Nodup &&
  decide net.used.Nodup &&
  net.used.all (fun end_ => net.expected.any (fun expected => decide (end_ = expected))) &&
  net.expected.all (fun end_ => net.used.any (fun used => decide (end_ = used)))

def Net.fresh (net : Net) (kind : Kind) : Nat × Net :=
  (net.nextId, { net with
    agents := net.agents ++ [(net.nextId, kind)], nextId := net.nextId + 1 })

def Net.connect (net : Net) (a b : End) : Net :=
  { net with wires := net.wires ++ [(a, b)] }

def build : Syntax → StateM Net End
  | .leaf => do
      let (id, net) := (← get).fresh .leaf
      set net
      return .agent id 0
  | .app fn arg => do
      let (id, net) := (← get).fresh .app
      set net
      let fnRoot ← build fn
      let argRoot ← build arg
      modify fun net => (net.connect (.agent id 1) fnRoot).connect (.agent id 2) argRoot
      return .agent id 0

def initial (source : Syntax) : Net := Id.run do
  let (root, net) := (build source) {}
  let (evalId, net) := net.fresh .eval
  return (net.connect root (.agent evalId 0)).connect (.agent evalId 1) (.free 0)

inductive Node where
  | real : End → Node
  | iface : Nat → Nat → Node
  deriving Repr, DecidableEq

abbrev Layer := List (Node × Node)

def Node.fromOld (left right : Nat) : End → Node
  | .agent id slot =>
      if id = left then .iface 0 slot
      else if id = right then .iface 1 slot
      else .real (.agent id slot)
  | .free name => .real (.free name)

def Node.fromRule (fresh : Nat) : TriageRuleModel.End → Node
  | .agent index slot => .real (.agent (fresh + index) slot)
  | .iface side slot => .iface side slot

def layerNeighbor : Layer → Node → Option Node
  | [], _ => none
  | (a, b) :: rest, node =>
      if node = a then some b
      else if node = b then some a
      else layerNeighbor rest node

/-- Follow the old and replacement matchings alternately through interface
nodes. A closed interface loop has no real endpoint and is discarded. -/
def follow (outer inner : Layer) : Nat → Node → Bool → Option End
  | 0, _, _ => none
  | fuel + 1, node, useInner => do
      let next ← layerNeighbor (if useInner then inner else outer) node
      match next with
      | .real end_ => some end_
      | .iface _ _ => follow outer inner fuel next (!useInner)

def starts (layer : Layer) : List (End × Node) :=
  layer.flatMap fun (a, b) =>
    match a, b with
    | .real end_, .iface side slot => [(end_, .iface side slot)]
    | .iface side slot, .real end_ => [(end_, .iface side slot)]
    | _, _ => []

def sameWire (a b : Wire) : Bool :=
  decide ((a.1 = b.1 ∧ a.2 = b.2) ∨
    (a.1 = b.2 ∧ a.2 = b.1))

def uniqueWires (wires : List Wire) : List Wire :=
  wires.foldl (fun acc wire =>
    if acc.any (sameWire wire) then acc else acc ++ [wire]) []

def direct (layer : Layer) : List Wire :=
  layer.filterMap fun (a, b) =>
    match a, b with
    | .real x, .real y => some (x, y)
    | _, _ => none

def spliceStarts (outer inner : Layer) (fuel : Nat) : List Wire :=
  let fromOuter := (starts outer).filterMap fun (start, iface) =>
    (follow outer inner fuel iface true).map fun target => (start, target)
  let fromInner := (starts inner).filterMap fun (start, iface) =>
    (follow outer inner fuel iface false).map fun target => (start, target)
  uniqueWires (fromOuter ++ fromInner)

def Net.replace (net : Net) (rule : Rule) (left right : Nat) : Net := Id.run do
  let belongs (end_ : End) := match end_ with
    | .agent id _ => id = left || id = right
    | .free _ => false
  let touched := net.wires.filter fun (a, b) => belongs a || belongs b
  let untouched := net.wires.filter fun (a, b) => !(belongs a || belongs b)
  let active : Wire := (.agent left 0, .agent right 0)
  let outer : Layer := (touched.filter fun edge => !sameWire edge active).map
    fun (a, b) => (Node.fromOld left right a, Node.fromOld left right b)
  let inner : Layer := rule.wires.map fun (a, b) =>
    (Node.fromRule net.nextId a, Node.fromRule net.nextId b)
  let through := spliceStarts outer inner (2 * (rule.left.arity + rule.right.arity) + 2)
  let added := rule.agents.zipIdx.map fun (kind, index) => (net.nextId + index, kind)
  return { agents := net.agents.filter (fun entry =>
             entry.1 != left && entry.1 != right) ++ added,
           wires := untouched ++ direct inner ++ through,
           nextId := net.nextId + rule.agents.length }

def Net.firstRedex (net : Net) : Option (Rule × Nat × Nat) :=
  (net.wires.filterMap fun (a, b) =>
    match a, b with
    | .agent first 0, .agent second 0 => do
        let firstKind ← net.kind? first
        let secondKind ← net.kind? second
        let rule ← rules.find? fun rule => accepts rule firstKind secondKind
        if rule.left == firstKind then some (rule, first, second)
        else some (rule, second, first)
    | _, _ => none).head?

def Net.noActivePairs (net : Net) : Bool :=
  net.wires.all fun (a, b) =>
    match a, b with
    | .agent _ 0, .agent _ 0 => false
    | _, _ => true

def Net.step? (net : Net) : Option Net := do
  let (rule, left, right) ← net.firstRedex
  some (net.replace rule left right)

def Net.run : Nat → Net → Net
  | 0, net => net
  | fuel + 1, net =>
      match net.step? with
      | none => net
      | some next => Net.run fuel next

def Net.trace : Nat → Net → List Net
  | 0, net => [net]
  | fuel + 1, net =>
      net :: match net.step? with
        | none => []
        | some next => Net.trace fuel next

def Net.outKind (net : Net) : Option Kind := do
  let end_ ← net.neighbor (.free 0)
  match end_ with
  | .agent id 0 => net.kind? id
  | _ => none

def Net.readRoot (net : Net) : Nat → End → Option Syntax
  | 0, _ => none
  | fuel + 1, .agent id 0 => do
      let kind ← net.kind? id
      match kind with
      | .leaf => some .leaf
      | .stem => do
          let child ← net.neighbor (.agent id 1)
          let childSyntax ← net.readRoot fuel child
          some (TriageMachine.stem childSyntax)
      | .fork => do
          let left ← net.neighbor (.agent id 1)
          let right ← net.neighbor (.agent id 2)
          let leftSyntax ← net.readRoot fuel left
          let rightSyntax ← net.readRoot fuel right
          some (TriageMachine.fork leftSyntax rightSyntax)
      | .app => do
          let fn ← net.neighbor (.agent id 1)
          let arg ← net.neighbor (.agent id 2)
          let fnSyntax ← net.readRoot fuel fn
          let argSyntax ← net.readRoot fuel arg
          some (.app fnSyntax argSyntax)
      | _ => none
  | _, _ => none

def Net.outputSyntax (net : Net) (fuel : Nat) : Option Syntax := do
  let root ← net.neighbor (.free 0)
  net.readRoot fuel root

def headSyntax : Head → Syntax
  | .leaf => .leaf
  | .stem child => TriageMachine.stem child
  | .fork left right => TriageMachine.fork left right

def agreesOn (source : Syntax) (fuel : Nat) : Bool :=
  match TriageMachine.run fuel (.eval source []) with
  | .done head =>
      let concrete := (initial source).run fuel
      concrete.outputSyntax fuel == some (headSyntax head) &&
      ((initial source).trace fuel).all Net.wellFormed &&
      concrete.noActivePairs
  | _ => true

def abstractDone (source : Syntax) (fuel : Nat) : Bool :=
  match TriageMachine.run fuel (.eval source []) with
  | .done _ => true
  | _ => false

def terms : Nat → Nat → List Syntax
  | 0, _ => []
  | fuel + 1, leaves =>
      if leaves == 1 then [.leaf]
      else (List.range (leaves - 1)).flatMap fun i =>
        let left := i + 1
        let right := leaves - left
        (terms fuel left).flatMap fun fn =>
          (terms fuel right).map fun arg => .app fn arg

def smallTerms : List Syntax :=
  (List.range 6).flatMap fun i => terms 6 (i + 1)

theorem smallTerms_count : smallTerms.length = 65 := by decide

theorem smallTerms_abstract_done :
    smallTerms.all (fun source => abstractDone source 100) = true := by
  native_decide

/-- Bounded exhaustive check of the executable concrete splice against the
abstract machine, including graph wellformedness at every visited state. -/
theorem smallTerms_agree : smallTerms.all (fun source => agreesOn source 100) = true := by
  native_decide

theorem demo_trace_wellFormed :
    ((initial demo).trace 100).all Net.wellFormed = true := by
  native_decide

theorem demo_output :
    ((initial demo).run 100).outputSyntax 100 =
      some (TriageMachine.stem .leaf) := by
  native_decide

end TriageConcrete
