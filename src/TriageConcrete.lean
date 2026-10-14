import TriageRuleProperties
import TriageInspection
import TriageGraph
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Enum

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

def wireEnds (wires : List Wire) : List End :=
  wires.flatMap fun (a, b) => [a, b]

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

theorem left_mem_wireEnds {wires : List Wire} {a b : End}
    (h : (a, b) ∈ wires) : a ∈ wireEnds wires := by
  simp only [wireEnds, List.mem_flatMap]
  exact ⟨(a, b), h, by simp⟩

theorem right_mem_wireEnds {wires : List Wire} {a b : End}
    (h : (a, b) ∈ wires) : b ∈ wireEnds wires := by
  simp only [wireEnds, List.mem_flatMap]
  exact ⟨(a, b), h, by simp⟩

/-- In a matching edge list, the lookup returns the other endpoint of every
listed edge. -/
theorem neighborIn_of_mem {wires : List Wire} {a b : End}
    (hn : (wireEnds wires).Nodup) (h : (a, b) ∈ wires) :
    neighborIn wires a = some b := by
  induction wires with
  | nil => cases h
  | cons wire rest ih =>
      rcases wire with ⟨x, y⟩
      change (x :: y :: wireEnds rest).Nodup at hn
      have hx := List.nodup_cons.mp hn
      have hy := List.nodup_cons.mp hx.2
      rcases List.mem_cons.mp h with hfirst | hrest
      · have hxy : a = x ∧ b = y := Prod.mk.inj hfirst
        rcases hxy with ⟨rfl, rfl⟩
        simp [neighborIn]
      · have ha := left_mem_wireEnds hrest
        have hax : a ≠ x := by
          intro heq
          exact hx.1 (List.mem_cons_of_mem _ (heq ▸ ha))
        have hay : a ≠ y := by
          intro heq
          exact hy.1 (heq ▸ ha)
        simpa [neighborIn, hax, hay] using ih hy.2 hrest

theorem neighborIn_of_mem_right {wires : List Wire} {a b : End}
    (hn : (wireEnds wires).Nodup) (h : (a, b) ∈ wires) :
    neighborIn wires b = some a := by
  induction wires with
  | nil => cases h
  | cons wire rest ih =>
      rcases wire with ⟨x, y⟩
      change (x :: y :: wireEnds rest).Nodup at hn
      have hx := List.nodup_cons.mp hn
      have hy := List.nodup_cons.mp hx.2
      rcases List.mem_cons.mp h with hfirst | hrest
      · have hxy : a = x ∧ b = y := Prod.mk.inj hfirst
        have hne : y ≠ x := by
          intro heq
          exact hx.1 (List.mem_cons.mpr (Or.inl heq.symm))
        rcases hxy with ⟨rfl, rfl⟩
        simp [neighborIn, hne]
      · have hb := right_mem_wireEnds hrest
        have hbx : b ≠ x := by
          intro heq
          exact hx.1 (List.mem_cons_of_mem _ (heq ▸ hb))
        have hby : b ≠ y := by
          intro heq
          exact hy.1 (heq ▸ hb)
        simpa [neighborIn, hbx, hby] using ih hy.2 hrest

theorem neighborIn_sound {wires : List Wire} {a b : End}
    (h : neighborIn wires a = some b) :
    (a, b) ∈ wires ∨ (b, a) ∈ wires := by
  induction wires with
  | nil => simp [neighborIn] at h
  | cons wire rest ih =>
      rcases wire with ⟨x, y⟩
      simp only [neighborIn] at h
      by_cases hax : a = x
      · simp [hax] at h
        subst b
        left
        exact List.mem_cons.mpr (Or.inl (by simp [hax]))
      · simp only [if_neg hax] at h
        by_cases hay : a = y
        · simp [hay] at h
          subst b
          right
          exact List.mem_cons.mpr (Or.inl (by simp [hay]))
        · simp only [if_neg hay] at h
          rcases ih h with hleft | hright
          · exact Or.inl (List.mem_cons_of_mem _ hleft)
          · exact Or.inr (List.mem_cons_of_mem _ hright)

theorem neighborIn_symmetric {wires : List Wire} {a b : End}
    (hn : (wireEnds wires).Nodup)
    (h : neighborIn wires a = some b) :
    neighborIn wires b = some a := by
  rcases neighborIn_sound h with hab | hba
  · exact neighborIn_of_mem_right hn hab
  · exact neighborIn_of_mem hn hba

theorem wire_endpoints_ne {wires : List Wire} {a b : End}
    (hn : (wireEnds wires).Nodup) (h : (a, b) ∈ wires) : a ≠ b := by
  have hpair : ([a, b] : List End).Nodup :=
    (List.nodup_flatMap.mp hn).1 (a, b) h
  simpa using hpair

theorem neighborIn_irreflexive {wires : List Wire} {a : End}
    (hn : (wireEnds wires).Nodup) : neighborIn wires a ≠ some a := by
  intro h
  rcases neighborIn_sound h with hwire | hwire
  · exact (wire_endpoints_ne hn hwire) rfl
  · exact (wire_endpoints_ne hn hwire) rfl

theorem neighborIn_total {wires : List Wire} {end_ : End}
    (hn : (wireEnds wires).Nodup) (h : end_ ∈ wireEnds wires) :
    ∃ other, neighborIn wires end_ = some other := by
  rcases List.mem_flatMap.mp h with ⟨wire, hwire, hend⟩
  rcases wire with ⟨a, b⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  rcases hend with heq | heq
  · subst end_
    exact ⟨b, neighborIn_of_mem hn hwire⟩
  · subst end_
    exact ⟨a, neighborIn_of_mem_right hn hwire⟩

def Net.neighbor (net : Net) (end_ : End) : Option End :=
  neighborIn net.wires end_

def Net.expected (net : Net) : List End :=
  (net.agents.flatMap fun (id, kind) =>
    (List.range (kind.arity + 1)).map (End.agent id)) ++ [.free 0]

def Net.used (net : Net) : List End :=
  wireEnds net.wires

/-- Every live port, including the one external result port, appears in
exactly one wire, and all allocated agent IDs are distinct. -/
def Net.wellFormed (net : Net) : Bool :=
  decide (net.agents.map Prod.fst).Nodup &&
  decide net.used.Nodup &&
  net.used.all (fun end_ => net.expected.any (fun expected => decide (end_ = expected))) &&
  net.expected.all (fun end_ => net.used.any (fun used => decide (end_ = used)))

def Net.freshIds (net : Net) : Bool :=
  net.agents.all fun (id, _) => id < net.nextId

def Net.valid (net : Net) : Bool := net.wellFormed && net.freshIds

theorem Net.wellFormed_iff (net : Net) : net.wellFormed = true ↔
    (net.agents.map Prod.fst).Nodup ∧
    net.used.Nodup ∧
    (∀ end_ ∈ net.used, end_ ∈ net.expected) ∧
    (∀ end_ ∈ net.expected, end_ ∈ net.used) := by
  simp [Net.wellFormed, List.all_eq_true, List.any_eq_true, and_assoc]

theorem Net.wellFormed_nodup {net : Net} (h : net.wellFormed = true) :
    (wireEnds net.wires).Nodup := by
  exact (net.wellFormed_iff.mp h).2.1

theorem Net.expected_has_neighbor {net : Net} (h : net.wellFormed = true)
    {end_ : End} (hlegal : end_ ∈ net.expected) :
    ∃ other, net.neighbor end_ = some other := by
  have hused := (net.wellFormed_iff.mp h).2.2.2 end_ hlegal
  exact neighborIn_total (net.wellFormed_nodup h) hused

def endToGraph : End → TriageGraph.End
  | .agent id slot => .agent id slot
  | .free id => .free id

def endFromGraph : TriageGraph.End → End
  | .agent id slot => .agent id slot
  | .free id => .free id

theorem endFromTo (end_ : End) : endFromGraph (endToGraph end_) = end_ := by
  cases end_ <;> rfl

theorem endToFrom (end_ : TriageGraph.End) :
    endToGraph (endFromGraph end_) = end_ := by
  cases end_ <;> rfl

/-- A checked concrete edge list supplies the symmetric, irreflexive partner
function used by the abstract port-graph lemmas. -/
def Net.toGraph (net : Net) (h : net.wellFormed = true) : TriageGraph.Net where
  kind := net.kind?
  isFree := fun id => decide (id = 0)
  partner := fun end_ => (net.neighbor (endFromGraph end_)).map endToGraph
  symmetric := by
    intro a b hab
    have hconcrete : net.neighbor (endFromGraph a) =
        some (endFromGraph b) := by
      simpa [endFromTo] using congrArg (Option.map endFromGraph) hab
    have hs := neighborIn_symmetric (net.wellFormed_nodup h) hconcrete
    simpa [Net.neighbor, endToFrom] using congrArg (Option.map endToGraph) hs
  irreflexive := by
    intro a haa
    have hconcrete : net.neighbor (endFromGraph a) =
        some (endFromGraph a) := by
      simpa [endFromTo] using congrArg (Option.map endFromGraph) haa
    exact neighborIn_irreflexive (net.wellFormed_nodup h) hconcrete

def Net.Active (net : Net) (left right : Nat) : Prop :=
  (∃ kind, net.kind? left = some kind) ∧
  (∃ kind, net.kind? right = some kind) ∧
  net.neighbor (.agent left 0) = some (.agent right 0)

@[simp] theorem map_end_agent_iff (option : Option End) (id slot : Nat) :
    option.map endToGraph = some (TriageGraph.End.agent id slot) ↔
      option = some (End.agent id slot) := by
  cases option with
  | none => simp
  | some end_ => cases end_ <;> simp [endToGraph]

theorem Net.active_iff_graph {net : Net} (h : net.wellFormed = true)
    {left right : Nat} :
    net.Active left right ↔ (net.toGraph h).Active left right := by
  simp only [Net.Active, TriageGraph.Net.Active, Net.toGraph,
    endFromGraph, map_end_agent_iff]

/-- The generic active-pair disjointness theorem now applies to the concrete
edge-list representation whenever its invariant holds. -/
theorem Net.active_disjoint_or_equal {net : Net} (h : net.wellFormed = true)
    {a b c d : Nat} (hab : net.Active a b) (hcd : net.Active c d)
    (hshare : a = c ∨ a = d ∨ b = c ∨ b = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  exact TriageGraph.Net.Active.disjoint_or_equal
    ((net.active_iff_graph h).mp hab)
    ((net.active_iff_graph h).mp hcd) hshare

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

theorem Net.replace_agents (net : Net) (rule : Rule) (left right : Nat) :
    (net.replace rule left right).agents =
      net.agents.filter (fun entry => entry.1 != left && entry.1 != right) ++
      (rule.agents.zipIdx.map fun (kind, index) => (net.nextId + index, kind)) := by
  rfl

theorem Net.replace_nextId (net : Net) (rule : Rule) (left right : Nat) :
    (net.replace rule left right).nextId = net.nextId + rule.agents.length := by
  rfl

/-- Fresh IDs remain above every surviving or newly allocated agent ID. This
is the allocation part of the universal rewrite-preservation obligation. -/
theorem Net.replace_freshIds {net : Net} (h : net.freshIds = true)
    (rule : Rule) (left right : Nat) :
    (net.replace rule left right).freshIds = true := by
  have hOld : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
    simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using h
  have hNew : ∀ entry ∈ rule.agents.zipIdx,
      net.nextId + entry.2 < net.nextId + rule.agents.length := by
    rw [List.forall_mem_zipIdx']
    intro i hi
    omega
  simp only [Net.freshIds, List.all_eq_true, Net.replace_agents,
    Net.replace_nextId, List.mem_append, decide_eq_true_eq]
  intro entry hentry
  rcases hentry with hold | hnew
  · have hmem := (List.mem_filter.mp hold).1
    exact Nat.lt_of_lt_of_le (hOld entry hmem) (Nat.le_add_right ..)
  · rcases List.mem_map.mp hnew with ⟨⟨kind, index⟩, hmem, heq⟩
    subst entry
    exact hNew (kind, index) hmem

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
      ((initial source).trace fuel).all Net.valid &&
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
    ((initial demo).trace 100).all Net.valid = true := by
  native_decide

theorem demo_output :
    ((initial demo).run 100).outputSyntax 100 =
      some (TriageMachine.stem .leaf) := by
  native_decide

end TriageConcrete
