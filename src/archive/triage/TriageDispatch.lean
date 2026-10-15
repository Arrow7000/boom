/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageLocalSemantics
import Mathlib.Tactic.IntervalCases

/-!
Concrete structural dispatch. These theorems describe the actual replacement
of a Triage agent by the exported rules in any valid surrounding graph. The
selected source and the inspected head's raw children are preserved exactly.
Unselected branches are attached to erasers; their eventual disappearance is
part of the separate administrative-resource simulation.
-/

namespace TriageDispatch
open TriageConcrete TriageRuleModel TriageRules TriageBoundary TriagePreservation
open TriageReduction TriageResidual TriageEncoding TriageLocalSemantics

def RawInput (net : Net) (owner slot : Nat) (source : TriageMachine.Syntax) : Prop :=
  ∃ root, Linked net (.agent owner slot) root ∧ Represents net root source

def EvalTask (net : Net) (source : TriageMachine.Syntax) (continuation : TriageConcrete.End) : Prop :=
  ∃ evalId root, net.kind? evalId = some .eval ∧ Represents net root source ∧
    net.neighbor (.agent evalId 0) = some root ∧
    net.neighbor (.agent evalId 1) = some continuation

theorem transfer_left_input {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right slot : Nat} {source : TriageMachine.Syntax}
    {newPort : TriageConcrete.End} (hc : (rule, left, right) ∈ net.redexChoices)
    (hin : RawInput net left (slot + 1) source)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 0 (slot + 1)) =
      some (.real newPort)) :
    ∃ root, (net.replace rule left right).neighbor newPort = some root ∧
      Represents (net.replace rule left right) root source := by
  rcases hin with ⟨root, hlink, hr⟩
  have hwf := valid_wellFormed hv
  have ha := (Net.redexChoice_sound hwf hc).2.1
  have hout := represented_child_outside hwf ha (by omega : slot + 1 ≠ 0) hlink hr
  exact ⟨root, Net.replace_left_aux hv hc (hlink.neighbor hwf) hout hnew,
    hr.replace hv hc hout⟩

theorem transfer_right_input {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right slot : Nat} {source : TriageMachine.Syntax}
    {newPort : TriageConcrete.End} (hc : (rule, left, right) ∈ net.redexChoices)
    (hin : RawInput net right (slot + 1) source)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 1 (slot + 1)) =
      some (.real newPort)) :
    ∃ root, (net.replace rule left right).neighbor newPort = some root ∧
      Represents (net.replace rule left right) root source := by
  rcases hin with ⟨root, hlink, hr⟩
  have hwf := valid_wellFormed hv
  have ha := (Net.redexChoice_sound hwf hc).2.1
  have hout := represented_child_outside hwf ha (by omega : slot + 1 ≠ 0) hlink hr
  exact ⟨root, Net.replace_right_aux hv hc (hlink.neighbor hwf) hout hnew,
    hr.replace hv hc hout⟩

def leafRule : Rule := rules[10]
def stemRule : Rule := rules[11]
def forkRule : Rule := rules[12]

theorem leafRule_mem : leafRule ∈ rules := by decide
theorem stemRule_mem : stemRule ∈ rules := by decide
theorem forkRule_mem : forkRule ∈ rules := by decide

theorem leaf_selects {net : Net} (hv : net.valid = true)
    {triageId leafId : Nat} {continuation : TriageConcrete.End} {w : TriageMachine.Syntax}
    (ha : net.Active triageId leafId)
    (ht : net.kind? triageId = some .triage) (hl : net.kind? leafId = some .leaf)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hout : belongs triageId leafId continuation = false)
    (hw : RawInput net triageId 2 w) :
    Step net (net.replace leafRule triageId leafId) ∧
      EvalTask (net.replace leafRule triageId leafId) w continuation := by
  have hc := Net.redexChoice_complete leafRule_mem ha ht hl
  have hx : layerNeighbor (ruleLayer leafRule net.nextId) (.iface 0 2) =
      some (.real (.agent net.nextId 0)) := by
    simp [leafRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  rcases transfer_left_input hv hc hw hx with ⟨root, hroot, hr⟩
  have he := Net.replace_created_kind hv hc (index := 0) (kind := .eval) (by rfl)
  have hcontinuation : (net.replace leafRule triageId leafId).neighbor (.agent net.nextId 1) =
      some continuation := by
    apply Net.replace_left_aux (slot := 0) hv hc hcont hout
    simp [leafRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  exact ⟨Step.chosen hc, net.nextId, root, by simpa using he, hr, hroot, hcontinuation⟩

theorem stem_selects {net : Net} (hv : net.valid = true)
    {triageId stemId : Nat} {continuation : TriageConcrete.End} {x u : TriageMachine.Syntax}
    (ha : net.Active triageId stemId)
    (ht : net.kind? triageId = some .triage) (hs : net.kind? stemId = some .stem)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hout : belongs triageId stemId continuation = false)
    (hx : RawInput net triageId 3 x) (hu : RawInput net stemId 1 u) :
    Step net (net.replace stemRule triageId stemId) ∧
      EvalTask (net.replace stemRule triageId stemId) (.app x u) continuation := by
  have hc := Net.redexChoice_complete stemRule_mem ha ht hs
  have hxWire : layerNeighbor (ruleLayer stemRule net.nextId) (.iface 0 3) =
      some (.real (.agent net.nextId 1)) := by
    simp [stemRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  have huWire : layerNeighbor (ruleLayer stemRule net.nextId) (.iface 1 1) =
      some (.real (.agent net.nextId 2)) := by
    simp [stemRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  rcases transfer_left_input hv hc hx hxWire with ⟨xroot, hxlink, hxr⟩
  rcases transfer_right_input hv hc hu huWire with ⟨uroot, hulink, hur⟩
  have happ := Net.replace_created_kind hv hc (index := 0) (kind := .app) (by rfl)
  have he := Net.replace_created_kind hv hc (index := 1) (kind := .eval) (by rfl)
  have hsource : Represents (net.replace stemRule triageId stemId) (.agent net.nextId 0) (.app x u) :=
    .app (Net.kind_mem (by simpa using happ)) (neighborIn_sound hxlink) (neighborIn_sound hulink) hxr hur
  have henter := Net.replace_internal_wire hv hc
    (first := 1) (firstSlot := 0) (second := 0) (secondSlot := 0) (by decide)
  have hcontinuation : (net.replace stemRule triageId stemId).neighbor (.agent (net.nextId + 1) 1) =
      some continuation := by
    apply Net.replace_left_aux (slot := 0) hv hc hcont hout
    simp [stemRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  exact ⟨Step.chosen hc, net.nextId + 1, .agent net.nextId 0, he, hsource,
    by simpa using henter, hcontinuation⟩

theorem fork_selects {net : Net} (hv : net.valid = true)
    {triageId forkId : Nat} {continuation : TriageConcrete.End} {y u v : TriageMachine.Syntax}
    (ha : net.Active triageId forkId)
    (ht : net.kind? triageId = some .triage) (hf : net.kind? forkId = some .fork)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hout : belongs triageId forkId continuation = false)
    (hy : RawInput net triageId 4 y) (hu : RawInput net forkId 1 u) (hvv : RawInput net forkId 2 v) :
    Step net (net.replace forkRule triageId forkId) ∧
      EvalTask (net.replace forkRule triageId forkId) (.app (.app y u) v) continuation := by
  have hc := Net.redexChoice_complete forkRule_mem ha ht hf
  have hyWire : layerNeighbor (ruleLayer forkRule net.nextId) (.iface 0 4) =
      some (.real (.agent net.nextId 1)) := by
    simp [forkRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  have huWire : layerNeighbor (ruleLayer forkRule net.nextId) (.iface 1 1) =
      some (.real (.agent net.nextId 2)) := by
    simp [forkRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hvWire : layerNeighbor (ruleLayer forkRule net.nextId) (.iface 1 2) =
      some (.real (.agent (net.nextId + 1) 2)) := by
    simp [forkRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  rcases transfer_left_input hv hc hy hyWire with ⟨yroot, hylink, hyr⟩
  rcases transfer_right_input hv hc hu huWire with ⟨uroot, hulink, hur⟩
  rcases transfer_right_input hv hc hvv hvWire with ⟨vroot, hvlink, hvr⟩
  have happ0 := Net.replace_created_kind hv hc (index := 0) (kind := .app) (by rfl)
  have happ1 := Net.replace_created_kind hv hc (index := 1) (kind := .app) (by rfl)
  have he := Net.replace_created_kind hv hc (index := 2) (kind := .eval) (by rfl)
  have hsource0 : Represents (net.replace forkRule triageId forkId) (.agent net.nextId 0) (.app y u) :=
    .app (Net.kind_mem (by simpa using happ0)) (neighborIn_sound hylink) (neighborIn_sound hulink) hyr hur
  have hbetween := Net.replace_internal_wire hv hc
    (first := 1) (firstSlot := 1) (second := 0) (secondSlot := 0) (by decide)
  have hsource : Represents (net.replace forkRule triageId forkId) (.agent (net.nextId + 1) 0)
      (.app (.app y u) v) :=
    .app (Net.kind_mem happ1) (neighborIn_sound (by simpa using hbetween)) (neighborIn_sound hvlink) hsource0 hvr
  have henter := Net.replace_internal_wire hv hc
    (first := 2) (firstSlot := 0) (second := 1) (secondSlot := 0) (by decide)
  have hcontinuation : (net.replace forkRule triageId forkId).neighbor (.agent (net.nextId + 2) 1) =
      some continuation := by
    apply Net.replace_left_aux (slot := 0) hv hc hcont hout
    simp [forkRule, rules, ruleLayer, Node.fromRule, layerNeighbor]
  exact ⟨Step.chosen hc, net.nextId + 2, .agent (net.nextId + 1) 0, he, hsource, henter, hcontinuation⟩

def Observed (net : Net) (id : Nat) : TriageMachine.Head → Prop
  | .leaf => net.kind? id = some .leaf
  | .stem u => net.kind? id = some .stem ∧ RawInput net id 1 u
  | .fork u v => net.kind? id = some .fork ∧ RawInput net id 1 u ∧ RawInput net id 2 v

def selected (head : TriageMachine.Head) (w x y : TriageMachine.Syntax) : TriageMachine.Syntax :=
  match head with
  | .leaf => w
  | .stem u => .app x u
  | .fork u v => .app (.app y u) v

def dispatchRule : TriageMachine.Head → Rule
  | .leaf => leafRule
  | .stem _ => stemRule
  | .fork _ _ => forkRule

theorem RawInput.not_continuation {net : Net} (hwf : net.wellFormed = true)
    {triageId owner slot : Nat} {continuation : TriageConcrete.End} {source : TriageMachine.Syntax}
    (hc : net.neighbor (.agent triageId 1) = some continuation)
    (hr : RawInput net owner slot source) : continuation ≠ .agent owner slot := by
  intro heq
  rcases hr with ⟨root, hlink, hsource⟩
  rcases hsource.principal with ⟨id, rfl⟩
  have hback : net.neighbor continuation = some (.agent triageId 1) :=
    neighborIn_symmetric (net.wellFormed_nodup hwf) hc
  rw [heq, hlink.neighbor hwf] at hback
  have hslots := (TriageConcrete.End.agent.inj (Option.some.inj hback)).2
  cases hslots

/-- A fully represented dispatch input forces the continuation to lie outside
the pair. This is derived from matching and arities, not assumed separately. -/
theorem continuation_outside {net : Net} (hwf : net.wellFormed = true)
    {triageId headId : Nat} {continuation : TriageConcrete.End}
    {head : TriageMachine.Head} {w x y : TriageMachine.Syntax}
    (ha : net.Active triageId headId) (ht : net.kind? triageId = some .triage)
    (hhead : Observed net headId head)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hw : RawInput net triageId 2 w) (hx : RawInput net triageId 3 x)
    (hy : RawInput net triageId 4 y) : belongs triageId headId continuation = false := by
  have hn := net.wellFormed_nodup hwf
  have hback : net.neighbor continuation = some (.agent triageId 1) :=
    neighborIn_symmetric hn hcont
  have hleft : continuation ≠ .agent triageId 0 := by
    intro heq
    rw [heq, ha.2.2] at hback
    cases (TriageConcrete.End.agent.inj (Option.some.inj hback)).2
  have hright : continuation ≠ .agent headId 0 := by
    intro heq
    have hp : net.neighbor (.agent headId 0) = some (.agent triageId 0) :=
      neighborIn_symmetric hn ha.2.2
    rw [heq, hp] at hback
    cases (TriageConcrete.End.agent.inj (Option.some.inj hback)).2
  have hself : continuation ≠ .agent triageId 1 := by
    intro heq
    rw [heq] at hcont
    exact neighborIn_irreflexive hn hcont
  have h2 := hw.not_continuation hwf hcont
  have h3 := hx.not_continuation hwf hcont
  have h4 := hy.not_continuation hwf hcont
  have hused : continuation ∈ net.used := by
    rcases neighborIn_sound hcont with hwire | hwire
    · exact right_mem_wireEnds hwire
    · exact left_mem_wireEnds hwire
  cases continuation with
  | free name => rfl
  | agent id slot =>
      by_cases hid : id = triageId
      · subst id
        have hb := Net.used_agent_slot_bound hwf ht hused
        simp only [Kind.arity] at hb
        interval_cases slot <;> simp_all
      · by_cases hihead : id = headId
        · subst id
          cases head with
          | leaf =>
              have hb := Net.used_agent_slot_bound hwf hhead hused
              simp only [Kind.arity] at hb
              interval_cases slot; simp_all
          | stem u =>
              have h1 := hhead.2.not_continuation hwf hcont
              have hb := Net.used_agent_slot_bound hwf hhead.1 hused
              simp only [Kind.arity] at hb
              interval_cases slot <;> simp_all
          | fork u v =>
              have h1 := hhead.2.1.not_continuation hwf hcont
              have h2 := hhead.2.2.not_continuation hwf hcont
              have hb := Net.used_agent_slot_bound hwf hhead.1 hused
              simp only [Kind.arity] at hb
              interval_cases slot <;> simp_all
        · simp [belongs, hid, hihead]

/-- A concrete Triage interaction starts exactly the source selected by the
corresponding abstract-machine transition. This is a local simulation theorem;
the continuation graph and eventual erasure tasks are not yet simulated. -/
theorem dispatch {net : Net} (hv : net.valid = true)
    {triageId headId : Nat} {continuation : TriageConcrete.End}
    {head : TriageMachine.Head} {w x y : TriageMachine.Syntax}
    (ha : net.Active triageId headId) (ht : net.kind? triageId = some .triage)
    (hhead : Observed net headId head)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hout : belongs triageId headId continuation = false)
    (hw : RawInput net triageId 2 w) (hx : RawInput net triageId 3 x)
    (hy : RawInput net triageId 4 y) (frames : List TriageMachine.Frame) :
    let next := net.replace (dispatchRule head) triageId headId
    Step net next ∧ EvalTask next (selected head w x y) continuation ∧
      TriageMachine.Step (.ret head (.triage w x y :: frames))
        (.eval (selected head w x y) frames) := by
  cases head with
  | leaf =>
      have h := leaf_selects hv ha ht hhead hcont hout hw
      exact ⟨h.1, h.2, .triageLeaf⟩
  | stem u =>
      have h := stem_selects hv ha ht hhead.1 hcont hout hx hhead.2
      exact ⟨h.1, h.2, .triageStem⟩
  | fork u v =>
      have h := fork_selects hv ha ht hhead.1 hcont hout hy hhead.2.1 hhead.2.2
      exact ⟨h.1, h.2, .triageFork⟩

theorem dispatch_from_inputs {net : Net} (hv : net.valid = true)
    {triageId headId : Nat} {continuation : TriageConcrete.End}
    {head : TriageMachine.Head} {w x y : TriageMachine.Syntax}
    (ha : net.Active triageId headId) (ht : net.kind? triageId = some .triage)
    (hhead : Observed net headId head)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hw : RawInput net triageId 2 w) (hx : RawInput net triageId 3 x)
    (hy : RawInput net triageId 4 y) (frames : List TriageMachine.Frame) :
    let next := net.replace (dispatchRule head) triageId headId
    Step net next ∧ EvalTask next (selected head w x y) continuation ∧
      TriageMachine.Step (.ret head (.triage w x y :: frames))
        (.eval (selected head w x y) frames) :=
  dispatch hv ha ht hhead hcont
    (continuation_outside (valid_wellFormed hv) ha ht hhead hcont hw hx hy) hw hx hy frames

/-- The same local concrete inspection is sound for the original TC term
reduction relation, under every abstract continuation stack. -/
theorem dispatch_tc_sound {net : Net} (hv : net.valid = true)
    {triageId headId : Nat} {continuation : TriageConcrete.End}
    {head : TriageMachine.Head} {w x y : TriageMachine.Syntax}
    (ha : net.Active triageId headId) (ht : net.kind? triageId = some .triage)
    (hhead : Observed net headId head)
    (hcont : net.neighbor (.agent triageId 1) = some continuation)
    (hw : RawInput net triageId 2 w) (hx : RawInput net triageId 3 x)
    (hy : RawInput net triageId 4 y) (frames : List TriageMachine.Frame) :
    let next := net.replace (dispatchRule head) triageId headId
    Step net next ∧ EvalTask next (selected head w x y) continuation ∧
      Relation.ReflTransGen Reduces
        (TriageMachine.State.ret head (.triage w x y :: frames)).toTerm
        (TriageMachine.State.eval (selected head w x y) frames).toTerm := by
  have hd := dispatch_from_inputs hv ha ht hhead hcont hw hx hy frames
  exact ⟨hd.1, hd.2.1, hd.2.2.sound⟩

end TriageDispatch
