/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageEncoding

/-! Semantic endpoints of a concrete exported rule replacement. -/

namespace TriageLocalSemantics
open TriageConcrete TriageRuleModel TriageRules TriageRuleProperties
open TriageBoundary TriagePreservation TriageReduction TriageResidual
open TriagePaths TriageSplicePaths TriageSplice TriageEncoding

theorem exported_rule_wellFormed {rule : Rule} (h : rule ∈ rules) :
    rule.wellFormed = true := by
  have hall : ∀ rule ∈ rules, rule.wellFormed = true := by
    simpa only [List.all_eq_true] using rules_wellFormed
  exact hall rule h

/-- Declarative boundary routes determine the actual output neighbor; this
uses the proved fuel bound and coverage of the executable splice. -/
theorem Net.replace_route {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    {source target : TriageConcrete.End}
    (hroute : Route (oldLayer net left right) (ruleLayer rule net.nextId) source target) :
    (net.replace rule left right).neighbor source = some target := by
  have hwf := valid_wellFormed hvalid
  rcases Net.redexChoice_sound hwf hchoice with ⟨hr, ha, hl, hright⟩
  have hrwf := exported_rule_wellFormed hr
  have houter := oldLayer_nodup hwf left right
  have hinner := ruleLayer_nodup hrwf net.nextId
  have hdisjoint := old_rule_real_disjoint hvalid rule left right
  have hsplice := concrete_splice_matching_and_coverage hvalid hrwf ha hl hright
  have hsource := (hsplice.2 source).mpr (route_source_exposed hroute)
  rcases neighborIn_total hsplice.1 hsource with ⟨other, hneighbor⟩
  have hactual : Route (oldLayer net left right) (ruleLayer rule net.nextId) source other := by
    rcases neighborIn_sound hneighbor with hwire | hwire
    · exact (spliceStarts_matching houter hinner hdisjoint _).2 _ hwire
    · exact Route.symmetric houter hinner
        ((spliceStarts_matching houter hinner hdisjoint _).2 _ hwire)
  have heq := Route.source_unique houter hinner hdisjoint hactual hroute
  subst other
  have hnext := Net.wellFormed_nodup
    (valid_wellFormed (Net.redexChoice_preserves_valid hvalid hchoice))
  rcases neighborIn_sound hneighbor with hwire | hwire
  · apply neighborIn_of_mem hnext
    change (source, target) ∈ _ ++ _ ++ spliceStarts _ _ _
    exact List.mem_append_right _ hwire
  · apply neighborIn_of_mem_right hnext
    change (target, source) ∈ _ ++ _ ++ spliceStarts _ _ _
    exact List.mem_append_right _ hwire

theorem oldLayer_neighbor {net : Net} (hwf : net.wellFormed = true)
    {left right : Nat} {source target : TriageConcrete.End}
    (hn : net.neighbor source = some target)
    (hb : belongs left right source = true)
    (hl : source ≠ .agent left 0) (hr : source ≠ .agent right 0) :
    layerNeighbor (oldLayer net left right) (Node.fromOld left right source) =
      some (Node.fromOld left right target) := by
  have hmem : ∀ a b, (a, b) ∈ net.wires → source ∈ [a, b] →
      (Node.fromOld left right a, Node.fromOld left right b) ∈ oldLayer net left right := by
    intro a b hwire hs
    have ht : (a, b) ∈ touched net left right := by
      apply List.mem_filter.mpr
      refine ⟨hwire, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> simp [hb]
    have hnot : sameWire (a, b) (.agent left 0, .agent right 0) = false := by
      by_contra hnot
      have ht : sameWire (a, b) (.agent left 0, .agent right 0) = true := by
        cases hh : sameWire (a, b) (.agent left 0, .agent right 0) <;> simp_all
      rcases sameWire_port_is_principal ht hs with heq | heq
      · exact hl heq
      · exact hr heq
    apply List.mem_map.mpr
    exact ⟨(a, b), List.mem_filter.mpr ⟨ht, by simp [hnot]⟩, rfl⟩
  rcases neighborIn_sound hn with hwire | hwire
  · exact layerNeighbor_of_mem (oldLayer_nodup hwf left right)
      (hmem source target hwire (by simp))
  · exact layerNeighbor_of_mem_right (oldLayer_nodup hwf left right)
      (hmem target source hwire (by simp))

/-- An interface attached to a fresh RHS port connects that port to the
corresponding old external endpoint in the actual resulting wire graph. -/
theorem Net.replace_interface {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right side slot : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    {oldPort oldTarget newTarget : TriageConcrete.End}
    (hold : net.neighbor oldPort = some oldTarget)
    (hbelongs : belongs left right oldPort = true)
    (hleft : oldPort ≠ .agent left 0) (hright : oldPort ≠ .agent right 0)
    (hiface : Node.fromOld left right oldPort = .iface side slot)
    (houtside : belongs left right oldTarget = false)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface side slot) =
      some (.real newTarget)) :
    (net.replace rule left right).neighbor newTarget = some oldTarget := by
  apply Net.replace_route hvalid hchoice
  have ho := oldLayer_neighbor (valid_wellFormed hvalid) hold hbelongs hleft hright
  rw [hiface, fromOld_real_of_not_belongs left right oldTarget houtside] at ho
  exact ⟨side, slot, false, 1, hnew, Walk.stop ho⟩

theorem Net.replace_created_kind {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right index : Nat} {kind : Kind}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    (hk : rule.agents[index]? = some kind) :
    (net.replace rule left right).kind? (net.nextId + index) = some kind := by
  have hv := Net.redexChoice_preserves_valid hvalid hchoice
  apply Net.kind_of_mem ((Net.wellFormed_iff _).mp (valid_wellFormed hv)).1
  rw [Net.replace_agents]
  apply List.mem_append_right
  apply List.mem_map.mpr
  exact ⟨(kind, index), List.mem_zipIdx_iff_getElem?.mpr hk, rfl⟩

theorem Net.replace_internal_wire {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right first firstSlot second secondSlot : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    (hwire : (TriageRuleModel.End.agent first firstSlot, .agent second secondSlot) ∈ rule.wires) :
    (net.replace rule left right).neighbor (.agent (net.nextId + first) firstSlot) =
      some (.agent (net.nextId + second) secondSlot) := by
  have hnext := Net.wellFormed_nodup
    (valid_wellFormed (Net.redexChoice_preserves_valid hvalid hchoice))
  apply neighborIn_of_mem hnext
  change _ ∈ _ ++ direct (ruleLayer rule net.nextId) ++ _
  apply List.mem_append_left
  apply List.mem_append_right
  apply direct_mem_iff.mpr
  exact List.mem_map.mpr ⟨_, hwire, rfl⟩

theorem Net.replace_left_aux {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right slot : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    {oldTarget newTarget : TriageConcrete.End}
    (hold : net.neighbor (.agent left (slot + 1)) = some oldTarget)
    (houtside : belongs left right oldTarget = false)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 0 (slot + 1)) =
      some (.real newTarget)) :
    (net.replace rule left right).neighbor newTarget = some oldTarget := by
  exact Net.replace_interface (side := 0) (slot := slot + 1) hvalid hchoice hold
    (by simp [belongs]) (by simp) (by simp) (by simp [Node.fromOld]) houtside hnew

theorem Net.replace_right_aux {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right slot : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    {oldTarget newTarget : TriageConcrete.End}
    (hold : net.neighbor (.agent right (slot + 1)) = some oldTarget)
    (houtside : belongs left right oldTarget = false)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 1 (slot + 1)) =
      some (.real newTarget)) :
    (net.replace rule left right).neighbor newTarget = some oldTarget := by
  have hactive := (Net.redexChoice_sound (valid_wellFormed hvalid) hchoice).2.1
  have hne := active_ids_ne (valid_wellFormed hvalid) hactive
  exact Net.replace_interface (side := 1) (slot := slot + 1) hvalid hchoice hold
    (by simp [belongs]) (by simp) (by simp)
    (by simp [Node.fromOld, Ne.symm hne]) houtside hnew

def evalLeafRule : Rule :=
  { left := .eval, right := .leaf, agents := [.leaf],
    wires := [(.agent 0 0, .iface 0 1)] }

theorem evalLeafRule_mem : evalLeafRule ∈ rules := by decide

/-- The Eval/Leaf interaction exposes a leaf at the evaluator's continuation
port in every valid surrounding net, not just in a closed example. -/
theorem eval_leaf_returns {net : Net} (hvalid : net.valid = true)
    {evalId leafId : Nat} {continuation : TriageConcrete.End}
    (ha : net.Active evalId leafId)
    (he : net.kind? evalId = some .eval) (hl : net.kind? leafId = some .leaf)
    (hc : net.neighbor (.agent evalId 1) = some continuation)
    (houtside : belongs evalId leafId continuation = false) :
    let next := net.replace evalLeafRule evalId leafId
    Step net next ∧ Represents next (.agent net.nextId 0) .leaf ∧
      next.neighbor (.agent net.nextId 0) = some continuation := by
  have hchoice := Net.redexChoice_complete evalLeafRule_mem ha he hl
  refine ⟨Step.chosen hchoice, Represents.leaf ?_, ?_⟩
  · have hk := Net.replace_created_kind hvalid hchoice (index := 0) (kind := .leaf) (by rfl)
    exact Net.kind_mem (by simpa using hk)
  · apply Net.replace_interface (side := 0) (slot := 1) hvalid hchoice hc (by simp [belongs])
      (by simp) (by simp) (by simp [Node.fromOld]) houtside
    simp [ruleLayer, evalLeafRule, Node.fromRule, layerNeighbor]

def callLeafRule : Rule :=
  { left := .call, right := .leaf, agents := [.stem],
    wires := [(.agent 0 0, .iface 0 1), (.agent 0 1, .iface 0 2)] }

theorem callLeafRule_mem : callLeafRule ∈ rules := by decide

/-- Calling a leaf constructs a stem with the exact raw argument, which may
itself be reducible syntax. No reduction of that argument is required. -/
theorem call_leaf_returns {net : Net} (hvalid : net.valid = true)
    {callId leafId : Nat} {continuation argumentRoot : TriageConcrete.End} {argument : TriageMachine.Syntax}
    (ha : net.Active callId leafId)
    (he : net.kind? callId = some .call) (hl : net.kind? leafId = some .leaf)
    (hc : net.neighbor (.agent callId 1) = some continuation)
    (houtside : belongs callId leafId continuation = false)
    (harg : Linked net (.agent callId 2) argumentRoot)
    (hr : Represents net argumentRoot argument) :
    let next := net.replace callLeafRule callId leafId
    Step net next ∧ Represents next (.agent net.nextId 0) (TriageMachine.stem argument) ∧
      next.neighbor (.agent net.nextId 0) = some continuation := by
  have hchoice := Net.redexChoice_complete callLeafRule_mem ha he hl
  have hwf := valid_wellFormed hvalid
  have hargOutside := represented_child_outside hwf ha (by decide : 2 ≠ 0) harg hr
  have hargNext := hr.replace hvalid hchoice hargOutside
  have hargWire : (net.replace callLeafRule callId leafId).neighbor (.agent net.nextId 1) =
      some argumentRoot := by
    apply Net.replace_left_aux (slot := 1) hvalid hchoice (harg.neighbor hwf) hargOutside
    simp [ruleLayer, callLeafRule, Node.fromRule, layerNeighbor]
  have hkind := Net.replace_created_kind hvalid hchoice (index := 0) (kind := .stem) (by rfl)
  refine ⟨Step.chosen hchoice, Represents.stem (Net.kind_mem (by simpa using hkind))
    (neighborIn_sound hargWire) hargNext, ?_⟩
  apply Net.replace_left_aux (slot := 0) hvalid hchoice hc houtside
  simp [ruleLayer, callLeafRule, Node.fromRule, layerNeighbor]

def callStemRule : Rule :=
  { left := .call, right := .stem, agents := [.fork],
    wires := [(.agent 0 0, .iface 0 1), (.agent 0 1, .iface 1 1), (.agent 0 2, .iface 0 2)] }

theorem callStemRule_mem : callStemRule ∈ rules := by decide

theorem call_stem_returns {net : Net} (hvalid : net.valid = true)
    {callId stemId : Nat} {continuation childRoot argumentRoot : TriageConcrete.End}
    {child argument : TriageMachine.Syntax}
    (ha : net.Active callId stemId)
    (he : net.kind? callId = some .call) (hl : net.kind? stemId = some .stem)
    (hc : net.neighbor (.agent callId 1) = some continuation)
    (houtside : belongs callId stemId continuation = false)
    (hchild : Linked net (.agent stemId 1) childRoot) (hcr : Represents net childRoot child)
    (harg : Linked net (.agent callId 2) argumentRoot) (har : Represents net argumentRoot argument) :
    let next := net.replace callStemRule callId stemId
    Step net next ∧ Represents next (.agent net.nextId 0) (TriageMachine.fork child argument) ∧
      next.neighbor (.agent net.nextId 0) = some continuation := by
  have hchoice := Net.redexChoice_complete callStemRule_mem ha he hl
  have hwf := valid_wellFormed hvalid
  have hcOutside := represented_child_outside hwf ha (by decide : 1 ≠ 0) hchild hcr
  have haOutside := represented_child_outside hwf ha (by decide : 2 ≠ 0) harg har
  have hcNext := hcr.replace hvalid hchoice hcOutside
  have haNext := har.replace hvalid hchoice haOutside
  have hcWire : (net.replace callStemRule callId stemId).neighbor (.agent net.nextId 1) =
      some childRoot := by
    apply Net.replace_right_aux (slot := 0) hvalid hchoice (hchild.neighbor hwf) hcOutside
    simp [ruleLayer, callStemRule, Node.fromRule, layerNeighbor]
  have haWire : (net.replace callStemRule callId stemId).neighbor (.agent net.nextId 2) =
      some argumentRoot := by
    apply Net.replace_left_aux (slot := 1) hvalid hchoice (harg.neighbor hwf) haOutside
    simp [ruleLayer, callStemRule, Node.fromRule, layerNeighbor]
  have hkind := Net.replace_created_kind hvalid hchoice (index := 0) (kind := .fork) (by rfl)
  refine ⟨Step.chosen hchoice, Represents.fork (Net.kind_mem (by simpa using hkind))
    (neighborIn_sound hcWire) (neighborIn_sound haWire) hcNext haNext, ?_⟩
  apply Net.replace_left_aux (slot := 0) hvalid hchoice hc houtside
  simp [ruleLayer, callStemRule, Node.fromRule, layerNeighbor]

end TriageLocalSemantics
