/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageConcrete
import Mathlib.Data.List.Flatten

/-!
Local invariants for the two layers joined by a concrete rule replacement.
The replacement layer comes from the exported RHS. The old layer comes from
the wires attached to the removed pair. Each must be a matching in its own
right before alternating paths are followed through their shared interface.
-/

namespace TriageBoundary
open TriageRuleModel TriageConcrete

def layerEnds (layer : Layer) : List Node :=
  layer.flatMap fun (a, b) => [a, b]

def ruleLayer (rule : Rule) (fresh : Nat) : Layer :=
  rule.wires.map fun (a, b) =>
    (Node.fromRule fresh a, Node.fromRule fresh b)

def ruleIfaces (rule : Rule) : List Node :=
  (List.range rule.left.arity).map (fun slot => Node.iface 0 (slot + 1)) ++
  (List.range rule.right.arity).map (fun slot => Node.iface 1 (slot + 1))

theorem ruleIfaces_length (rule : Rule) :
    (ruleIfaces rule).length = rule.left.arity + rule.right.arity := by
  simp [ruleIfaces]

theorem ruleIfaces_nodup (rule : Rule) : (ruleIfaces rule).Nodup := by
  apply List.nodup_append'.2
  constructor
  · apply List.Nodup.map
    · intro a b h
      cases (Node.iface.inj h) with
      | intro _ hslot => omega
    · exact List.nodup_range
  constructor
  · apply List.Nodup.map
    · intro a b h
      cases (Node.iface.inj h) with
      | intro _ hslot => omega
    · exact List.nodup_range
  · rw [List.disjoint_left]
    intro node hleft hright
    rcases List.mem_map.mp hleft with ⟨a, _, ha⟩
    rcases List.mem_map.mp hright with ⟨b, _, hb⟩
    rw [← ha] at hb
    cases hb

theorem ruleIfaces_mem_cases {rule : Rule} {node : Node}
    (hmem : node ∈ ruleIfaces rule) :
    (∃ slot, slot < rule.left.arity ∧ node = .iface 0 (slot + 1)) ∨
    (∃ slot, slot < rule.right.arity ∧ node = .iface 1 (slot + 1)) := by
  rcases List.mem_append.mp hmem with hleft | hright
  · rcases List.mem_map.mp hleft with ⟨slot, hslot, heq⟩
    exact Or.inl ⟨slot, List.mem_range.mp hslot, heq.symm⟩
  · rcases List.mem_map.mp hright with ⟨slot, hslot, heq⟩
    exact Or.inr ⟨slot, List.mem_range.mp hslot, heq.symm⟩

def belongs (left right : Nat) : TriageConcrete.End → Bool
  | .agent id _ => id == left || id == right
  | .free _ => false

def touched (net : Net) (left right : Nat) : List TriageConcrete.Wire :=
  net.wires.filter fun (a, b) => belongs left right a || belongs left right b

def untouched (net : Net) (left right : Nat) : List TriageConcrete.Wire :=
  net.wires.filter fun (a, b) => !(belongs left right a || belongs left right b)

def oldLayer (net : Net) (left right : Nat) : Layer :=
  ((touched net left right).filter fun edge =>
    !sameWire edge (.agent left 0, .agent right 0)).map fun (a, b) =>
      (Node.fromOld left right a, Node.fromOld left right b)

theorem layerEnds_map {α β : Type} (f : α → β)
    (wires : List (α × α)) :
    (wires.map fun (a, b) => (f a, f b)).flatMap
      (fun (a, b) => [a, b]) =
    (wires.flatMap fun (a, b) => [a, b]).map f := by
  simp [List.flatMap_map, List.map_flatMap]

theorem Node.fromRule_injective (fresh : Nat) :
    Function.Injective (Node.fromRule fresh) := by
  intro first second h
  cases first <;> cases second <;>
    simp [Node.fromRule] at h ⊢ <;> omega

theorem ruleLayer_ends (rule : Rule) (fresh : Nat) :
    layerEnds (ruleLayer rule fresh) =
      rule.used.map (Node.fromRule fresh) := by
  simp [layerEnds, ruleLayer, Rule.used, List.flatMap_map,
    List.map_flatMap]

theorem Node.fromOld_injective (left right : Nat) :
    Function.Injective (Node.fromOld left right) := by
  intro first second h
  cases first <;> cases second <;>
    simp only [Node.fromOld] at h <;>
    (try split_ifs at h) <;>
    simp_all [Node.iface.injEq, Node.real.injEq,
      TriageConcrete.End.agent.injEq]

theorem oldLayer_ends (net : Net) (left right : Nat) :
    layerEnds (oldLayer net left right) =
      (wireEnds ((touched net left right).filter fun edge =>
        !sameWire edge (.agent left 0, .agent right 0))).map
          (Node.fromOld left right) := by
  exact layerEnds_map _ _

theorem oldLayer_nodup {net : Net} (h : net.wellFormed = true)
    (left right : Nat) :
    (layerEnds (oldLayer net left right)).Nodup := by
  rw [oldLayer_ends]
  apply List.Nodup.map (Node.fromOld_injective left right)
  exact (net.wellFormed_nodup h).sublist
    ((List.filter_sublist).flatMap _ |>.trans
      ((List.filter_sublist).flatMap _))

theorem ruleLayer_nodup {rule : Rule} (h : rule.wellFormed = true)
    (fresh : Nat) : (layerEnds (ruleLayer rule fresh)).Nodup := by
  rw [ruleLayer_ends]
  exact ((Rule.wellFormed_iff rule).mp h).1.map
    (Node.fromRule_injective fresh)

theorem ruleLayer_covers {rule : Rule} (h : rule.wellFormed = true)
    (fresh : Nat) {end_ : TriageRuleModel.End}
    (hexpected : end_ ∈ rule.expected) :
    Node.fromRule fresh end_ ∈ layerEnds (ruleLayer rule fresh) := by
  rw [ruleLayer_ends]
  apply List.mem_map.mpr
  exact ⟨end_, ((Rule.wellFormed_iff rule).mp h).2.2 end_ hexpected, rfl⟩

theorem ruleLayer_ends_iff {rule : Rule} (h : rule.wellFormed = true)
    (fresh : Nat) (end_ : TriageRuleModel.End) :
    Node.fromRule fresh end_ ∈ layerEnds (ruleLayer rule fresh) ↔
      end_ ∈ rule.expected := by
  constructor
  · rw [ruleLayer_ends]
    intro hmem
    rcases List.mem_map.mp hmem with ⟨used, hused, heq⟩
    have : used = end_ := Node.fromRule_injective fresh heq
    exact ((Rule.wellFormed_iff rule).mp h).2.1 end_ (this ▸ hused)
  · exact ruleLayer_covers h fresh

theorem ruleLayer_no_primary_iface {rule : Rule}
    (h : rule.wellFormed = true) (fresh side : Nat) :
    Node.iface side 0 ∉ layerEnds (ruleLayer rule fresh) := by
  intro hmem
  have hexpected := (ruleLayer_ends_iff h fresh (.iface side 0)).mp hmem
  simp [Rule.expected] at hexpected

theorem ruleLayer_iface_mem_ruleIfaces {rule : Rule}
    (h : rule.wellFormed = true) (fresh side slot : Nat)
    (hmem : Node.iface side slot ∈ layerEnds (ruleLayer rule fresh)) :
    Node.iface side slot ∈ ruleIfaces rule := by
  have hexpected := (ruleLayer_ends_iff h fresh (.iface side slot)).mp hmem
  simp only [Rule.expected, List.mem_append] at hexpected
  rcases hexpected with (hleft | hright) | hnew
  · rcases List.mem_map.mp hleft with ⟨i, hi, heq⟩
    have hnode : Node.iface side slot = Node.iface 0 (i + 1) := by
      simpa [Node.fromRule] using congrArg (Node.fromRule fresh) heq.symm
    rw [hnode]
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rcases List.mem_map.mp hright with ⟨i, hi, heq⟩
    have hnode : Node.iface side slot = Node.iface 1 (i + 1) := by
      simpa [Node.fromRule] using congrArg (Node.fromRule fresh) heq.symm
    rw [hnode]
    exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · simp [List.mem_flatMap] at hnew

/-- Direct RHS wires retain their endpoints from the replacement matching. -/
theorem direct_ends_sublist (layer : Layer) :
    ((wireEnds (direct layer)).map Node.real).Sublist (layerEnds layer) := by
  induction layer with
  | nil => simp [direct, layerEnds, wireEnds]
  | cons wire rest ih =>
      rcases wire with ⟨a, b⟩
      cases a <;> cases b <;>
        simp [direct, wireEnds, layerEnds] at *
      · exact ih
      all_goals simpa using List.Sublist.cons _ (List.Sublist.cons _ ih)

theorem direct_ends_nodup {layer : Layer}
    (h : (layerEnds layer).Nodup) :
    (wireEnds (direct layer)).Nodup := by
  apply List.Nodup.of_map Node.real
  exact h.sublist (direct_ends_sublist layer)

theorem ruleLayer_direct_nodup {rule : Rule}
    (h : rule.wellFormed = true) (fresh : Nat) :
    (wireEnds (direct (ruleLayer rule fresh))).Nodup :=
  direct_ends_nodup (ruleLayer_nodup h fresh)

theorem ruleLayer_real_fresh {rule : Rule} {fresh id slot : Nat}
    (h : Node.real (.agent id slot) ∈ layerEnds (ruleLayer rule fresh)) :
    fresh ≤ id := by
  rw [ruleLayer_ends] at h
  rcases List.mem_map.mp h with ⟨source, _, heq⟩
  cases source with
  | iface side port => simp [Node.fromRule] at heq
  | agent index port =>
      simp [Node.fromRule] at heq
      omega

theorem ruleLayer_direct_fresh {rule : Rule} {fresh id slot : Nat}
    (h : TriageConcrete.End.agent id slot ∈
      wireEnds (direct (ruleLayer rule fresh))) :
    fresh ≤ id := by
  have hm : Node.real (.agent id slot) ∈
      (wireEnds (direct (ruleLayer rule fresh))).map Node.real :=
    List.mem_map.mpr ⟨_, h, rfl⟩
  exact ruleLayer_real_fresh ((direct_ends_sublist _).subset hm)

theorem ruleLayer_no_free {rule : Rule} {fresh name : Nat}
    (h : Node.real (.free name) ∈ layerEnds (ruleLayer rule fresh)) :
    False := by
  rw [ruleLayer_ends] at h
  rcases List.mem_map.mp h with ⟨source, _, heq⟩
  cases source <;> simp [Node.fromRule] at heq

theorem ruleLayer_direct_no_free {rule : Rule} {fresh name : Nat}
    (h : TriageConcrete.End.free name ∈
      wireEnds (direct (ruleLayer rule fresh))) : False := by
  have hm : Node.real (.free name) ∈
      (wireEnds (direct (ruleLayer rule fresh))).map Node.real :=
    List.mem_map.mpr ⟨_, h, rfl⟩
  exact ruleLayer_no_free ((direct_ends_sublist _).subset hm)

theorem net_used_agent_old {net : Net} (h : net.valid = true)
    {id slot : Nat} (hused : TriageConcrete.End.agent id slot ∈ net.used) :
    id < net.nextId := by
  have hv : net.wellFormed = true ∧ net.freshIds = true := by
    simpa [Net.valid] using h
  have hwf := hv.1
  have hfresh := hv.2
  have hexpected := ((Net.wellFormed_iff net).mp hwf).2.2.1 _ hused
  simp only [Net.expected, List.mem_append, List.mem_flatMap] at hexpected
  rcases hexpected with ⟨⟨entryId, kind⟩, hentry, hport⟩ | hfree
  · have hid : id = entryId := by
      rcases List.mem_map.mp hport with ⟨_, _, heq⟩
      cases heq
      rfl
    subst id
    have hf : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
      simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using hfresh
    exact hf (entryId, kind) hentry
  · simp at hfree

theorem untouched_ends_sublist (net : Net) (left right : Nat) :
    (wireEnds (untouched net left right)).Sublist net.used := by
  exact List.Sublist.flatMap List.filter_sublist _

theorem untouched_ends_nodup {net : Net} (h : net.wellFormed = true)
    (left right : Nat) :
    (wireEnds (untouched net left right)).Nodup :=
  (net.wellFormed_nodup h).sublist (untouched_ends_sublist net left right)

/-- Preserved old wires and direct replacement wires cannot share a port. -/
theorem untouched_direct_disjoint {net : Net} (h : net.valid = true)
    (rule : Rule) (left right : Nat) :
    (wireEnds (untouched net left right)).Disjoint
      (wireEnds (direct (ruleLayer rule net.nextId))) := by
  rw [List.disjoint_left]
  intro end_ hold hnew
  have hold' : end_ ∈ net.used :=
    (untouched_ends_sublist net left right).subset hold
  cases end_ with
  | free name => exact ruleLayer_direct_no_free hnew
  | agent id slot =>
      have hOld := net_used_agent_old h hold'
      have hNew := ruleLayer_direct_fresh hnew
      omega

theorem untouched_direct_nodup {net : Net} (hvalid : net.valid = true)
    {rule : Rule} (hrule : rule.wellFormed = true)
    (left right : Nat) :
    (wireEnds (untouched net left right ++
      direct (ruleLayer rule net.nextId))).Nodup := by
  have hwf : net.wellFormed = true := by
    simpa [Net.valid] using (Bool.and_eq_true_iff.mp hvalid).1
  simp only [wireEnds, List.flatMap_append]
  exact List.nodup_append'.2
    ⟨untouched_ends_nodup hwf left right,
      ruleLayer_direct_nodup hrule net.nextId,
      untouched_direct_disjoint hvalid rule left right⟩

theorem replace_wires (net : Net) (rule : Rule) (left right : Nat) :
    (net.replace rule left right).wires =
      untouched net left right ++
      direct (ruleLayer rule net.nextId) ++
      spliceStarts (oldLayer net left right) (ruleLayer rule net.nextId)
        (2 * (rule.left.arity + rule.right.arity) + 2) := by
  rfl

theorem left_mem_layerEnds {layer : Layer} {a b : Node}
    (h : (a, b) ∈ layer) : a ∈ layerEnds layer := by
  simp only [layerEnds, List.mem_flatMap]
  exact ⟨(a, b), h, by simp⟩

theorem right_mem_layerEnds {layer : Layer} {a b : Node}
    (h : (a, b) ∈ layer) : b ∈ layerEnds layer := by
  simp only [layerEnds, List.mem_flatMap]
  exact ⟨(a, b), h, by simp⟩

theorem layerNeighbor_of_mem {layer : Layer} {a b : Node}
    (hn : (layerEnds layer).Nodup) (h : (a, b) ∈ layer) :
    layerNeighbor layer a = some b := by
  induction layer with
  | nil => cases h
  | cons wire rest ih =>
      rcases wire with ⟨x, y⟩
      change (x :: y :: layerEnds rest).Nodup at hn
      have hx := List.nodup_cons.mp hn
      have hy := List.nodup_cons.mp hx.2
      rcases List.mem_cons.mp h with hfirst | hrest
      · have hxy : a = x ∧ b = y := Prod.mk.inj hfirst
        rcases hxy with ⟨rfl, rfl⟩
        simp [layerNeighbor]
      · have ha := left_mem_layerEnds hrest
        have hax : a ≠ x := by
          intro heq
          exact hx.1 (List.mem_cons_of_mem _ (heq ▸ ha))
        have hay : a ≠ y := by
          intro heq
          exact hy.1 (heq ▸ ha)
        simpa [layerNeighbor, hax, hay] using ih hy.2 hrest

theorem layerNeighbor_of_mem_right {layer : Layer} {a b : Node}
    (hn : (layerEnds layer).Nodup) (h : (a, b) ∈ layer) :
    layerNeighbor layer b = some a := by
  induction layer with
  | nil => cases h
  | cons wire rest ih =>
      rcases wire with ⟨x, y⟩
      change (x :: y :: layerEnds rest).Nodup at hn
      have hx := List.nodup_cons.mp hn
      have hy := List.nodup_cons.mp hx.2
      rcases List.mem_cons.mp h with hfirst | hrest
      · have hxy : a = x ∧ b = y := Prod.mk.inj hfirst
        have hne : y ≠ x := by
          intro heq
          exact hx.1 (List.mem_cons.mpr (Or.inl heq.symm))
        rcases hxy with ⟨rfl, rfl⟩
        simp [layerNeighbor, hne]
      · have hb := right_mem_layerEnds hrest
        have hbx : b ≠ x := by
          intro heq
          exact hx.1 (List.mem_cons_of_mem _ (heq ▸ hb))
        have hby : b ≠ y := by
          intro heq
          exact hy.1 (heq ▸ hb)
        simpa [layerNeighbor, hbx, hby] using ih hy.2 hrest

theorem layerNeighbor_sound {layer : Layer} {a b : Node}
    (h : layerNeighbor layer a = some b) :
    (a, b) ∈ layer ∨ (b, a) ∈ layer := by
  induction layer with
  | nil => simp [layerNeighbor] at h
  | cons wire rest ih =>
      rcases wire with ⟨x, y⟩
      simp only [layerNeighbor] at h
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

theorem layerNeighbor_symmetric {layer : Layer} {a b : Node}
    (hn : (layerEnds layer).Nodup)
    (h : layerNeighbor layer a = some b) :
    layerNeighbor layer b = some a := by
  rcases layerNeighbor_sound h with hab | hba
  · exact layerNeighbor_of_mem_right hn hab
  · exact layerNeighbor_of_mem hn hba

theorem layerNeighbor_target_mem {layer : Layer} {a b : Node}
    (h : layerNeighbor layer a = some b) : b ∈ layerEnds layer := by
  rcases layerNeighbor_sound h with hab | hba
  · exact right_mem_layerEnds hab
  · exact left_mem_layerEnds hba

theorem layerNeighbor_total {layer : Layer} {node : Node}
    (hn : (layerEnds layer).Nodup)
    (hmem : node ∈ layerEnds layer) :
    ∃ target, layerNeighbor layer node = some target := by
  rcases List.mem_flatMap.mp hmem with ⟨wire, hwire, hport⟩
  rcases wire with ⟨a, b⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with heq | heq
  · subst node
    exact ⟨b, layerNeighbor_of_mem hn hwire⟩
  · subst node
    exact ⟨a, layerNeighbor_of_mem_right hn hwire⟩

theorem incident_edge_unique {net : Net} (hwf : net.wellFormed = true)
    {p q a b : TriageConcrete.End}
    (hpq : net.neighbor p = some q)
    (hwire : (a, b) ∈ net.wires) (hincident : a = p ∨ b = p) :
    sameWire (a, b) (p, q) = true := by
  change neighborIn net.wires p = some q at hpq
  rcases hincident with ha | hb
  · have hab := neighborIn_of_mem (net.wellFormed_nodup hwf) hwire
    rw [ha, hpq] at hab
    have : b = q := Option.some.inj hab.symm
    subst a
    subst b
    simp [sameWire]
  · have hba := neighborIn_of_mem_right (net.wellFormed_nodup hwf) hwire
    rw [hb, hpq] at hba
    have : a = q := Option.some.inj hba.symm
    subst a
    subst b
    simp [sameWire]

theorem active_ids_ne {net : Net} (hwf : net.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right) :
    left ≠ right := by
  intro heq
  have h := hactive.2.2
  rw [← heq] at h
  exact neighborIn_irreflexive (net.wellFormed_nodup hwf) h

theorem oldLayer_excludes_principals {net : Net}
    (hwf : net.wellFormed = true) {left right : Nat}
    (hactive : net.Active left right) {edge : TriageConcrete.Wire}
    (h : edge ∈ (touched net left right).filter fun edge =>
      !sameWire edge (.agent left 0, .agent right 0)) :
    TriageConcrete.End.agent left 0 ∉ [edge.1, edge.2] ∧
      TriageConcrete.End.agent right 0 ∉ [edge.1, edge.2] := by
  have hwire : edge ∈ net.wires :=
    List.filter_sublist.subset (List.filter_sublist.subset h)
  have hnot : sameWire edge (.agent left 0, .agent right 0) = false := by
    have := (List.mem_filter.mp h).2
    simpa using this
  rcases edge with ⟨a, b⟩
  constructor
  · intro hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hincident : a = .agent left 0 ∨ b = .agent left 0 :=
      hp.elim (fun heq => Or.inl heq.symm) (fun heq => Or.inr heq.symm)
    have hsame := incident_edge_unique hwf hactive.2.2 hwire hincident
    exact Bool.false_ne_true (hnot.symm.trans hsame)
  · intro hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    have hreverse : net.neighbor (.agent right 0) =
        some (.agent left 0) :=
      neighborIn_symmetric (net.wellFormed_nodup hwf) hactive.2.2
    have hincident : a = .agent right 0 ∨ b = .agent right 0 :=
      hp.elim (fun heq => Or.inl heq.symm) (fun heq => Or.inr heq.symm)
    have hsame := incident_edge_unique hwf hreverse hwire hincident
    have hsame' : sameWire (a, b)
        (.agent left 0, .agent right 0) = true := by
      simpa [sameWire, and_comm, or_comm] using hsame
    exact Bool.false_ne_true (hnot.symm.trans hsame')

theorem oldLayer_no_primary_iface {net : Net}
    (hwf : net.wellFormed = true) {left right : Nat}
    (hactive : net.Active left right) :
    Node.iface 0 0 ∉ layerEnds (oldLayer net left right) ∧
      Node.iface 1 0 ∉ layerEnds (oldLayer net left right) := by
  have hne := active_ids_ne hwf hactive
  constructor
  · intro hmem
    rw [oldLayer_ends] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
    have hsourceEq : source = .agent left 0 :=
      Node.fromOld_injective left right
        (heq.trans (by simp [Node.fromOld]))
    rcases List.mem_flatMap.mp hsource with ⟨edge, hedge, hport⟩
    have hno := (oldLayer_excludes_principals hwf hactive hedge).1
    rcases edge with ⟨a, b⟩
    exact hno (hsourceEq ▸ hport)
  · intro hmem
    rw [oldLayer_ends] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
    have hsourceEq : source = .agent right 0 :=
      Node.fromOld_injective left right
        (heq.trans (by simp [Node.fromOld, hne.symm]))
    rcases List.mem_flatMap.mp hsource with ⟨edge, hedge, hport⟩
    have hno := (oldLayer_excludes_principals hwf hactive hedge).2
    rcases edge with ⟨a, b⟩
    exact hno (hsourceEq ▸ hport)

theorem sameWire_port_is_principal {left right : Nat}
    {edge : TriageConcrete.Wire} {source : TriageConcrete.End}
    (hsame : sameWire edge (.agent left 0, .agent right 0) = true)
    (hport : source ∈ [edge.1, edge.2]) :
    source = .agent left 0 ∨ source = .agent right 0 := by
  rcases edge with ⟨a, b⟩
  simp only [sameWire, decide_eq_true_eq] at hsame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hsame with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hport with hp | hp <;> simp_all

theorem oldLayer_covers_used {net : Net} {left right : Nat}
    {source : TriageConcrete.End} (hused : source ∈ net.used)
    (hbelongs : belongs left right source = true)
    (hleft : source ≠ .agent left 0)
    (hright : source ≠ .agent right 0) :
    Node.fromOld left right source ∈
      layerEnds (oldLayer net left right) := by
  rcases List.mem_flatMap.mp hused with ⟨edge, hwire, hport⟩
  have htouched : edge ∈ touched net left right := by
    apply List.mem_filter.mpr
    constructor
    · exact hwire
    · rcases edge with ⟨a, b⟩
      have hloc := hport
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hloc
      rcases hloc with hs | hs
      · rw [← hs]
        simp [hbelongs]
      · rw [← hs]
        simp [hbelongs]
  have hnot : sameWire edge (.agent left 0, .agent right 0) = false := by
    by_contra h
    have hsame : sameWire edge (.agent left 0, .agent right 0) = true := by
      cases hval : sameWire edge (.agent left 0, .agent right 0) <;>
        simp_all
    rcases sameWire_port_is_principal hsame hport with hp | hp
    · exact hleft hp
    · exact hright hp
  rw [oldLayer_ends]
  apply List.mem_map.mpr
  exact ⟨source, List.mem_flatMap.mpr
    ⟨edge, List.mem_filter.mpr ⟨htouched, by simp [hnot]⟩, hport⟩, rfl⟩

theorem oldLayer_covers_left_aux {net : Net} {left right slot : Nat}
    (hused : TriageConcrete.End.agent left (slot + 1) ∈ net.used) :
    Node.iface 0 (slot + 1) ∈ layerEnds (oldLayer net left right) := by
  have h := oldLayer_covers_used (left := left) (right := right) hused
    (by simp [belongs])
    (by simp)
    (by simp)
  simpa [Node.fromOld] using h

theorem oldLayer_covers_right_aux {net : Net} {left right slot : Nat}
    (hne : left ≠ right)
    (hused : TriageConcrete.End.agent right (slot + 1) ∈ net.used) :
    Node.iface 1 (slot + 1) ∈ layerEnds (oldLayer net left right) := by
  have h := oldLayer_covers_used (left := left) (right := right) hused
    (by simp [belongs])
    (by simp [hne.symm])
    (by simp)
  simpa [Node.fromOld, hne.symm] using h

theorem Net.kind_mem {net : Net} {id : Nat} {kind : Kind}
    (hkind : net.kind? id = some kind) : (id, kind) ∈ net.agents := by
  unfold Net.kind? at hkind
  cases hfind : net.agents.find? (fun entry => entry.1 == id) with
  | none => simp [hfind] at hkind
  | some entry =>
      have hmem := List.mem_of_find?_eq_some hfind
      have hid := List.find?_some hfind
      simp only [hfind, Option.map_some, Option.some.injEq] at hkind
      rcases entry with ⟨foundId, foundKind⟩
      simp only [beq_iff_eq] at hid
      simp only at hkind
      subst foundId
      subst foundKind
      exact hmem

theorem ids_unique {agents : List (Nat × Kind)}
    (hids : (agents.map Prod.fst).Nodup)
    {id : Nat} {first second : Kind}
    (hfirst : (id, first) ∈ agents)
    (hsecond : (id, second) ∈ agents) : first = second := by
  induction agents with
  | nil => cases hfirst
  | cons head rest ih =>
      rcases head with ⟨headId, headKind⟩
      have hn := List.nodup_cons.mp hids
      rcases List.mem_cons.mp hfirst with hf | hf
      · rcases List.mem_cons.mp hsecond with hs | hs
        · have hf' : id = headId ∧ first = headKind := Prod.mk.inj hf
          have hs' : id = headId ∧ second = headKind := Prod.mk.inj hs
          exact hf'.2.trans hs'.2.symm
        · have hid : id = headId := (Prod.mk.inj hf).1
          have hmem : headId ∈ rest.map Prod.fst := by
            apply List.mem_map.mpr
            exact ⟨(id, second), hs, by simpa using hid⟩
          exact False.elim (hn.1 hmem)
      · rcases List.mem_cons.mp hsecond with hs | hs
        · have hid : id = headId := (Prod.mk.inj hs).1
          have hmem : headId ∈ rest.map Prod.fst := by
            apply List.mem_map.mpr
            exact ⟨(id, first), hf, by simpa using hid⟩
          exact False.elim (hn.1 hmem)
        · exact ih hn.2 hf hs

theorem Net.used_agent_slot_bound {net : Net}
    (hwf : net.wellFormed = true)
    {id slot : Nat} {kind : Kind}
    (hkind : net.kind? id = some kind)
    (hused : TriageConcrete.End.agent id slot ∈ net.used) :
    slot ≤ kind.arity := by
  have hids := ((Net.wellFormed_iff net).mp hwf).1
  have hexpected := ((Net.wellFormed_iff net).mp hwf).2.2.1 _ hused
  simp only [Net.expected, List.mem_append, List.mem_flatMap] at hexpected
  rcases hexpected with ⟨⟨otherId, otherKind⟩, hentry, hport⟩ | hfree
  · rcases List.mem_map.mp hport with ⟨port, hslot, heq⟩
    have heq' : id = otherId ∧ slot = port :=
      TriageConcrete.End.agent.inj heq.symm
    rcases heq' with ⟨hid, hportEq⟩
    rw [← hid] at hentry hslot
    rw [← hportEq] at hslot
    have hk : kind = otherKind :=
      ids_unique hids (Net.kind_mem hkind) hentry
    rw [← hk] at hslot
    have hlt : slot < kind.arity + 1 := by
      simpa only using List.mem_range.mp hslot
    omega
  · simp at hfree

theorem Net.aux_used {net : Net} (hwf : net.wellFormed = true)
    {id : Nat} {kind : Kind} {slot : Nat}
    (hkind : net.kind? id = some kind) (hslot : slot < kind.arity) :
    TriageConcrete.End.agent id (slot + 1) ∈ net.used := by
  apply ((Net.wellFormed_iff net).mp hwf).2.2.2
  simp only [Net.expected, List.mem_append]
  left
  apply List.mem_flatMap.mpr
  refine ⟨(id, kind), Net.kind_mem hkind, ?_⟩
  apply List.mem_map.mpr
  have hslot' : slot + 1 < kind.arity + 1 := by omega
  exact ⟨slot + 1, List.mem_range.mpr hslot', rfl⟩

theorem oldLayer_covers_rule_left {net : Net} (hwf : net.wellFormed = true)
    (rule : Rule) {left right slot : Nat}
    (hkind : net.kind? left = some rule.left)
    (hslot : slot < rule.left.arity) :
    Node.iface 0 (slot + 1) ∈ layerEnds (oldLayer net left right) :=
  oldLayer_covers_left_aux (Net.aux_used hwf hkind hslot)

theorem oldLayer_covers_rule_right {net : Net} (hwf : net.wellFormed = true)
    (rule : Rule) {left right slot : Nat}
    (hne : left ≠ right)
    (hkind : net.kind? right = some rule.right)
    (hslot : slot < rule.right.arity) :
    Node.iface 1 (slot + 1) ∈ layerEnds (oldLayer net left right) :=
  oldLayer_covers_right_aux hne (Net.aux_used hwf hkind hslot)

theorem matched_left_aux {net : Net} (hwf : net.wellFormed = true)
    {rule : Rule} (hrule : rule.wellFormed = true)
    {left right slot : Nat}
    (hkind : net.kind? left = some rule.left)
    (hslot : slot < rule.left.arity) :
    Node.iface 0 (slot + 1) ∈ layerEnds (oldLayer net left right) ∧
    Node.iface 0 (slot + 1) ∈ layerEnds (ruleLayer rule net.nextId) := by
  constructor
  · exact oldLayer_covers_rule_left hwf rule hkind hslot
  · have hexpected : TriageRuleModel.End.iface 0 (slot + 1) ∈
        rule.expected := by
      simp only [Rule.expected, List.mem_append]
      left
      left
      apply List.mem_map.mpr
      exact ⟨slot, List.mem_range.mpr hslot, rfl⟩
    simpa [Node.fromRule] using ruleLayer_covers hrule net.nextId hexpected

theorem matched_right_aux {net : Net} (hwf : net.wellFormed = true)
    {rule : Rule} (hrule : rule.wellFormed = true)
    {left right slot : Nat}
    (hactive : net.Active left right)
    (hkind : net.kind? right = some rule.right)
    (hslot : slot < rule.right.arity) :
    Node.iface 1 (slot + 1) ∈ layerEnds (oldLayer net left right) ∧
    Node.iface 1 (slot + 1) ∈ layerEnds (ruleLayer rule net.nextId) := by
  constructor
  · exact oldLayer_covers_rule_right hwf rule (active_ids_ne hwf hactive)
      hkind hslot
  · have hexpected : TriageRuleModel.End.iface 1 (slot + 1) ∈
        rule.expected := by
      simp only [Rule.expected, List.mem_append]
      left
      right
      apply List.mem_map.mpr
      exact ⟨slot, List.mem_range.mpr hslot, rfl⟩
    simpa [Node.fromRule] using ruleLayer_covers hrule net.nextId hexpected

theorem oldLayer_iface_mem_ruleIfaces {net : Net}
    (hwf : net.wellFormed = true) (rule : Rule)
    {left right side slot : Nat}
    (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    (hmem : Node.iface side slot ∈ layerEnds (oldLayer net left right)) :
    Node.iface side slot ∈ ruleIfaces rule := by
  have hprimary := oldLayer_no_primary_iface hwf hactive
  have hne := active_ids_ne hwf hactive
  have hmem0 := hmem
  rw [oldLayer_ends] at hmem
  rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
  have hsourceUsed : source ∈ net.used := by
    exact ((List.filter_sublist).flatMap _ |>.trans
      ((List.filter_sublist).flatMap _)).subset hsource
  cases source with
  | free name => simp [Node.fromOld] at heq
  | agent id port =>
      by_cases hidl : id = left
      · have hnode : Node.iface side slot = Node.iface 0 port := by
          simpa [Node.fromOld, hidl] using heq.symm
        have hport : port ≠ 0 := by
          intro hz
          have : Node.iface 0 0 ∈ layerEnds (oldLayer net left right) := by
            simpa only [hnode, hz] using hmem0
          exact hprimary.1 this
        have hbound : port ≤ rule.left.arity := by
          rw [hidl] at hsourceUsed
          exact Net.used_agent_slot_bound hwf hleftkind hsourceUsed
        let i := port - 1
        have hip : port = i + 1 := by dsimp [i]; omega
        have hi : i < rule.left.arity := by omega
        rw [hnode, hip]
        exact List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
      · by_cases hidr : id = right
        · have hnode : Node.iface side slot = Node.iface 1 port := by
            simpa [Node.fromOld, hidl, hidr, hne.symm] using heq.symm
          have hport : port ≠ 0 := by
            intro hz
            have : Node.iface 1 0 ∈ layerEnds (oldLayer net left right) := by
              simpa only [hnode, hz] using hmem0
            exact hprimary.2 this
          have hbound : port ≤ rule.right.arity := by
            rw [hidr] at hsourceUsed
            exact Net.used_agent_slot_bound hwf hrightkind hsourceUsed
          let i := port - 1
          have hip : port = i + 1 := by dsimp [i]; omega
          have hi : i < rule.right.arity := by omega
          rw [hnode, hip]
          exact List.mem_append.mpr
            (Or.inr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
        · simp [Node.fromOld, hidl, hidr] at heq

theorem oldLayer_real_used {net : Net} {left right : Nat}
    {end_ : TriageConcrete.End}
    (hmem : Node.real end_ ∈ layerEnds (oldLayer net left right)) :
    end_ ∈ net.used := by
  rw [oldLayer_ends] at hmem
  rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
  have hsourceUsed : source ∈ net.used :=
    ((List.filter_sublist).flatMap _ |>.trans
      ((List.filter_sublist).flatMap _)).subset hsource
  have hsame : source = end_ := by
    cases source with
    | free name => simpa [Node.fromOld] using heq
    | agent id slot =>
        by_cases hleft : id = left
        · simp [Node.fromOld, hleft] at heq
        · by_cases hright : id = right
          · have hne : right ≠ left := by
              intro h
              exact hleft (hright.trans h)
            simp [Node.fromOld, hright, hne] at heq
          · simpa [Node.fromOld, hleft, hright] using heq
  exact hsame ▸ hsourceUsed

theorem old_rule_real_disjoint {net : Net} (hvalid : net.valid = true)
    (rule : Rule) (left right : Nat) (end_ : TriageConcrete.End)
    (hold : Node.real end_ ∈ layerEnds (oldLayer net left right))
    (hnew : Node.real end_ ∈ layerEnds (ruleLayer rule net.nextId)) :
    False := by
  have hused := oldLayer_real_used hold
  cases end_ with
  | free name => exact ruleLayer_no_free hnew
  | agent id slot =>
      have hlt := net_used_agent_old hvalid hused
      have hge := ruleLayer_real_fresh hnew
      omega

end TriageBoundary
