/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageWireCommutation

/-!
Executable reduction respects isomorphisms that have equal allocation
counters and fix the unused suffix of IDs. The allocation-block swap in
the local diamond has precisely this property.
-/

namespace TriageEquivariance
open TriageRuleModel (Rule Kind)
open TriageConcrete TriageBoundary TriagePreservation TriageReduction TriageResidual
open TriageAllocation TriageLocalSemantics TriagePortContraction TriageEquivalence
open TriageWireCommutation TriageContraction

structure AlignedIso (rename : Nat ≃ Nat) (first second : Net) : Prop where
  iso : Iso rename first second
  counter : first.nextId = second.nextId
  future : ∀ id, first.nextId ≤ id → rename id = id

def Aligned (first second : Net) : Prop := ∃ rename, AlignedIso rename first second

theorem AlignedIso.refl (net : Net) : AlignedIso (Equiv.refl Nat) net net :=
  ⟨Iso.refl net, rfl, fun _ _ => rfl⟩

theorem AlignedIso.symm {rename : Nat ≃ Nat} {first second : Net}
    (h : AlignedIso rename first second) : AlignedIso rename.symm second first := by
  refine ⟨h.iso.symm, h.counter.symm, ?_⟩
  intro id hb
  have hf := h.future id (by rw [h.counter]; exact hb)
  have hi := congrArg rename.symm hf
  simpa using hi.symm

theorem AlignedIso.trans {f g : Nat ≃ Nat} {first second third : Net}
    (hf : AlignedIso f first second) (hg : AlignedIso g second third) :
    AlignedIso (f.trans g) first third := by
  refine ⟨hf.iso.trans hg.iso, hf.counter.trans hg.counter, ?_⟩
  intro id hb
  change g (f id) = id
  rw [hf.future id hb, hg.future id (by rw [← hf.counter]; exact hb)]

theorem Aligned.refl (net : Net) : Aligned net net := ⟨_, AlignedIso.refl net⟩
theorem Aligned.symm {first second : Net} (h : Aligned first second) : Aligned second first := by
  rcases h with ⟨r, h⟩; exact ⟨r.symm, h.symm⟩
theorem Aligned.trans {first second third : Net} (hf : Aligned first second) (hs : Aligned second third) :
    Aligned first third := by
  rcases hf with ⟨f, hf⟩; rcases hs with ⟨g, hg⟩; exact ⟨f.trans g, hf.trans hg⟩
theorem Aligned.equivalent {first second : Net} (h : Aligned first second) : Equivalent first second := by
  rcases h with ⟨r, h⟩; exact ⟨r, h.iso⟩

theorem Iso.link {rename : Nat ≃ Nat} {first second : Net}
    (hi : Iso rename first second) (hf : first.wellFormed = true) (hs : second.wellFormed = true)
    (a b : End) : Link second.wires (renameEnd rename a) (renameEnd rename b) ↔ Link first.wires a b := by
  rw [link_neighbor (second.wellFormed_nodup hs), link_neighbor (first.wellFormed_nodup hf)]
  change second.neighbor (renameEnd rename a) = _ ↔ first.neighbor a = _
  rw [hi.neighbors]
  cases hn : first.neighbor a with
  | none => simp
  | some end_ =>
      simp only [Option.map_some, Option.some.injEq]
      exact ⟨fun h => renameEnd_injective rename h, congrArg (renameEnd rename)⟩

theorem Iso.agent_mem {rename : Nat ≃ Nat} {first second : Net}
    (hi : Iso rename first second) (hf : first.wellFormed = true) (hs : second.wellFormed = true)
    (id : Nat) (kind : Kind) : (rename id, kind) ∈ second.agents ↔ (id, kind) ∈ first.agents := by
  constructor
  · intro hm
    have hk := Net.kind_of_mem (second.wellFormed_iff.mp hs).1 hm
    rw [hi.kinds] at hk
    exact Net.kind_mem hk
  · intro hm
    have hk := Net.kind_of_mem (first.wellFormed_iff.mp hf).1 hm
    exact Net.kind_mem (by rw [hi.kinds, hk])

theorem wiring_map {rule : Rule} (hr : rule.wellFormed = true)
    (rename : Nat ≃ Nat) (fresh next left right : Nat)
    (hnew : ∀ index, index < rule.agents.length → rename (fresh + index) = next + index) :
    mapped (renameEnd rename) (wiring rule fresh left right) =
      wiring rule next (rename left) (rename right) := by
  have hp : ∀ end_ ∈ rule.used, renameEnd rename (port fresh left right end_) =
      port next (rename left) (rename right) end_ := by
    intro end_ hm
    cases end_ with
    | agent index slot => simp [port, renameEnd, hnew index (rule_agent_bound hr hm)]
    | iface side slot => by_cases hh : side = 0 <;> simp [port, renameEnd, hh]
  simp only [mapped, wiring, List.map_map]
  apply List.map_congr_left
  intro wire hw
  rcases wire with ⟨a, b⟩
  simp only [Function.comp_apply, hp a (List.mem_flatMap.mpr ⟨(a, b), hw, by simp⟩),
    hp b (List.mem_flatMap.mpr ⟨(a, b), hw, by simp⟩)]

theorem removed_map (rename : Nat ≃ Nat) (left right : Nat) (end_ : End) :
    Removed (rename left) (rename right) (renameEnd rename end_) ↔ Removed left right end_ := by
  cases end_ <;> simp [Removed, belongs, renameEnd]

theorem AlignedIso.choice {rename : Nat ≃ Nat} {first second : Net}
    (hi : AlignedIso rename first second) (hv : first.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ first.redexChoices) :
    (rule, rename left, rename right) ∈ second.redexChoices := by
  rcases Net.redexChoice_sound (valid_wellFormed hv) hc with ⟨hr, ha, hl, hright⟩
  exact Net.redexChoice_complete hr ((hi.iso.active left right).mp ha)
    (by rw [hi.iso.kinds, hl]) (by rw [hi.iso.kinds, hright])

theorem AlignedIso.replace {rename : Nat ≃ Nat} {first second : Net}
    (hi : AlignedIso rename first second) (hf : first.valid = true) (hs : second.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ first.redexChoices) :
    AlignedIso rename (first.replace rule left right) (second.replace rule (rename left) (rename right)) := by
  have hc2 := hi.choice hf hc
  have hfv := Net.redexChoice_preserves_valid hf hc
  have hsv := Net.redexChoice_preserves_valid hs hc2
  have hfw := valid_wellFormed hf
  have hsw := valid_wellFormed hs
  have hfnew := valid_wellFormed hfv
  have hsnew := valid_wellFormed hsv
  have hr := exported_rule_wellFormed (Net.redexChoice_sound hfw hc).1
  have hwire := wiring_map hr rename first.nextId second.nextId left right (fun index _ => by
    rw [← hi.counter]
    exact hi.future _ (by omega))
  have hnewmem : ∀ id kind, (rename id, kind) ∈ allocated second.nextId rule.agents ↔
      (id, kind) ∈ allocated first.nextId rule.agents := by
    have hmap : (allocated first.nextId rule.agents).map (fun entry => (rename entry.1, entry.2)) =
        allocated second.nextId rule.agents := by
      simp only [allocated, List.map_map]
      apply List.map_congr_left
      intro entry _
      simp only [Function.comp_apply]
      rw [hi.future (first.nextId + entry.2) (by omega), hi.counter]
    intro id kind
    rw [← hmap, List.mem_map]
    constructor
    · rintro ⟨⟨found, foundKind⟩, hm, heq⟩
      have he := Prod.mk.inj heq
      have hid : found = id := rename.injective he.1
      have hk : foundKind = kind := he.2
      subst found; subst foundKind
      exact hm
    · intro hm; exact ⟨(id, kind), hm, rfl⟩
  have hmem : ∀ id kind,
      (rename id, kind) ∈ (second.replace rule (rename left) (rename right)).agents ↔
      (id, kind) ∈ (first.replace rule left right).agents := by
    intro id kind
    simp only [Net.replace_agents, List.mem_append, List.mem_filter, Bool.and_eq_true,
      bne_iff_ne]
    change ((_ ∧ _) ∨ (rename id, kind) ∈ allocated second.nextId rule.agents) ↔
      ((_ ∧ _) ∨ (id, kind) ∈ allocated first.nextId rule.agents)
    rw [hnewmem, Iso.agent_mem hi.iso hfw hsw]
    simp
  have hkind : ∀ id, (second.replace rule (rename left) (rename right)).kind? (rename id) =
      (first.replace rule left right).kind? id := by
    intro id
    have hsome : ∀ kind,
        (second.replace rule (rename left) (rename right)).kind? (rename id) = some kind ↔
          (first.replace rule left right).kind? id = some kind := by
      intro kind
      constructor
      · intro hk
        exact Net.kind_of_mem ((Net.wellFormed_iff _).mp hfnew).1 ((hmem id kind).mp (Net.kind_mem hk))
      · intro hk
        exact Net.kind_of_mem ((Net.wellFormed_iff _).mp hsnew).1 ((hmem id kind).mpr (Net.kind_mem hk))
    cases hk : (first.replace rule left right).kind? id with
    | some kind => exact (hsome kind).mpr hk
    | none =>
        cases ht : (second.replace rule (rename left) (rename right)).kind? (rename id) with
        | none => rfl
        | some kind => have := (hsome kind).mp ht; rw [hk] at this; cases this
  have hlink : ∀ a b,
      Link (second.replace rule (rename left) (rename right)).wires (renameEnd rename a) (renameEnd rename b) ↔
      Link (first.replace rule left right).wires a b := by
    intro a b
    rw [link_neighbor (Net.wellFormed_nodup hsnew), ← Net.neighbor, replace_iff_port_contract hs hc2,
      link_neighbor (Net.wellFormed_nodup hfnew), ← Net.neighbor, replace_iff_port_contract hf hc]
    apply contract_equiv (portRename rename)
    · intro x y
      dsimp only [portRename, Equiv.coe_fn_mk]
      rw [Iso.link hi.iso hfw hsw, link_rename hwire]
    · exact removed_map rename left right
  refine ⟨⟨hkind, ?_⟩, by simp only [Net.replace_nextId, hi.counter], ?_⟩
  · intro end_
    cases hn : (first.replace rule left right).neighbor end_ with
    | some target =>
        exact (link_neighbor (Net.wellFormed_nodup hsnew) _ _).mp
          ((hlink end_ target).mpr ((link_neighbor (Net.wellFormed_nodup hfnew) _ _).mpr hn))
    | none =>
        cases ht : (second.replace rule (rename left) (rename right)).neighbor (renameEnd rename end_) with
        | none => rfl
        | some target =>
            have htarget : renameEnd rename (renameEnd rename.symm target) = target := renameEnd_apply_symm rename target
            have hh := (link_neighbor (Net.wellFormed_nodup hsnew) _ _).mpr ht
            rw [← htarget] at hh
            have hb := (link_neighbor (Net.wellFormed_nodup hfnew) _ _).mp ((hlink _ _).mp hh)
            change (first.replace rule left right).neighbor _ = some _ at hb
            rw [hn] at hb
            cases hb
  · intro id hb
    exact hi.future id (by rw [Net.replace_nextId] at hb; omega)

theorem Aligned.transport {first second next : Net} (hi : Aligned first second)
    (hf : first.valid = true) (hs : second.valid = true) (hstep : Step first next) :
    ∃ target, Step second target ∧ Aligned next target := by
  rcases hi with ⟨rename, hi⟩
  cases hstep with
  | @chosen rule left right hc =>
      exact ⟨second.replace rule (rename left) (rename right), Step.chosen (hi.choice hf hc),
        rename, hi.replace hf hs hc⟩

theorem double_aligned {net : Net} (hv : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices) (hs : (second, c, d) ∈ net.redexChoices)
    (hne : (first, a, b) ≠ (second, c, d)) :
    Aligned ((net.replace first a b).replace second c d) ((net.replace second c d).replace first a b) := by
  refine ⟨blockSwap net.nextId first.agents.length second.agents.length,
    double_iso hv hf hs hne, Net.residual_nextId .., ?_⟩
  intro id hb
  simp only [Net.replace_nextId] at hb
  change swapBlocks net.nextId first.agents.length second.agents.length id = id
  unfold swapBlocks
  split_ifs <;> omega

end TriageEquivariance
