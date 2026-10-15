/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriagePortContraction

/-! Wire connectivity commutes for two independent executable choices. -/

namespace TriageWireCommutation
open TriageRuleModel (Rule)
open TriageConcrete TriageBoundary TriagePreservation TriageReduction TriageResidual
open TriageAllocation TriageLocalSemantics TriagePortContraction TriageEquivalence TriageContraction

def portRename (rename : Nat ≃ Nat) : End ≃ End where
  toFun := renameEnd rename
  invFun := renameEnd rename.symm
  left_inv := renameEnd_symm rename
  right_inv := renameEnd_apply_symm rename

theorem rule_agent_bound {rule : Rule} (hr : rule.wellFormed = true)
    {index slot : Nat} (hm : TriageRuleModel.End.agent index slot ∈ rule.used) :
    index < rule.agents.length := by
  have he := ((Rule.wellFormed_iff rule).mp hr).2.1 _ hm
  simp only [Rule.expected, List.mem_append] at he
  rcases he with (he | he) | he
  · simp at he
  · simp at he
  · rcases List.mem_flatMap.mp he with ⟨⟨kind, found⟩, hzip, hport⟩
    rcases List.mem_map.mp hport with ⟨_, _, heq⟩
    have hid := (TriageRuleModel.End.agent.inj heq).1
    have hb := (List.mem_zipIdx' hzip).1
    simp only at hid
    omega

theorem wiring_nodup {rule : Rule} (hr : rule.wellFormed = true)
    {fresh left right : Nat} (hl : left < fresh) (hright : right < fresh) (hne : left ≠ right) :
    (wireEnds (wiring rule fresh left right)).Nodup := by
  have hh := ruleLayer_nodup hr fresh
  rw [← mapped_wiring hr hl hright hne, mapped, layerEnds, layerEnds_map] at hh
  exact List.Nodup.of_map _ hh

theorem wiring_irreflexive {rule : Rule} (hr : rule.wellFormed = true)
    {fresh left right : Nat} (hl : left < fresh) (hright : right < fresh) (hne : left ≠ right) :
    ∀ a, ¬Link (wiring rule fresh left right) a a := by
  intro a hh
  exact neighborIn_irreflexive (wiring_nodup hr hl hright hne)
    ((link_neighbor (wiring_nodup hr hl hright hne) a a).mp hh)

theorem wiring_outside {rule : Rule} {fresh left right otherLeft otherRight : Nat}
    (hol : otherLeft < fresh) (hor : otherRight < fresh)
    (hll : left ≠ otherLeft) (hlr : left ≠ otherRight)
    (hrl : right ≠ otherLeft) (hrr : right ≠ otherRight) :
    ∀ a b, Link (wiring rule fresh left right) a b →
      ¬Removed otherLeft otherRight a ∧ ¬Removed otherLeft otherRight b := by
  have hp : ∀ end_, ¬Removed otherLeft otherRight (port fresh left right end_) := by
    intro end_
    cases end_ with
    | agent index slot =>
        have h1 : fresh + index ≠ otherLeft := by omega
        have h2 : fresh + index ≠ otherRight := by omega
        simp [port, Removed, belongs, h1, h2]
    | iface side slot =>
        by_cases hs : side = 0 <;> simp [port, hs, Removed, belongs, hll, hlr, hrl, hrr]
  intro a b hh
  rcases hh with hab | hba
  · rcases List.mem_map.mp hab with ⟨⟨x, y⟩, _, heq⟩
    cases heq
    exact ⟨hp x, hp y⟩
  · rcases List.mem_map.mp hba with ⟨⟨x, y⟩, _, heq⟩
    cases heq
    exact ⟨hp y, hp x⟩

theorem wiring_rename {rule : Rule} (hr : rule.wellFormed = true)
    (rename : Nat ≃ Nat) (fresh next left right : Nat)
    (hl : rename left = left) (hright : rename right = right)
    (hnew : ∀ index, index < rule.agents.length → rename (fresh + index) = next + index) :
    mapped (renameEnd rename) (wiring rule fresh left right) = wiring rule next left right := by
  have hp : ∀ end_ ∈ rule.used,
      renameEnd rename (port fresh left right end_) = port next left right end_ := by
    intro end_ hm
    cases end_ with
    | agent index slot => simp [port, renameEnd, hnew index (rule_agent_bound hr hm)]
    | iface side slot => by_cases hs : side = 0 <;> simp [port, renameEnd, hs, hl, hright]
  simp only [mapped, wiring, List.map_map]
  apply List.map_congr_left
  intro wire hw
  rcases wire with ⟨a, b⟩
  simp only [Function.comp_apply, hp a (List.mem_flatMap.mpr ⟨(a, b), hw, by simp⟩),
    hp b (List.mem_flatMap.mpr ⟨(a, b), hw, by simp⟩)]

theorem link_rename {rename : Nat ≃ Nat} {first second : List Wire}
    (hm : mapped (renameEnd rename) first = second) (a b : End) :
    Link second (renameEnd rename a) (renameEnd rename b) ↔ Link first a b := by
  rw [← hm]
  change (_ ∨ _) ↔ _
  rw [mapped_link]
  constructor
  · rintro ⟨x, y, hx, hy, he⟩
    have hxa := renameEnd_injective rename hx
    have hyb := renameEnd_injective rename hy
    simpa [← hxa, ← hyb] using he
  · intro he
    exact ⟨a, b, rfl, rfl, he⟩

theorem old_wires_rename {net : Net} (hv : net.valid = true) (first second : Nat) :
    mapped (renameEnd (blockSwap net.nextId first second)) net.wires = net.wires := by
  have hp : ∀ end_ ∈ net.used, renameEnd (blockSwap net.nextId first second) end_ = end_ := by
    intro end_ hm
    cases end_ with
    | free name => rfl
    | agent id slot => simp [renameEnd, blockSwap_old (net_used_agent_old hv hm)]
  unfold mapped
  rw [List.map_congr_left (g := fun wire => wire)]
  · exact List.map_id' _
  · intro wire hw
    rcases wire with ⟨a, b⟩
    simp only [hp a (left_mem_wireEnds hw), hp b (right_mem_wireEnds hw)]

theorem removed_rename (rename : Nat ≃ Nat) {left right : Nat}
    (hl : rename left = left) (hr : rename right = right) (end_ : End) :
    Removed left right (renameEnd rename end_) ↔ Removed left right end_ := by
  cases end_ with
  | free name => rfl
  | agent id slot =>
      have h1 : rename id = left ↔ id = left := by
        conv_lhs => rw [← hl]
        exact rename.injective.eq_iff
      have h2 : rename id = right ↔ id = right := by
        conv_lhs => rw [← hr]
        exact rename.injective.eq_iff
      simp [Removed, belongs, renameEnd, h1, h2]

theorem double_link {net : Net} (hv : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ (net.replace first a b).redexChoices) (x y : End) :
    Link ((net.replace first a b).replace second c d).wires x y ↔
      Contract (fun s t =>
        Contract (fun p q => Link net.wires p q ∨ Link (wiring first net.nextId a b) p q)
          (Removed a b) s t ∨ Link (wiring second (net.nextId + first.agents.length) c d) s t)
        (Removed c d) x y := by
  have hvf := Net.redexChoice_preserves_valid hv hf
  have hvfs := Net.redexChoice_preserves_valid hvf hs
  rw [link_neighbor (Net.wellFormed_nodup (valid_wellFormed hvfs)),
    ← Net.neighbor, replace_iff_port_contract hvf hs]
  have hrel : Link (net.replace first a b).wires =
      Contract (fun p q => Link net.wires p q ∨ Link (wiring first net.nextId a b) p q) (Removed a b) := by
    funext p q
    apply propext
    rw [link_neighbor (Net.wellFormed_nodup (valid_wellFormed hvf)), ← Net.neighbor,
      replace_iff_port_contract hv hf]
  rw [hrel, Net.replace_nextId]

/-- The two orders have exactly the same undirected wires after swapping
the allocation blocks, even when auxiliary wires connect their boundaries. -/
theorem double_wires {net : Net} (hv : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices)
    (hne : (first, a, b) ≠ (second, c, d)) (x y : End) :
    let rename := blockSwap net.nextId first.agents.length second.agents.length
    Link ((net.replace second c d).replace first a b).wires (renameEnd rename x) (renameEnd rename y) ↔
      Link ((net.replace first a b).replace second c d).wires x y := by
  dsimp only
  have hwf := valid_wellFormed hv
  rcases Net.redexChoice_sound hwf hf with ⟨hfm, hfa, hfl, hfr⟩
  rcases Net.redexChoice_sound hwf hs with ⟨hsm, hsa, hsl, hsr⟩
  have hfw := exported_rule_wellFormed hfm
  have hsw := exported_rule_wellFormed hsm
  have hab := active_ids_ne hwf hfa
  have hcd := active_ids_ne hwf hsa
  have habound := active_id_bound hv hfl
  have hbbound := active_id_bound hv hfr
  have hcbound := active_id_bound hv hsl
  have hdbound := active_id_bound hv hsr
  rcases Net.choices_equal_or_disjoint hv hf hs with ⟨rfl, rfl, rfl⟩ | hd
  · exact False.elim (hne rfl)
  rcases hd with ⟨hca, hcb, hda, hdb⟩
  have hresB := Net.replace_retains_choice hv hf hs hca hcb hda hdb
  have hresA := Net.replace_retains_choice hv hs hf hca.symm hda.symm hcb.symm hdb.symm
  let rename := blockSwap net.nextId first.agents.length second.agents.length
  have hfixA : rename a = a := blockSwap_old habound
  have hfixB : rename b = b := blockSwap_old hbbound
  have hfixC : rename c = c := blockSwap_old hcbound
  have hfixD : rename d = d := blockSwap_old hdbound
  have hmapA : mapped (renameEnd rename) (wiring first net.nextId a b) =
      wiring first (net.nextId + second.agents.length) a b :=
    wiring_rename hfw rename _ _ _ _ hfixA hfixB (fun _ hi => blockSwap_first hi)
  have hmapB : mapped (renameEnd rename) (wiring second (net.nextId + first.agents.length) c d) =
      wiring second net.nextId c d :=
    wiring_rename hsw rename _ _ _ _ hfixC hfixD (fun _ hi => blockSwap_second hi)
  have hmapOld := old_wires_rename hv first.agents.length second.agents.length
  have hpredA := removed_rename rename hfixA hfixB
  have hpredB := removed_rename rename hfixC hfixD
  have hfirstB : ∀ p q,
      Contract (fun s t => Link net.wires s t ∨ Link (wiring second net.nextId c d) s t)
        (Removed c d) (renameEnd rename p) (renameEnd rename q) ↔
      Contract (fun s t => Link net.wires s t ∨ Link (wiring second (net.nextId + first.agents.length) c d) s t)
        (Removed c d) p q := by
    intro p q
    apply contract_equiv (portRename rename)
    · intro s t
      dsimp only [portRename, Equiv.coe_fn_mk]
      rw [link_rename hmapOld, link_rename hmapB]
    · exact hpredB
  rw [double_link hv hs hresA, double_link hv hf hresB]
  have hrename :
      Contract (fun s t =>
        Contract (fun p q => Link net.wires p q ∨ Link (wiring second net.nextId c d) p q)
          (Removed c d) s t ∨ Link (wiring first (net.nextId + second.agents.length) a b) s t)
        (Removed a b) (renameEnd rename x) (renameEnd rename y) ↔
      Contract (fun s t =>
        Contract (fun p q => Link net.wires p q ∨ Link (wiring second (net.nextId + first.agents.length) c d) p q)
          (Removed c d) s t ∨ Link (wiring first net.nextId a b) s t)
        (Removed a b) x y := by
    apply contract_equiv (portRename rename)
    · intro s t
      dsimp only [portRename, Equiv.coe_fn_mk]
      rw [hfirstB, link_rename hmapA]
    · exact hpredA
  apply hrename.trans
  apply Iff.symm
  apply replacement_commute
  · exact wiring_outside hcbound hdbound hca.symm hda.symm hcb.symm hdb.symm
  · exact wiring_outside (by omega : a < net.nextId + first.agents.length)
      (by omega : b < net.nextId + first.agents.length) hca hcb hda hdb
  · exact wiring_irreflexive hfw habound hbbound hab
  · exact wiring_irreflexive hsw (by omega) (by omega) hcd

/-- This closes the executable local diamond for independent choices. -/
theorem double_iso {net : Net} (hv : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices)
    (hne : (first, a, b) ≠ (second, c, d)) :
    Iso (blockSwap net.nextId first.agents.length second.agents.length)
      ((net.replace first a b).replace second c d)
      ((net.replace second c d).replace first a b) := by
  have hfValid := Net.redexChoice_preserves_valid hv hf
  have hsValid := Net.redexChoice_preserves_valid hv hs
  rcases Net.residual_schedules hv hf hs hne with ⟨hfs, hsf⟩
  have hfsN := Net.wellFormed_nodup (valid_wellFormed (hfs.preserves_valid hfValid))
  have hsfN := Net.wellFormed_nodup (valid_wellFormed (hsf.preserves_valid hsValid))
  refine ⟨double_replace_kinds hv hf hs hne, ?_⟩
  intro end_
  let rename := blockSwap net.nextId first.agents.length second.agents.length
  cases hn : ((net.replace first a b).replace second c d).neighbor end_ with
  | some target =>
      have hlink := (link_neighbor hfsN end_ target).mpr hn
      have hnext := (double_wires hv hf hs hne end_ target).mpr hlink
      exact (link_neighbor hsfN _ _).mp hnext
  | none =>
      cases hm : ((net.replace second c d).replace first a b).neighbor (renameEnd rename end_) with
      | none => rfl
      | some target =>
          let before := renameEnd rename.symm target
          have htarget : renameEnd rename before = target := renameEnd_apply_symm rename target
          have hlink := (link_neighbor hsfN _ _).mpr hm
          rw [← htarget] at hlink
          have hbefore := (double_wires hv hf hs hne end_ before).mp hlink
          have hbad := (link_neighbor hfsN _ _).mp hbefore
          change ((net.replace first a b).replace second c d).neighbor end_ = some before at hbad
          rw [hn] at hbad
          cases hbad

end TriageWireCommutation
