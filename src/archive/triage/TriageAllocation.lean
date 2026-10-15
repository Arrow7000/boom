import TriageResidual

/-! The ID permutation relating the two orders of independent allocations. -/

namespace TriageAllocation
open TriageConcrete TriageRuleModel TriageBoundary TriagePreservation
open TriageResidual TriageReduction

def swapBlocks (start first second id : Nat) : Nat :=
  if id < start then id
  else if id < start + first then id + second
  else if id < start + first + second then id - first
  else id

theorem swapBlocks_inverse (start first second id : Nat) :
    swapBlocks start second first (swapBlocks start first second id) = id := by
  unfold swapBlocks
  split_ifs <;> omega

def blockSwap (start first second : Nat) : Nat ≃ Nat where
  toFun := swapBlocks start first second
  invFun := swapBlocks start second first
  left_inv := swapBlocks_inverse start first second
  right_inv := swapBlocks_inverse start second first

@[simp] theorem blockSwap_old {start first second id : Nat} (h : id < start) :
    blockSwap start first second id = id := by simp [blockSwap, swapBlocks, h]

theorem blockSwap_first {start first second index : Nat} (h : index < first) :
    blockSwap start first second (start + index) = start + second + index := by
  change swapBlocks start first second (start + index) = _
  unfold swapBlocks
  split_ifs <;> omega

theorem blockSwap_second {start first second index : Nat} (h : index < second) :
    blockSwap start first second (start + first + index) = start + index := by
  change swapBlocks start first second (start + first + index) = _
  unfold swapBlocks
  split_ifs <;> omega

def allocated (start : Nat) (kinds : List Kind) : List (Nat × Kind) :=
  kinds.zipIdx.map fun (kind, index) => (start + index, kind)

theorem allocated_bounds {start id : Nat} {kinds : List Kind} {kind : Kind}
    (hmem : (id, kind) ∈ allocated start kinds) :
    start ≤ id ∧ id < start + kinds.length := by
  rcases List.mem_map.mp hmem with ⟨⟨foundKind, index⟩, hi, heq⟩
  have hib := (List.mem_zipIdx' hi).1
  have hid := (Prod.mk.inj heq).1
  simp only at hid
  omega

theorem allocated_filter {start left right : Nat} (kinds : List Kind)
    (hl : left < start) (hr : right < start) :
    (allocated start kinds).filter (fun entry => entry.1 != left && entry.1 != right) =
      allocated start kinds := by
  apply List.filter_eq_self.mpr
  intro entry hmem
  have hb := allocated_bounds hmem
  have h1 : entry.1 ≠ left := by omega
  have h2 : entry.1 ≠ right := by omega
  simp [h1, h2]

theorem map_allocated_first (start second : Nat) (kinds : List Kind) :
    (allocated start kinds).map (fun entry =>
      (blockSwap start kinds.length second entry.1, entry.2)) =
      allocated (start + second) kinds := by
  simp only [allocated, List.map_map]
  apply List.map_congr_left
  intro entry hmem
  rcases entry with ⟨kind, index⟩
  have hi := (List.mem_zipIdx' hmem).1
  simp only [Function.comp_apply, blockSwap_first hi]

theorem map_allocated_second (start first : Nat) (kinds : List Kind) :
    (allocated (start + first) kinds).map (fun entry =>
      (blockSwap start first kinds.length entry.1, entry.2)) =
      allocated start kinds := by
  simp only [allocated, List.map_map]
  apply List.map_congr_left
  intro entry hmem
  rcases entry with ⟨kind, index⟩
  have hi := (List.mem_zipIdx' hmem).1
  simp only [Function.comp_apply, blockSwap_second hi]

theorem active_id_bound {net : Net} (hvalid : net.valid = true)
    {id : Nat} {kind : Kind} (hk : net.kind? id = some kind) : id < net.nextId := by
  have hf : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
    have hv := hvalid
    simp only [Net.valid, Bool.and_eq_true] at hv
    simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using hv.2
  exact hf (id, kind) (Net.kind_mem hk)

theorem double_replace_agents {net : Net} (hvalid : net.valid = true)
    (first second : Rule) {a b c d : Nat}
    (hc : ∃ kind, net.kind? c = some kind)
    (hd : ∃ kind, net.kind? d = some kind) :
    ((net.replace first a b).replace second c d).agents =
      (net.agents.filter fun entry =>
        (entry.1 != a && entry.1 != b) && (entry.1 != c && entry.1 != d)) ++
      allocated net.nextId first.agents ++
      allocated (net.nextId + first.agents.length) second.agents := by
  rcases hc with ⟨ck, hck⟩
  rcases hd with ⟨dk, hdk⟩
  have hcBound := active_id_bound hvalid hck
  have hdBound := active_id_bound hvalid hdk
  simp only [Net.replace_agents, Net.replace_nextId, List.filter_append]
  change ((net.agents.filter _).filter _ ++ (allocated net.nextId first.agents).filter _) ++ _ = _
  rw [allocated_filter first.agents hcBound hdBound, List.filter_filter]
  congr 2
  apply List.filter_congr
  intro entry _
  simp [Bool.and_comm]

/-- The complete surviving and newly allocated agent lists agree up to the
explicit block permutation, independently of their wire connectivity. -/
theorem double_replace_agents_perm {net : Net} (hvalid : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices) :
    (((net.replace first a b).replace second c d).agents.map (fun entry =>
      (blockSwap net.nextId first.agents.length second.agents.length entry.1, entry.2))).Perm
      ((net.replace second c d).replace first a b).agents := by
  rcases Net.redexChoice_sound (valid_wellFormed hvalid) hf with ⟨_, hfa, _, _⟩
  rcases Net.redexChoice_sound (valid_wellFormed hvalid) hs with ⟨_, hsa, _, _⟩
  rw [double_replace_agents hvalid first second hsa.1 hsa.2.1,
    double_replace_agents hvalid second first hfa.1 hfa.2.1]
  rw [List.map_append, List.map_append, map_allocated_first, map_allocated_second]
  have hold :
      ((net.agents.filter fun entry =>
        (entry.1 != a && entry.1 != b) && (entry.1 != c && entry.1 != d)).map
        (fun entry => (blockSwap net.nextId first.agents.length second.agents.length
          entry.1, entry.2))) =
      (net.agents.filter fun entry =>
        (entry.1 != c && entry.1 != d) && (entry.1 != a && entry.1 != b)) := by
    rw [List.map_congr_left (g := fun entry => entry)]
    · rw [List.map_id']
      apply List.filter_congr
      intro entry _
      exact Bool.and_comm _ _
    · intro entry hmem
      have hentry := (List.mem_filter.mp hmem).1
      have hfresh : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
        have hv := hvalid
        simp only [Net.valid, Bool.and_eq_true] at hv
        simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using hv.2
      simp only [blockSwap_old (hfresh entry hentry)]
  rw [hold, List.append_assoc, List.append_assoc]
  exact List.Perm.append_left _ (List.perm_append_comm ..)

theorem kinds_of_agents_perm {first second : Net} {rename : Nat ≃ Nat}
    (hf : (first.agents.map Prod.fst).Nodup)
    (hs : (second.agents.map Prod.fst).Nodup)
    (hp : (first.agents.map (fun entry => (rename entry.1, entry.2))).Perm
      second.agents) (id : Nat) : second.kind? (rename id) = first.kind? id := by
  have hforward : ∀ kind, first.kind? id = some kind →
      second.kind? (rename id) = some kind := by
    intro kind hk
    apply Net.kind_of_mem hs
    exact hp.mem_iff.mp (List.mem_map.mpr ⟨(id, kind), Net.kind_mem hk, rfl⟩)
  have hbackward : ∀ kind, second.kind? (rename id) = some kind →
      first.kind? id = some kind := by
    intro kind hk
    have hm := hp.mem_iff.mpr (Net.kind_mem hk)
    rcases List.mem_map.mp hm with ⟨⟨found, foundKind⟩, hmem, heq⟩
    have he := Prod.mk.inj heq
    have hid : found = id := rename.injective he.1
    subst found
    have hkEq : foundKind = kind := he.2
    subst foundKind
    exact Net.kind_of_mem hf hmem
  cases hk : first.kind? id with
  | some kind => exact hforward kind hk
  | none =>
      cases hs : second.kind? (rename id) with
      | none => rfl
      | some kind => have := hbackward kind hs; rw [hk] at this; cases this

theorem double_replace_kinds {net : Net} (hvalid : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices)
    (hne : (first, a, b) ≠ (second, c, d)) (id : Nat) :
    ((net.replace second c d).replace first a b).kind?
      (blockSwap net.nextId first.agents.length second.agents.length id) =
    ((net.replace first a b).replace second c d).kind? id := by
  rcases Net.residual_schedules hvalid hf hs hne with ⟨hfs, hsf⟩
  have hfv := hfs.preserves_valid (Net.redexChoice_preserves_valid hvalid hf)
  have hsv := hsf.preserves_valid (Net.redexChoice_preserves_valid hvalid hs)
  exact kinds_of_agents_perm
    ((Net.wellFormed_iff _).mp (valid_wellFormed hfv)).1
    ((Net.wellFormed_iff _).mp (valid_wellFormed hsv)).1
    (double_replace_agents_perm hvalid hf hs) id

end TriageAllocation
