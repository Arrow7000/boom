import TriageEquivalence

/-! Residual active pairs for the executable wire-list reducer. -/

namespace TriageResidual
open TriageConcrete TriageRuleModel TriageRules TriageRuleProperties
open TriageBoundary TriagePreservation TriageReduction

theorem Net.kind_of_mem {net : Net}
    (hids : (net.agents.map Prod.fst).Nodup) {id : Nat} {kind : Kind}
    (hmem : (id, kind) ∈ net.agents) : net.kind? id = some kind := by
  have hex : ∃ entry ∈ net.agents, (entry.1 == id) = true :=
    ⟨(id, kind), hmem, by simp⟩
  have hsome := List.find?_isSome.mpr hex
  cases hf : net.agents.find? (fun entry => entry.1 == id) with
  | none => simp [hf] at hsome
  | some entry =>
      have hentry := List.mem_of_find?_eq_some hf
      have heq := List.find?_some hf
      rcases entry with ⟨found, foundKind⟩
      simp only [beq_iff_eq] at heq
      subst found
      have hk := ids_unique hids hentry hmem
      simp [Net.kind?, hf, hk]

theorem Net.replace_retains_kind {net : Net} (hvalid : net.valid = true)
    (rule : Rule) {left right id : Nat} {kind : Kind}
    (hkind : net.kind? id = some kind) (hl : id ≠ left) (hr : id ≠ right) :
    (net.replace rule left right).kind? id = some kind := by
  apply Net.kind_of_mem
  · exact Net.replace_ids_nodup (net.wellFormed_iff.mp (valid_wellFormed hvalid)).1
      (by have hv := hvalid; simp only [Net.valid, Bool.and_eq_true] at hv; exact hv.2) rule left right
  · rw [Net.replace_agents]
    exact List.mem_append_left _ (List.mem_filter.mpr
      ⟨Net.kind_mem hkind, by simp [hl, hr]⟩)

theorem Net.replace_retains_wire (net : Net) (rule : Rule) (left right : Nat)
    {a b : TriageConcrete.End} (hwire : (a, b) ∈ net.wires)
    (ha : belongs left right a = false) (hb : belongs left right b = false) :
    (a, b) ∈ (net.replace rule left right).wires := by
  have hmem : (a, b) ∈ untouched net left right :=
    List.mem_filter.mpr ⟨hwire, by simp [ha, hb]⟩
  change (a, b) ∈ untouched net left right ++ _ ++ _
  exact List.mem_append_left _ (List.mem_append_left _ hmem)

/-- A disjoint active pair remains active after replacement, including when
its auxiliary ports are wired to the pair being replaced. -/
theorem Net.replace_retains_active {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right a b : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    (hactive : net.Active a b)
    (hal : a ≠ left) (har : a ≠ right) (hbl : b ≠ left) (hbr : b ≠ right) :
    (net.replace rule left right).Active a b := by
  rcases hactive with ⟨⟨ak, hak⟩, ⟨bk, hbk⟩, hwire⟩
  have hnext := Net.redexChoice_preserves_valid hvalid hchoice
  refine ⟨⟨ak, Net.replace_retains_kind hvalid rule hak hal har⟩,
    ⟨bk, Net.replace_retains_kind hvalid rule hbk hbl hbr⟩, ?_⟩
  have ha : belongs left right (.agent a 0) = false := by simp [belongs, hal, har]
  have hb : belongs left right (.agent b 0) = false := by simp [belongs, hbl, hbr]
  have hn := Net.wellFormed_nodup (valid_wellFormed hnext)
  rcases neighborIn_sound hwire with hab | hba
  · exact neighborIn_of_mem hn (Net.replace_retains_wire net rule left right hab ha hb)
  · exact neighborIn_of_mem_right hn (Net.replace_retains_wire net rule left right hba hb ha)

theorem rule_kinds_distinct {rule : Rule} (hrule : rule ∈ rules) :
    rule.left ≠ rule.right := by
  have hall : ∀ rule ∈ rules, rule.left ≠ rule.right := by decide
  exact hall rule hrule

theorem selected_rule {rule : Rule} (hrule : rule ∈ rules)
    {first second : Kind} (haccept : accepts rule first second = true) :
    rules.find? (fun candidate => accepts candidate first second) = some rule := by
  have hex : ∃ candidate ∈ rules, accepts candidate first second = true :=
    ⟨rule, hrule, haccept⟩
  have hsome := List.find?_isSome.mpr hex
  cases hf : rules.find? (fun candidate => accepts candidate first second) with
  | none => simp [hf] at hsome
  | some found =>
      have ha : accepts found first second = true := List.find?_some (p := fun candidate => accepts candidate first second) hf
      have heq := unique_rule (List.mem_of_find?_eq_some hf) hrule ha haccept
      exact congrArg some heq

/-- Every applicable active pair is offered by the executable reducer. -/
theorem Net.redexChoice_complete {net : Net} {rule : Rule} {left right : Nat}
    (hrule : rule ∈ rules) (hactive : net.Active left right)
    (hl : net.kind? left = some rule.left) (hr : net.kind? right = some rule.right) :
    (rule, left, right) ∈ net.redexChoices := by
  have hforward := selected_rule hrule
    (show accepts rule rule.left rule.right = true by simp [accepts])
  have hreverse := selected_rule hrule
    (show accepts rule rule.right rule.left = true by simp [accepts])
  have hne := rule_kinds_distinct hrule
  rcases neighborIn_sound hactive.2.2 with hwire | hwire
  · exact List.mem_filterMap.mpr ⟨_, hwire, by
      simp [hl, hr, hforward]⟩
  · exact List.mem_filterMap.mpr ⟨_, hwire, by
      simp [hl, hr, hreverse, hne]⟩

/-- Reducing another disjoint choice preserves this exact oriented choice. -/
theorem Net.replace_retains_choice {net : Net} (hvalid : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) :
    (second, c, d) ∈ (net.replace first a b).redexChoices := by
  rcases Net.redexChoice_sound (valid_wellFormed hvalid) hs with
    ⟨hrule, hactive, hl, hr⟩
  exact Net.redexChoice_complete hrule
    (Net.replace_retains_active hvalid hf hactive hca hcb hda hdb)
    (Net.replace_retains_kind hvalid first hl hca hcb)
    (Net.replace_retains_kind hvalid first hr hda hdb)

/-- Two executable choices either coincide exactly or use four distinct
agent IDs. There are no competing rules or competing orientations. -/
theorem Net.choices_equal_or_disjoint {net : Net} (hvalid : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices) :
    (first = second ∧ a = c ∧ b = d) ∨
      (c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b) := by
  have hwf := valid_wellFormed hvalid
  rcases Net.redexChoice_sound hwf hf with ⟨hfm, hfa, hfl, hfr⟩
  rcases Net.redexChoice_sound hwf hs with ⟨hsm, hsa, hsl, hsr⟩
  by_cases hshare : a = c ∨ a = d ∨ b = c ∨ b = d
  · left
    rcases Net.active_disjoint_or_equal hwf hfa hsa hshare with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hl : first.left = second.left := Option.some.inj (hfl.symm.trans hsl)
      have hr : first.right = second.right := Option.some.inj (hfr.symm.trans hsr)
      have heq := unique_rule hfm hsm
        (show accepts first first.left first.right = true by simp [accepts])
        (show accepts second first.left first.right = true by simp [accepts, hl, hr])
      exact ⟨heq, rfl, rfl⟩
    · have hl : first.left = second.right := Option.some.inj (hfl.symm.trans hsr)
      have hr : first.right = second.left := Option.some.inj (hfr.symm.trans hsl)
      have heq := unique_rule hfm hsm
        (show accepts first first.left first.right = true by simp [accepts])
        (show accepts second first.left first.right = true by simp [accepts, hl, hr])
      have : first.left = first.right := hl.trans (congrArg Rule.right heq).symm
      exact False.elim (rule_kinds_distinct hfm this)
  · right
    simp only [not_or] at hshare
    exact ⟨Ne.symm hshare.1, Ne.symm hshare.2.2.1, Ne.symm hshare.2.1, Ne.symm hshare.2.2.2⟩

/-- Both orders of two distinct executable choices are valid schedules.
Equality of their resulting graphs is the remaining local-diamond obligation. -/
theorem Net.residual_schedules {net : Net} (hvalid : net.valid = true)
    {first second : Rule} {a b c d : Nat}
    (hf : (first, a, b) ∈ net.redexChoices)
    (hs : (second, c, d) ∈ net.redexChoices)
    (hne : (first, a, b) ≠ (second, c, d)) :
    Step (net.replace first a b) ((net.replace first a b).replace second c d) ∧
    Step (net.replace second c d) ((net.replace second c d).replace first a b) := by
  rcases Net.choices_equal_or_disjoint hvalid hf hs with ⟨rfl, rfl, rfl⟩ | hd
  · exact False.elim (hne rfl)
  · rcases hd with ⟨hca, hcb, hda, hdb⟩
    exact ⟨Step.chosen (Net.replace_retains_choice hvalid hf hs hca hcb hda hdb),
      Step.chosen (Net.replace_retains_choice hvalid hs hf
        hca.symm hda.symm hcb.symm hdb.symm)⟩

theorem Net.residual_nextId (net : Net) (first second : Rule) (a b c d : Nat) :
    ((net.replace first a b).replace second c d).nextId =
      ((net.replace second c d).replace first a b).nextId := by
  simp only [Net.replace_nextId]
  omega

end TriageResidual
