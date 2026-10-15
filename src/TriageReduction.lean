import TriagePreservation

/-!
The executable reducer only offers applicable active pairs. Universal graph
preservation therefore applies to every redex choice, including arbitrary
orders of concrete reduction.
-/

namespace TriageReduction
open TriageConcrete TriageBoundary TriagePreservation TriageRuleProperties TriageRules

theorem Net.redexChoice_sound {net : Net} (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} {left right : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices) :
    rule ∈ rules ∧ net.Active left right ∧
      net.kind? left = some rule.left ∧
      net.kind? right = some rule.right := by
  rcases List.mem_filterMap.mp hchoice with ⟨⟨a, b⟩, hwire, hout⟩
  cases a with
  | free name => simp at hout
  | agent first firstSlot =>
      cases firstSlot with
      | succ slot => simp at hout
      | zero =>
          cases b with
          | free name => simp at hout
          | agent second secondSlot =>
              cases secondSlot with
              | succ slot => simp at hout
              | zero =>
                  cases hk1 : net.kind? first with
                  | none => simp [hk1] at hout
                  | some firstKind =>
                      cases hk2 : net.kind? second with
                      | none => simp [hk1, hk2] at hout
                      | some secondKind =>
                          cases hf : rules.find? (fun candidate =>
                            accepts candidate firstKind secondKind) with
                          | none => simp [hk1, hk2, hf] at hout
                          | some candidate =>
                              have hmem := List.mem_of_find?_eq_some hf
                              have haccept := List.find?_some hf
                              simp only [accepts, decide_eq_true_eq] at haccept
                              by_cases hsame : candidate.left = firstKind
                              · have heq : (candidate, first, second) =
                                    (rule, left, right) := by
                                  simpa [hk1, hk2, hf, hsame] using hout
                                cases heq
                                have hright : rule.right = secondKind := by
                                  rcases haccept with ⟨_, hr⟩ | ⟨hl, hr⟩
                                  · exact hr
                                  · exact hr.trans (hsame.symm.trans hl)
                                refine ⟨hmem, ?_, ?_, ?_⟩
                                · exact ⟨⟨firstKind, hk1⟩, ⟨secondKind, hk2⟩,
                                    neighborIn_of_mem (net.wellFormed_nodup hwf) hwire⟩
                                · simpa only [hsame] using hk1
                                · simpa only [hright] using hk2
                              · have heq : (candidate, second, first) =
                                    (rule, left, right) := by
                                  simpa [hk1, hk2, hf, hsame] using hout
                                cases heq
                                rcases haccept with ⟨hl, _⟩ | ⟨hl, hr⟩
                                · exact False.elim (hsame hl)
                                · refine ⟨hmem, ?_, ?_, ?_⟩
                                  · exact ⟨⟨secondKind, hk2⟩, ⟨firstKind, hk1⟩,
                                      neighborIn_of_mem_right (net.wellFormed_nodup hwf) hwire⟩
                                  · simpa only [hl] using hk2
                                  · simpa only [hr] using hk1

theorem Net.redexChoice_preserves_valid {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} {left right : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices) :
    (net.replace rule left right).valid = true := by
  rcases Net.redexChoice_sound (valid_wellFormed hvalid) hchoice with
    ⟨hmem, hactive, hleft, hright⟩
  have hwell : rule.wellFormed = true := by
    have hall : ∀ rule ∈ rules, rule.wellFormed = true := by
      simpa only [List.all_eq_true] using rules_wellFormed
    exact hall rule hmem
  exact Net.replace_valid hvalid hwell hactive hleft hright

inductive Step : Net → Net → Prop where
  | chosen {net : Net} {rule : TriageRuleModel.Rule} {left right : Nat} :
      (rule, left, right) ∈ net.redexChoices →
      Step net (net.replace rule left right)

abbrev Steps := Relation.ReflTransGen Step

theorem Step.preserves_valid {first second : Net}
    (hstep : Step first second) (hvalid : first.valid = true) :
    second.valid = true := by
  cases hstep with
  | chosen hchoice => exact Net.redexChoice_preserves_valid hvalid hchoice

/-- Validity is preserved under every finite order of executable choices. -/
theorem Steps.preserves_valid {first second : Net}
    (hsteps : Steps first second) (hvalid : first.valid = true) :
    second.valid = true := by
  induction hsteps with
  | refl => exact hvalid
  | tail _ hstep ih => exact Step.preserves_valid hstep ih

theorem Net.step_sound {net next : Net} (hstep : net.step? = some next) :
    Step net next := by
  cases hc : net.firstRedex with
  | none => simp [Net.step?, hc] at hstep
  | some choice =>
      rcases choice with ⟨rule, left, right⟩
      have hmem : (rule, left, right) ∈ net.redexChoices := by
        rcases List.head?_eq_some_iff.mp hc with ⟨rest, hlist⟩
        rw [hlist]
        exact List.mem_cons_self ..
      have heq : net.replace rule left right = next := by
        simpa [Net.step?, hc] using hstep
      rw [← heq]
      exact Step.chosen hmem

theorem Net.step_preserves_valid {net next : Net}
    (hvalid : net.valid = true) (hstep : net.step? = some next) :
    next.valid = true := Step.preserves_valid (Net.step_sound hstep) hvalid

theorem Net.run_steps (fuel : Nat) (net : Net) : Steps net (net.run fuel) := by
  induction fuel generalizing net with
  | zero => exact .refl
  | succ fuel ih =>
      cases hs : net.step? with
      | none => simpa only [Net.run, hs] using (Relation.ReflTransGen.refl : Steps net net)
      | some next =>
          simpa only [Net.run, hs] using
            Relation.ReflTransGen.head (Net.step_sound hs) (ih next)

theorem Net.run_preserves_valid (fuel : Nat) {net : Net}
    (hvalid : net.valid = true) : (net.run fuel).valid = true := by
  induction fuel generalizing net with
  | zero => exact hvalid
  | succ fuel ih =>
      cases hs : net.step? with
      | none => simpa [Net.run, hs] using hvalid
      | some next =>
          simpa [Net.run, hs] using
            ih (Net.step_preserves_valid hvalid hs)

theorem Net.trace_valid (fuel : Nat) {net : Net}
    (hvalid : net.valid = true) : (net.trace fuel).all Net.valid = true := by
  induction fuel generalizing net with
  | zero => simp [Net.trace, hvalid]
  | succ fuel ih =>
      cases hs : net.step? with
      | none => simp [Net.trace, hs, hvalid]
      | some next =>
          have hnext := ih (Net.step_preserves_valid hvalid hs)
          simpa [Net.trace, hs, hvalid] using hnext

end TriageReduction
