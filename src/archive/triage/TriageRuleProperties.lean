/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageRules

/-!
Properties of rule selection and the active pairs created directly inside a
replacement template. These statements concern the complete rule table
exported from netties; active pairs formed across a template boundary need a
reachable-net invariant and are not covered here.
-/

namespace TriageRuleProperties
open TriageRuleModel TriageRules

def accepts (rule : Rule) (left right : Kind) : Bool :=
  decide ((rule.left = left ∧ rule.right = right) ∨
    (rule.left = right ∧ rule.right = left))

theorem unique_rule {first second : Rule} (hf : first ∈ rules)
    (hs : second ∈ rules) {left right : Kind}
    (hfirst : accepts first left right = true)
    (hsecond : accepts second left right = true) : first = second := by
  have hall : ∀ a ∈ rules, ∀ b ∈ rules,
      Rule.nonOverlapping a b = true := by
    simpa only [List.all_eq_true] using rules_nonOverlapping
  by_cases heq : first = second
  · exact heq
  · have hnon := hall first hf second hs
    simp [Rule.nonOverlapping, heq] at hnon
    simp only [accepts, decide_eq_true_eq] at hfirst hsecond
    rcases hfirst with ⟨hfl, hfr⟩ | ⟨hfl, hfr⟩ <;>
      rcases hsecond with ⟨hsl, hsr⟩ | ⟨hsl, hsr⟩ <;>
      simp_all

def internalActiveCovered (all : List Rule) (rule : Rule) : Bool :=
  rule.wires.all fun (left, right) =>
    match left, right with
    | .agent i 0, .agent j 0 =>
        match rule.agents[i]?, rule.agents[j]? with
        | some a, some b => all.any fun candidate =>
            accepts candidate a b
        | _, _ => false
    | _, _ => true

/-- Every principal-principal connection between agents newly created in a
rule RHS is itself covered by the exported rule table. -/
theorem all_internal_active_pairs_covered :
    rules.all (internalActiveCovered rules) = true := by
  decide

theorem internal_active_has_rule {rule : Rule} (hrule : rule ∈ rules)
    {i j : Nat} {a b : Kind}
    (hi : rule.agents[i]? = some a) (hj : rule.agents[j]? = some b)
    (hwire : (End.agent i 0, End.agent j 0) ∈ rule.wires) :
    ∃ candidate ∈ rules, accepts candidate a b = true := by
  have hall : ∀ r ∈ rules, internalActiveCovered rules r = true := by
    simpa only [List.all_eq_true] using all_internal_active_pairs_covered
  have hwires : ∀ pair ∈ rule.wires,
      (match pair with
        | (left, right) =>
            match left, right with
            | .agent i 0, .agent j 0 =>
                match rule.agents[i]?, rule.agents[j]? with
                | some a, some b => rules.any fun candidate => accepts candidate a b
                | _, _ => false
            | _, _ => true) = true := by
    simpa only [internalActiveCovered, List.all_eq_true] using hall rule hrule
  have h := hwires _ hwire
  simp only [hi, hj, List.any_eq_true] at h
  exact h

end TriageRuleProperties
