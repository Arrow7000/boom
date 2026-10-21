/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus

/-!
# Quest 2: confluence

If a term can reduce to `a` and also to `b`, then `a` and `b` can both reduce
further to a common term. The order in which you fire redexes never changes
the final answer. This is the Church–Rosser theorem for tree calculus, and
most later quests rely on it.

What's given: the props in the headline statements, with their shapes. What's
yours: their definitions, and *every* auxiliary relation and lemma the proof
needs. Most of the design work is in those, and part B shows why they're
needed.

Rough size: large. The proof for the other presentation in `ValOrRedex.lean`
is long. Don't open that file before hint 5 of part C, because it gives the
design away.

Hints: `hints/Q2Confluence.md`.
-/

/-! ## Part A: what confluence means -/

/-- `r` is confluent: whenever `t` reaches both `a` and `b` in zero or more
`r`-steps, there is a `d` that both `a` and `b` reach in zero or more
`r`-steps. -/
def Confluent {α : Type} (r : α → α → Prop) : Prop := sorry

example : Confluent (fun _ _ : Nat => False) := sorry
/-- Deterministic relations are confluent. -/
example : Confluent (fun a b : Nat => b = a + 1) := sorry
/-- Two branches that never meet again. -/
example : ¬ Confluent (fun a b : Fin 3 => a = 0 ∧ b ≠ 0) := sorry

/-! ## Part B: why the obvious proof fails

The obvious attempt: "if `t` steps to `a` and to `b`, then `a` and `b` meet
again within one step each", and then induction. That isn't true. Find a term
that breaks it. (Rule 2 copies its third argument.) -/

example : ¬ ∀ t a b : Term, Reduces t a → Reduces t b →
    ∃ d, Relation.ReflGen Reduces a d ∧ Relation.ReflGen Reduces b d := sorry

/-! ## Part C: the theorem -/

theorem Reduces.confluent : Confluent Reduces := sorry

/-! ## Part D: consequences -/

/-- A term has at most one normal form. -/
theorem Term.normalForm_unique {t n₁ n₂ : Term}
    (h₁ : Relation.ReflTransGen Reduces t n₁) (h₂ : Relation.ReflTransGen Reduces t n₂)
    (hn₁ : n₁.NormalForm) (hn₂ : n₂.NormalForm) : n₁ = n₂ := sorry

/-- Equality in the equational theory of tree calculus: the smallest
equivalence relation containing `Reduces`. Steps may go forwards *or*
backwards. -/
def Term.Convertible (a b : Term) : Prop := sorry

example : (△ ⬝ △ ⬝ △ ⬝ combΩ).Convertible △ := sorry
/-- Backwards steps are allowed. -/
example : (△ : Term).Convertible (△ ⬝ △ ⬝ △ ⬝ combΩ) := sorry

/-- Zig-zags of forward and backward steps can be straightened out. -/
theorem Term.Convertible.joinable {a b : Term} (h : a.Convertible b) :
    ∃ d, Relation.ReflTransGen Reduces a d ∧ Relation.ReflTransGen Reduces b d := sorry

/-- Consistency: the theory doesn't prove every equation. -/
theorem Term.not_convertible_leaf_stem : ¬ (△ : Term).Convertible (△ ⬝ △) := sorry
