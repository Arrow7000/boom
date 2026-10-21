/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus

/-!
# Quest 1: normal forms, from both sides

`Term.NormalForm` is defined by *shape*: a leaf, stem or fork of normal forms.
`Term.Diverges` says every reduct can still take a step. Neither says directly
what we mean by "finished" or "runs forever". This quest connects them, and
pins down the difference between *having no normal form* and *having an
infinite reduction*.

Builds on `Term.progress` and `Term.NormalForm.irreducible` (section
`NormalForms` in `TreeCalculus.lean`) and `combΩ_diverges`.

Rough size: part A is a few lines, part B a few dozen, and part C is the
interesting one.

Hints: `hints/Q1Normalization.md`.
-/

/-! ## Part A: stuck terms -/

/-- `t` is stuck: no `Reduces` step starts from `t`. -/
def Term.Irreducible (t : Term) : Prop := sorry

example : (△ : Term).Irreducible := sorry
example : combI.Irreducible := sorry
/-- A redex hidden inside a stem still counts. -/
example : ¬ (△ ⬝ (△ ⬝ △ ⬝ △ ⬝ △)).Irreducible := sorry
example : ¬ combΩ.Irreducible := sorry

/-- The shape definition and the behavioural one agree. -/
theorem Term.normalForm_iff_irreducible (t : Term) : t.NormalForm ↔ t.Irreducible := sorry

/-! ## Part B: having a normal form -/

/-- `t` can reach a normal form in finitely many steps (it is *weakly
normalizing*). It may also have other reduction paths that never finish. -/
def Term.HasNormalForm (t : Term) : Prop := sorry

example : (△ : Term).HasNormalForm := sorry
/-- `K △ Ω`: rule 1 throws `Ω` away. -/
example : (△ ⬝ △ ⬝ △ ⬝ combΩ).HasNormalForm := sorry
example : ¬ combΩ.HasNormalForm := sorry

theorem Term.diverges_iff_not_hasNormalForm (t : Term) :
  t.Diverges ↔ ¬ t.HasNormalForm := sorry

/-! ## Part C: infinite reductions -/

/-- There is an infinite sequence of `Reduces` steps starting at `t`. -/
def Term.HasInfiniteReduction (t : Term) : Prop := sorry

example : ¬ (△ : Term).HasInfiniteReduction := sorry

/-- Having no normal form gives an infinite reduction... -/
theorem Term.Diverges.hasInfiniteReduction {t : Term} (h : t.Diverges) :
  t.HasInfiniteReduction := sorry

example : combΩ.HasInfiniteReduction := sorry

/-- ...but not conversely: a term can have a normal form *and* an infinite
reduction. So "diverges" and "may run forever" are different properties. -/
theorem Term.exists_hasNormalForm_hasInfiniteReduction :
  ∃ t : Term, t.HasNormalForm ∧ t.HasInfiniteReduction := sorry
