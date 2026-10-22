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

-- /-- `t` is stuck: no `Reduces` step starts from `t`. -/
-- def Term.Irreducible (t : Term) : Prop := t.NormalForm

-- example : (△ : Term).Irreducible := by
--   have is_leaf : △.IsLeaf := rfl
--   have := RewriteRules.leaf_irreducible _ is_leaf
--   simp [Term.Irreducible]
--   exact Term.NormalForm.leaf




/-- `t` is stuck: no `Reduces` step starts from `t`. -/
def Term.Irreducible (t : Term) : Prop := ¬∃ t', Reduces t t'

example : (△ : Term).Irreducible := by
  have is_leaf : △.IsLeaf := rfl
  have := RewriteRules.leaf_irreducible _ is_leaf
  simp only [Term.Irreducible]
  simp
  intro t
  refine Term.NormalForm.irreducible ?_ t
  exact Term.NormalForm.leaf






lemma combI_is_Irreducible : combI.Irreducible := by
  simp [Term.Irreducible, combI]

  generalize ha : △ ⬝ (△ ⬝ △) = a
  generalize hb : △ ⬝ △ = b
  generalize ht : (△ ⬝ a) ⬝ b = t
  intro t'
  refine Term.NormalForm.irreducible ?_ t'

  have han : a.NormalForm := by
    subst ha
    constructor
    constructor
    constructor

  have hbn : b.NormalForm := by
    subst hb
    constructor
    constructor

  subst t
  refine Term.NormalForm.fork _ _ han hbn


example : combI.Irreducible := combI_is_Irreducible



/-- A redex hidden inside a stem still counts. -/
example : ¬ (△ ⬝ (△ ⬝ △ ⬝ △ ⬝ △)).Irreducible := by
  simp only [Term.Irreducible]
  simp
  have ⟨t, ht⟩ : ∃ t', Reduces (△ ⬝ △ ⬝ △ ⬝ △) t' := Term.exists_reduces_of_three (by simp [Term.numChildren]) (by simp [Term.numChildren])
  have := Reduces.congr_right (t1 := △) ht
  refine ⟨_,this⟩


lemma combΩ_not_irreducible : ¬ combΩ.Irreducible := by
  simp only [Term.Irreducible]
  simp
  have : ¬combΩ.NormalForm := by
    simp only [combΩ, combω]
    intro contra
    cases contra

  exact combΩ.progress this


example : ¬ combΩ.Irreducible := combΩ_not_irreducible





/-- The shape definition and the behavioural one agree. -/
theorem Term.normalForm_iff_irreducible (t : Term) : t.NormalForm ↔ t.Irreducible := by
  constructor
  · intro hnf
    simp only [Term.Irreducible]
    simp
    exact Term.NormalForm.irreducible hnf
  · false_or_by_contra
    expose_names
    simp only [Term.Irreducible] at h
    have := t.progress h_1
    exact h this




/-! ## Part B: having a normal form -/


/-- Zero or more reductions can get `t` to `t'`. -/
@[simp]
def Term.MultiStepReduction (t t' : Term) := Relation.ReflTransGen Reduces t t'

/-- `t` can reach a normal form in finitely many steps (it is *weakly
normalizing*). It may also have other reduction paths that never finish. -/
def Term.HasNormalForm (t : Term) : Prop := ∃ t', Term.MultiStepReduction t t' ∧ t'.NormalForm

example : (△ : Term).HasNormalForm := by
  simp [Term.HasNormalForm]
  exists △
  constructor
  · refine .refl
  · refine .leaf

/-- `K △ Ω`: rule 1 throws `Ω` away. -/
example : (△ ⬝ △ ⬝ △ ⬝ combΩ).HasNormalForm := by
  simp [Term.HasNormalForm]
  exists △
  constructor
  · have : Reduces (△ ⬝ △ ⬝ △ ⬝ combΩ) △ := .rule .one
    refine .tail .refl this
  · exact .leaf



example : ¬ combΩ.HasNormalForm := by
  simp [Term.HasNormalForm]
  intro t chain
  have := combΩ_diverges
  simp [Term.Diverges] at this
  replace this := this _ chain
  apply t.normalForm_iff_irreducible.not.mpr
  simp [Term.Irreducible]
  exact this







theorem Term.diverges_iff_not_hasNormalForm (t : Term) :
  t.Diverges ↔ ¬ t.HasNormalForm := by
  constructor
  · intro hdiv
    simp [Term.HasNormalForm]
    intro t' hchain
    simp [Term.Diverges] at hdiv
    apply t'.normalForm_iff_irreducible.not.mpr
    simp [Term.Irreducible]
    exact hdiv _ hchain
  · intro hnorm
    simp [HasNormalForm, Diverges] at hnorm ⊢
    intro t' hchain
    have := hnorm _ hchain
    have := t'.normalForm_iff_irreducible.not.mp this
    simp [Term.Irreducible] at this
    exact this




/-! ## Part C: infinite reductions -/



/-- There is an infinite sequence of `Reduces` steps starting at `t`. -/
coinductive Term.HasInfiniteReduction : Term → Prop
  | mk :
    Reduces t t' →
    Term.HasInfiniteReduction t' →
    Term.HasInfiniteReduction t




-- def Term.HasInfiniteReduction (t : Term) : Prop :=

example : ¬ (△ : Term).HasInfiniteReduction := by
  intro prem
  cases prem with
  | @mk t t' rel ih =>
    generalize h : △ = t at rel
    cases rel
    · expose_names
      cases h_1
      repeat cases h
    · exact (Term.apply_ne_delta _ _).elim h.symm
    · exact (Term.apply_ne_delta _ _).elim h.symm

/-- Having no normal form gives an infinite reduction... -/
theorem Term.Diverges.hasInfiniteReduction {t : Term} (h : t.Diverges) :
  t.HasInfiniteReduction := by
  simp [Diverges] at h
  have :=
    Term.HasInfiniteReduction.coinduct
      (Relation.ReflTransGen Reduces t)
      (by
        intro a hchain
        replace h := h a hchain
        obtain ⟨v,hredv⟩ := h
        refine ⟨v, hredv, .tail hchain hredv⟩)
  apply this
  exact .refl





example : combΩ.HasInfiniteReduction := combΩ_diverges.hasInfiniteReduction






lemma Term.HasInfiniteReduction.congr_right (heq : outer = a ⬝ inner) : inner.HasInfiniteReduction → outer.HasInfiniteReduction := by
  intro hinf
  apply HasInfiniteReduction.coinduct
    (fun t ↦ ∃ inner', t = a ⬝ inner' ∧ inner'.HasInfiniteReduction) _ _ ⟨_, heq, hinf⟩
  intro t ih
  obtain ⟨inn', heq', hinf'⟩ := ih
  cases hinf' with
  | @mk _ inn'' hred hinf'' =>
    exists a ⬝ inn''
    constructor
    · subst_eqs
      exact .congr_right hred
    · subst_eqs
      exists inn''





/-- ...but not conversely: a term can have a normal form *and* an infinite
reduction. So "diverges" and "may run forever" are different properties. -/
theorem Term.exists_hasNormalForm_hasInfiniteReduction :
  ∃ t : Term, t.HasNormalForm ∧ t.HasInfiniteReduction := by
  let kapp := △ ⬝ △ ⬝ △ ⬝ combΩ
  have hk : kapp = kapp := rfl
  conv at hk =>
    right
    unfold kapp
  exists kapp
  constructor
  · have rule_one : RewriteRules kapp △ := .one
    simp [HasNormalForm]
    exists △
    refine ⟨.tail .refl (.rule rule_one), .leaf⟩
  · have := combΩ_diverges.hasInfiniteReduction
    refine Term.HasInfiniteReduction.congr_right hk combΩ_diverges.hasInfiniteReduction
