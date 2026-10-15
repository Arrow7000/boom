/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import Mathlib.Tactic.Tauto

/-!
# Canonical Tree Calculus syntax

`Term` is the ordered-tree presentation of the free applicative syntax
`E ::= △ | E E`: each node is a `△`, with its arguments as ordered children.
It includes unreduced applications with three or more children. The
value/redex presentation is available separately in `TreeCalculus.ValOrRedex`.
-/

/-- The canonical Tree Calculus syntax: an ordered node with any number of
children. `△` is a leaf and application appends a child. Being a value, being
in normal form, and being rewritable are separate properties of this syntax. -/
@[grind cases]
inductive Term : Type where
  | term : List Term → Term


@[grind]
def Term.decEq (a b : Term) : Decidable (a = b) :=
    match a, b with
    | .term [], .term [] =>
      .isTrue ?_
    | .term (a :: as), .term (b :: bs) =>
      match a.decEq b with
      | .isTrue prf =>
        match (Term.term as).decEq (.term bs) with
        | .isTrue prf' => .isTrue ?_
        | .isFalse prf' => .isFalse ?_
      | .isFalse prf => .isFalse ?_
    | .term (_ :: _), .term [] =>
      .isFalse ?_
    | .term [], .term (_ :: _) =>
      .isFalse ?_
  where finally
    · simp
    · subst_eqs
      simp
    · grind
    · grind
    · grind
    · simp


@[grind ., simp]
theorem Term.nil_ne_cons : ∀ (a : Term) (as : List Term), Term.term [] ≠ Term.term (a :: as) := by
  intro a as h
  injection h with h'
  exact List.noConfusion h'

-- Mark term constructor as injective for simp
@[simp, grind =]
theorem Term.term_injective {xs ys : List Term} : Term.term xs = Term.term ys ↔ xs = ys := by
  constructor
  · intro h; injection h
  · intro h; rw [h]


@[grind]
instance : DecidableEq Term := Term.decEq



/-- Spec application: attach `arg` as the rightmost child of `fn`'s root.
Application itself is left-associative; “to the right” means where the child
hangs on the tree, i.e. `children ++ [arg]`. -/
@[reducible, grind]
def Term.apply (fn arg : Term) : Term :=
  match fn with
  | .term cs => .term (cs ++ [arg])

@[match_pattern]
notation "△" => Term.term []

@[inherit_doc, match_pattern] infixl:67 " ⬝ " => Term.apply
