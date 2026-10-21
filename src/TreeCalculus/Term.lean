/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import Mathlib.Tactic.Tauto

/-!
# Canonical Tree Calculus syntax and rewrite rules

`Term` is the ordered-tree presentation of the free applicative syntax
`E ::= △ | E E`: each node is a `△`, with its arguments as ordered children.
It includes unreduced applications with three or more children. The
value/redex presentation is available separately in `TreeCalculus.ValOrRedex`.

The file ends with the rewrite rules and the one-step reduction relation
`Reduces`.
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
  cases h'

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

/-- Syntax sugar for an empty tree calculus term -/
@[match_pattern]
notation "△" => Term.term []

/-- Left-associative application, the usual companion to `△`.

`t ⬝ u` applies `t` to `u`. A leaf is `△`; each `⬝` adds a child, so
`△ ⬝ a ⬝ b ⬝ c` is the tree with children `a`, `b`, `c`. Parentheses nest
subtrees, e.g. `△ ⬝ (△ ⬝ x) ⬝ y`. -/
@[match_pattern] infixl:67 " ⬝ " => Term.apply




/-! ## Structure of application -/

/-- Returns all of a term's children. There is nothing else to a term than its children. -/
def Term.children : Term → List Term
  | .term cs => cs

def Term.numChildren : Term → Nat
  | .term cs => cs.length

@[simp] theorem Term.numChildren_apply (t1 t2 : Term) :
    (t1 ⬝ t2).numChildren = t1.numChildren + 1 := by
  cases t1; simp [Term.numChildren]

theorem Term.foldl_apply (t : Term) (cs : List Term) :
    cs.foldl (· ⬝ ·) t = match t with | .term ts => .term (ts ++ cs) := by
  induction cs generalizing t with
  | nil => cases t; simp
  | cons a as ih =>
    cases t with | term ts
    simp only [List.foldl, Term.apply]
    rw [ih]
    simp [List.append_assoc]

theorem Term.term_eq_foldl (cs : List Term) :
    Term.term cs = cs.foldl (· ⬝ ·) △ := by
  rw [Term.foldl_apply]; simp

theorem Term.apply_ne_delta (fn arg : Term) : fn ⬝ arg ≠ △ := by
  cases fn with | term cs
  simp [Term.apply]

theorem Term.eq_stem_of_apply {t1 t2 a : Term} (h : t1 ⬝ t2 = △ ⬝ a) :
    t1 = △ ∧ t2 = a := by
  cases t1 with | term cs
  simp [Term.apply] at h
  match cs with
  | [] =>
    simp at h
    exact ⟨rfl, h⟩
  | head :: tail =>
    have hlen := congrArg List.length h
    simp at hlen

theorem Term.eq_fork_of_apply {t1 t2 a b : Term} (h : t1 ⬝ t2 = △ ⬝ a ⬝ b) :
    t1 = △ ⬝ a ∧ t2 = b := by
  cases t1 with | term cs
  simp [Term.apply] at h
  match cs with
  | [] => simp at h
  | [x] =>
    simp at h
    refine ⟨?_, h.2⟩
    simp [Term.apply, h.1]
  | x :: y :: zs =>
    have hlen := congrArg List.length h
    simp at hlen

theorem Term.apply_inj {fn1 arg1 fn2 arg2 : Term}
    (h : fn1 ⬝ arg1 = fn2 ⬝ arg2) : fn1 = fn2 ∧ arg1 = arg2 := by
  cases fn1 with | term cs1
  cases fn2 with | term cs2
  simp [Term.apply] at h
  exact ⟨congrArg Term.term h.1, h.2⟩

/-- Explicit weight: nested `sizeOf` on `Term`/`List` is awkward for `omega`. -/
def Term.weight : Term → Nat
  | .term cs => 1 + (cs.map weight).sum

theorem Term.weight_lt_of_mem {a : Term} {cs : List Term} (h : a ∈ cs) :
    a.weight < (Term.term cs).weight := by
  induction cs with
  | nil => cases h
  | cons b bs ih =>
    simp [Term.weight] at *
    cases h with
    | inl heq => subst heq; omega
    | inr hmem =>
      have := ih hmem
      simp at this ⊢
      omega

/-! ## Rewrite rules and reduction

This is the whole calculus: five rules, plus congruence so that any subterm
can be rewritten. -/

/-- The tree calculus rewrite rules. Not reflexive or transitive. -/
inductive RewriteRules : (input output : Term) → Prop where
  | one {y z : Term} :
    RewriteRules (△⬝△⬝y⬝z)
      y

  | two {x y z : Term} :
    RewriteRules (△⬝(△⬝x)⬝y⬝z)
      (x⬝z⬝(y⬝z))

  | threeA {w x y : Term} :
    RewriteRules (△⬝(△⬝w⬝x)⬝y⬝△)
      w

  | threeB {w x y u : Term} :
    RewriteRules (△⬝(△⬝w⬝x)⬝y⬝(△⬝u))
      (x⬝u)

  | threeC {w x y u v : Term} :
    RewriteRules (△⬝(△⬝w⬝x)⬝y⬝(△⬝u⬝v))
      (y⬝u⬝v)

-- Full reduction relation: includes the 5 rules + congruence
@[grind cases]
inductive Reduces : (input output : Term) → Prop where
  | rule {t t' : Term} :
      RewriteRules t t' →
      Reduces t t'
  | congr_left {t1 t1' t2 : Term} :
      Reduces t1 t1' →
      Reduces (t1⬝t2) (t1'⬝t2)
  | congr_right {t1 t2 t2' : Term} :
      Reduces t2 t2' →
      Reduces (t1⬝t2) (t1⬝t2')

theorem Reduces.congr_foldl {t t' : Term} (args : List Term) (h : Reduces t t') :
    Reduces (args.foldl (· ⬝ ·) t) (args.foldl (· ⬝ ·) t') := by
  induction args generalizing t t' with
  | nil => exact h
  | cons a as ih => exact ih (Reduces.congr_left h)

/-- Any argument can be rewritten in place: earlier arguments are a prefix
application (`congr_right`), later ones are reattached (`congr_left`). -/
theorem Reduces.congr_arg {cs : List Term} {i : Nat} {c c' : Term}
    (hi : cs[i]? = some c) (h : Reduces c c') : Reduces (.term cs) (.term (cs.set i c')) := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hi
  have hsplit : ∀ x, Term.term (cs.take i ++ x :: cs.drop (i + 1)) =
      (cs.drop (i + 1)).foldl (· ⬝ ·) (Term.term (cs.take i) ⬝ x) := by
    intro x; rw [Term.foldl_apply]; simp
  have hcs : cs = cs.take i ++ cs[i] :: cs.drop (i + 1) := by simp
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hlt, hsplit]
  have := Reduces.congr_foldl (cs.drop (i + 1)) (Reduces.congr_right (t1 := .term (cs.take i)) h)
  rwa [← hsplit cs[i], ← hcs] at this

theorem RewriteRules.numChildren_eq_three {t t' : Term}
    (h : RewriteRules t t') : t.numChildren = 3 := by
  cases h <;> simp [Term.numChildren, Term.apply]
