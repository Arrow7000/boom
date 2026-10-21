/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus.Term

/-!
# Executable redex classification

These are local rewrite sites, not a test for normal form of an entire subtree.
`rootRule` matches exactly three arguments; `redexRule` also sees a rewritable
three-argument prefix with further arguments attached by application.
Correctness against `RewriteRules` and `Reduces` is proved at the end of this file.
-/

inductive RedexRule where
  | one | two | threeA | threeB | threeC
  deriving DecidableEq, Repr

def RedexRule.label : RedexRule → String
  | .one => "1"
  | .two => "2"
  | .threeA => "3a"
  | .threeB => "3b"
  | .threeC => "3c"

/-- Which rule fires on this entire term, without application congruence? -/
def Term.rootRule : Term → Option RedexRule
  | .term [.term [], _, _] => some .one
  | .term [.term [_], _, _] => some .two
  | .term [.term [_, _], _, .term []] => some .threeA
  | .term [.term [_, _], _, .term [_]] => some .threeB
  | .term [.term [_, _], _, .term [_, _]] => some .threeC
  | _ => none

/-- Which rule fires at this node's three-argument application prefix?
Descendants are classified independently; extra arguments are retained. -/
def Term.redexRule : Term → Option RedexRule
  | .term (a :: b :: c :: _) => (Term.term [a, b, c]).rootRule
  | _ => none

/-! ### Executable rewriting

The widget steps through reductions with these functions. `Term.rewriteAt?`
is proved sound with respect to `Reduces` below.
-/

/-- The output of `RewriteRules` on a term with exactly three arguments. -/
def Term.rootRewrite? : Term → Option Term
  | .term [.term [], y, _] => some y
  | .term [.term [x], y, z] => some (x ⬝ z ⬝ (y ⬝ z))
  | .term [.term [w, _], _, .term []] => some w
  | .term [.term [_, x], _, .term [u]] => some (x ⬝ u)
  | .term [.term [_, _], y, .term [u, v]] => some (y ⬝ u ⬝ v)
  | _ => none

/-- Rewrite this node's three-argument prefix, reattaching further arguments. -/
def Term.rewrite? : Term → Option Term
  | .term (a :: b :: c :: rest) => (Term.term [a, b, c]).rootRewrite?.map (rest.foldl (· ⬝ ·))
  | _ => none

/-- Rewrite the node reached by following child indices from the root. -/
def Term.rewriteAt? : Term → List Nat → Option Term
  | t, [] => t.rewrite?
  | .term cs, i :: path => do
    let c' ← (← cs[i]?).rewriteAt? path
    return .term (cs.set i c')

def Term.subtermAt? : Term → List Nat → Option Term
  | t, [] => some t
  | .term cs, i :: path => do (← cs[i]?).subtermAt? path

/-- The leftmost-outermost rewrite site: the first in preorder. -/
def Term.firstRedex? : Term → Option (List Nat)
  | t@(.term cs) => if t.redexRule.isSome then some [] else go 0 cs
where
  go (i : Nat) : List Term → Option (List Nat)
    | [] => none
    | c :: cs => (c.firstRedex?.map (i :: ·)).or (go (i + 1) cs)

def Term.size : Term → Nat
  | .term cs => 1 + (cs.map Term.size).sum

/-- Leftmost-outermost reduction for at most `fuel` steps, stopping early once
the term grows beyond `maxSize` nodes. Returns the result and the step count. -/
def Term.runOutermost (fuel maxSize : Nat) (t : Term) (steps : Nat := 0) : Term × Nat :=
  match fuel with
  | 0 => (t, steps)
  | fuel + 1 =>
    match t.firstRedex?.bind t.rewriteAt? with
    | none => (t, steps)
    | some t' => if t'.size > maxSize then (t', steps + 1) else t'.runOutermost fuel maxSize (steps + 1)




/-! ### Agreement with `RewriteRules` and `Reduces` -/

/-- Every reported local rule is an actual rewrite rule. -/
theorem Term.rootRule_sound (h : t.rootRule = some rule) :
    ∃ output, RewriteRules t output := by
  unfold Term.rootRule at h
  split at h
  · exact ⟨_, .one⟩
  · exact ⟨_, .two⟩
  · exact ⟨_, .threeA⟩
  · exact ⟨_, .threeB⟩
  · exact ⟨_, .threeC⟩
  · contradiction

/-- The local classifier detects exactly the roots accepted by `RewriteRules`. -/
theorem Term.rootRule_correct (t : Term) :
    t.rootRule.isSome = true ↔ ∃ output, RewriteRules t output := by
  constructor
  · intro h
    cases heq : t.rootRule with
    | none => simp [heq] at h
    | some rule => exact Term.rootRule_sound heq
  · rintro ⟨_, h⟩
    cases h <;> rfl

-- theorem Term.rootRule_complete (t : Term) :
--     t.rootRule = some output ↔ RewriteRules t output := by
--   sorry


/-- Extra arguments do not hide a rewrite site in the application prefix. -/
theorem Term.redexRule_prefix_correct (a b c : Term) (rest : List Term) :
    (Term.term (a :: b :: c :: rest)).redexRule.isSome = true ↔
      ∃ output, RewriteRules (Term.term [a, b, c]) output :=
  Term.rootRule_correct _

theorem Term.rootRewrite?_sound {t t' : Term} (h : t.rootRewrite? = some t') :
    RewriteRules t t' := by
  unfold Term.rootRewrite? at h
  split at h <;> cases h
  · exact .one
  · exact .two
  · exact .threeA
  · exact .threeB
  · exact .threeC

theorem Term.rewrite?_sound {t t' : Term} (h : t.rewrite? = some t') : Reduces t t' := by
  unfold Term.rewrite? at h
  split at h
  · rename_i a b c rest
    obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
    have : Term.term (a :: b :: c :: rest) = rest.foldl (· ⬝ ·) (.term [a, b, c]) := by
      rw [Term.foldl_apply]; rfl
    rw [this]
    exact Reduces.congr_foldl rest (.rule (Term.rootRewrite?_sound hr))
  · cases h

/-- Every step the widget shows is a `Reduces` step. -/
theorem Term.rewriteAt?_sound {t t' : Term} {path : List Nat}
    (h : t.rewriteAt? path = some t') : Reduces t t' := by
  induction path generalizing t t' with
  | nil => exact Term.rewrite?_sound h
  | cons i path ih =>
    obtain ⟨cs⟩ := t
    simp only [Term.rewriteAt?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨c, hc, c', hc', rfl⟩ := h
    exact Reduces.congr_arg hc (ih hc')

theorem Term.rootRewrite?_isSome (a b c : Term) :
    (Term.term [a, b, c]).rootRewrite?.isSome = (Term.term [a, b, c]).rootRule.isSome := by
  obtain ⟨_ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ := a <;>
    obtain ⟨_ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ := c <;> rfl

/-- The widget colours exactly the nodes it can rewrite. -/
theorem Term.rewrite?_isSome (t : Term) : t.rewrite?.isSome = t.redexRule.isSome := by
  unfold Term.rewrite? Term.redexRule
  split
  · rw [Option.isSome_map]; exact Term.rootRewrite?_isSome ..
  · rfl
