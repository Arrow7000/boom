import TreeCalculus.Term

/-!
# Executable redex classification

These are local rewrite sites, not a test for normal form of an entire subtree.
`rootRule` matches exactly three arguments; `redexRule` also sees a rewritable
three-argument prefix with further arguments attached by application.
Correctness against `RewriteRules` is checked in `TreeCalculus.lean`.
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
is proved sound with respect to `Reduces` in `TreeCalculus.lean`.
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
