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
