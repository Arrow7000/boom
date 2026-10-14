/-!
A finite model of the rule templates used by netties' interaction-net engine.
The separate generated `TriageRules.lean` contains the actual agent and wire
table exported from `src/core/triageMachine.ts`.
-/

namespace TriageRuleModel

inductive Kind where
  | leaf | stem | fork | app | eval | call | case_ | triage | dup | erase
  deriving Repr, DecidableEq

def Kind.arity : Kind → Nat
  | .leaf | .erase => 0
  | .stem | .eval => 1
  | .fork | .app | .call | .dup => 2
  | .case_ => 3
  | .triage => 4

inductive End where
  | agent : Nat → Nat → End
  | iface : Nat → Nat → End
  deriving Repr, DecidableEq

structure Rule where
  left : Kind
  right : Kind
  agents : List Kind
  wires : List (End × End)
  deriving Repr, DecidableEq

def Rule.expected (rule : Rule) : List End :=
  ((List.range rule.left.arity).map (fun slot => End.iface 0 (slot + 1))) ++
  ((List.range rule.right.arity).map (fun slot => End.iface 1 (slot + 1))) ++
  (rule.agents.zipIdx.flatMap fun (kind, index) =>
    (List.range (kind.arity + 1)).map (End.agent index))

def Rule.used (rule : Rule) : List End :=
  rule.wires.flatMap fun (left, right) => [left, right]

/-- A rule RHS uses every old auxiliary port and every created port exactly
once. This is the same finite condition checked by `System.validate` in JS. -/
def Rule.wellFormed (rule : Rule) : Bool :=
  decide rule.used.Nodup &&
  decide (rule.used.length = rule.expected.length) &&
  rule.used.all (fun end_ => rule.expected.any (fun expected => decide (end_ = expected)))

theorem Rule.wellFormed_iff (rule : Rule) :
    rule.wellFormed = true ↔
      rule.used.Nodup ∧ rule.used.length = rule.expected.length ∧
        ∀ end_ ∈ rule.used, end_ ∈ rule.expected := by
  simp [Rule.wellFormed, List.all_eq_true, List.any_eq_true, and_assoc]

def Rule.branchesOnlyOnHeads (rule : Rule) : Bool :=
  if rule.left = .triage then
    decide (rule.right = .leaf ∨ rule.right = .stem ∨ rule.right = .fork)
  else true

def Rule.nonOverlapping (first second : Rule) : Bool :=
  if first = second then true else
    decide (¬ ((first.left = second.left ∧ first.right = second.right) ∨
               (first.left = second.right ∧ first.right = second.left)))

def Rule.hasWire (rule : Rule) (a b : End) : Bool :=
  rule.wires.any fun (x, y) =>
    decide ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- The actual `Dup/value` template creates two value agents and one
duplicator for each child, with the two outputs wired to the copies. -/
def Rule.copyLayout (rule : Rule) : Bool :=
  if rule.left = .dup then
    decide (rule.agents =
      [rule.right, rule.right] ++ List.replicate rule.right.arity .dup) &&
    rule.hasWire (.agent 0 0) (.iface 0 1) &&
    rule.hasWire (.agent 1 0) (.iface 0 2) &&
    (List.range rule.right.arity).all (fun i =>
      rule.hasWire (.agent (i + 2) 0) (.iface 1 (i + 1)) &&
      rule.hasWire (.agent (i + 2) 1) (.agent 0 (i + 1)) &&
      rule.hasWire (.agent (i + 2) 2) (.agent 1 (i + 1)))
  else true

/-- The actual `Erase/value` template recursively erases each child. -/
def Rule.eraseLayout (rule : Rule) : Bool :=
  if rule.left = .erase then
    decide (rule.agents = List.replicate rule.right.arity .erase) &&
    (List.range rule.right.arity).all (fun i =>
      rule.hasWire (.agent i 0) (.iface 1 (i + 1)))
  else true

def Rule.introduces (rule : Rule) (kind : Kind) : Bool :=
  rule.agents.any fun created => decide (created = kind)

/-- Every newly created observer is paired with an evaluator at its
principal port. The evaluator receives the raw source term. -/
def Rule.observerBarrier (rule : Rule) : Bool :=
  match rule.left, rule.right with
  | .eval, .app =>
      decide (rule.agents = [.eval, .call]) &&
      rule.hasWire (.agent 0 0) (.iface 1 1) &&
      rule.hasWire (.agent 0 1) (.agent 1 0)
  | .call, .fork =>
      decide (rule.agents = [.eval, .case_]) &&
      rule.hasWire (.agent 0 0) (.iface 1 1) &&
      rule.hasWire (.agent 0 1) (.agent 1 0)
  | .case_, .fork =>
      decide (rule.agents = [.eval, .triage]) &&
      rule.hasWire (.agent 0 0) (.iface 0 3) &&
      rule.hasWire (.agent 0 1) (.agent 1 0)
  | _, _ => true

def Rule.observerProvenance (rule : Rule) : Bool :=
  (if rule.introduces .call then
    decide (rule.left = .eval ∧ rule.right = .app) else true) &&
  (if rule.introduces .case_ then
    decide (rule.left = .call ∧ rule.right = .fork) else true) &&
  (if rule.introduces .triage then
    decide (rule.left = .case_ ∧ rule.right = .fork) else true)

end TriageRuleModel
