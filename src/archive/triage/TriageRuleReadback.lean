/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageRules
import TriageMachine

/-!
Read back the expression fed to a new `Eval` agent from an exported rule's
right-hand-side wiring. This is a local graph check: interface ports become
variables, while newly created `App`, `Leaf`, `Stem`, and `Fork` agents form
expressions. It does not yet traverse the surrounding net or interpret
`Dup`/`Erase` interactions.
-/

namespace TriageRuleReadback
open TriageRuleModel TriageRules
open TriageMachine

inductive Expr where
  | boundary : Nat → Nat → Expr
  | leaf : Expr
  | stem : Expr → Expr
  | fork : Expr → Expr → Expr
  | app : Expr → Expr → Expr
  deriving Repr, DecidableEq

def Expr.instantiate (env : Nat → Nat → Syntax) : Expr → Syntax
  | .boundary side slot => env side slot
  | .leaf => .leaf
  | .stem child => TriageMachine.stem (child.instantiate env)
  | .fork left right =>
      TriageMachine.fork (left.instantiate env) (right.instantiate env)
  | .app fn arg => .app (fn.instantiate env) (arg.instantiate env)

def triageEnv (w x y u v : Syntax) : Nat → Nat → Syntax
  | 0, 2 => w
  | 0, 3 => x
  | 0, 4 => y
  | 1, 1 => u
  | 1, 2 => v
  | _, _ => .leaf

def neighborIn : List (End × End) → End → Option End
  | [], _ => none
  | (a, b) :: rest, end_ =>
      if end_ = a then some b
      else if end_ = b then some a
      else neighborIn rest end_

def readRoot (rule : Rule) : Nat → End → Option Expr
  | 0, _ => none
  | _ + 1, .iface side slot => some (.boundary side slot)
  | fuel + 1, .agent index slot =>
      if slot != 0 then none else
      match rule.agents[index]? with
      | some .leaf => some .leaf
      | some .stem => do
          let childEnd ← neighborIn rule.wires (.agent index 1)
          let child ← readRoot rule fuel childEnd
          some (.stem child)
      | some .fork => do
          let leftEnd ← neighborIn rule.wires (.agent index 1)
          let rightEnd ← neighborIn rule.wires (.agent index 2)
          let left ← readRoot rule fuel leftEnd
          let right ← readRoot rule fuel rightEnd
          some (.fork left right)
      | some .app => do
          let fnEnd ← neighborIn rule.wires (.agent index 1)
          let argEnd ← neighborIn rule.wires (.agent index 2)
          let fn ← readRoot rule fuel fnEnd
          let arg ← readRoot rule fuel argEnd
          some (.app fn arg)
      | _ => none

def readEvalInput (rule : Rule) (evalIndex fuel : Nat) : Option Expr := do
  if rule.agents[evalIndex]? != some .eval then none else
  let root ← neighborIn rule.wires (.agent evalIndex 0)
  readRoot rule fuel root

def ruleFor (left right : Kind) : Option Rule :=
  rules.find? (fun rule => decide (rule.left = left ∧ rule.right = right))

def erasureInputs (rule : Rule) : List End :=
  rule.agents.zipIdx.filterMap fun (kind, index) =>
    if kind = .erase then neighborIn rule.wires (.agent index 0) else none

theorem triage_leaf_reads_w :
    (ruleFor .triage .leaf).bind (fun rule => readEvalInput rule 0 8) =
      some (.boundary 0 2) := by decide

theorem triage_stem_reads_x_u :
    (ruleFor .triage .stem).bind (fun rule => readEvalInput rule 1 8) =
      some (.app (.boundary 0 3) (.boundary 1 1)) := by decide

theorem triage_fork_reads_y_u_v :
    (ruleFor .triage .fork).bind (fun rule => readEvalInput rule 2 8) =
      some (.app (.app (.boundary 0 4) (.boundary 1 1))
        (.boundary 1 2)) := by decide

theorem triage_leaf_erases_x_y :
    (ruleFor .triage .leaf).map erasureInputs =
      some [.iface 0 3, .iface 0 4] := by decide

theorem triage_stem_erases_w_y :
    (ruleFor .triage .stem).map erasureInputs =
      some [.iface 0 2, .iface 0 4] := by decide

theorem triage_fork_erases_w_x :
    (ruleFor .triage .fork).map erasureInputs =
      some [.iface 0 2, .iface 0 3] := by decide

theorem triage_outputs_reach_continuation :
    (ruleFor .triage .leaf).map
      (fun rule => rule.hasWire (.agent 0 1) (.iface 0 1)) = some true ∧
    (ruleFor .triage .stem).map
      (fun rule => rule.hasWire (.agent 1 1) (.iface 0 1)) = some true ∧
    (ruleFor .triage .fork).map
      (fun rule => rule.hasWire (.agent 2 1) (.iface 0 1)) = some true := by
  decide

/-- Local semantic bridge from the exported RHS wires to the three abstract
`TriageMachine.Step` branch expressions, for arbitrary source subterms. -/
theorem triage_leaf_builds_w (w x y u v : Syntax) :
    ((ruleFor .triage .leaf).bind (fun rule => readEvalInput rule 0 8)).map
      (Expr.instantiate (triageEnv w x y u v)) = some w := by
  rw [triage_leaf_reads_w]
  rfl

theorem triage_stem_builds_x_u (w x y u v : Syntax) :
    ((ruleFor .triage .stem).bind (fun rule => readEvalInput rule 1 8)).map
      (Expr.instantiate (triageEnv w x y u v)) = some (.app x u) := by
  rw [triage_stem_reads_x_u]
  rfl

theorem triage_fork_builds_y_u_v (w x y u v : Syntax) :
    ((ruleFor .triage .fork).bind (fun rule => readEvalInput rule 2 8)).map
      (Expr.instantiate (triageEnv w x y u v)) =
        some (.app (.app y u) v) := by
  rw [triage_fork_reads_y_u_v]
  rfl

end TriageRuleReadback
