import TriageRawEncoding
import TriageLocalSemantics
import Mathlib.Tactic.IntervalCases

/-! Connect abstract resource tasks to the actual exported interaction rules. -/

namespace TriageResources
open TriageRuleModel (Kind Rule)
open TriageRules

def Raw.eraseRule : Raw → Rule
  | .leaf => rules[13]
  | .stem _ => rules[15]
  | .fork _ _ => rules[17]
  | .app _ _ => rules[19]

def Raw.copyRule : Raw → Rule
  | .leaf => rules[14]
  | .stem _ => rules[16]
  | .fork _ _ => rules[18]
  | .app _ _ => rules[20]

def Task.raw : Task → Raw
  | .erase raw | .copy raw => raw

def Task.kind : Task → Kind
  | .erase _ => .erase
  | .copy _ => .dup

def Task.rule : Task → Rule
  | .erase raw => raw.eraseRule
  | .copy raw => raw.copyRule

def Task.offset : Task → Nat
  | .erase _ => 0
  | .copy _ => 2

theorem Task.rule_mem (task : Task) : task.rule ∈ rules := by
  cases task <;> rename_i raw <;> cases raw <;> simp only [Task.rule, Raw.eraseRule, Raw.copyRule] <;> decide

theorem Task.rule_left (task : Task) : task.rule.left = task.kind := by
  cases task <;> rename_i raw <;> cases raw <;> rfl

theorem Task.rule_right (task : Task) : task.rule.right = task.raw.kind := by
  cases task <;> rename_i raw <;> cases raw <;> rfl

theorem Task.expand_length (task : Task) : task.expand.length = task.raw.children.length := by
  cases task <;> simp [Task.expand, Task.raw]

theorem Task.child_kind {task : Task} {index : Nat} (hi : index < task.expand.length) :
    task.rule.agents[task.offset + index]? = some task.kind := by
  cases task <;> rename_i raw <;> cases raw <;>
    simp only [Task.expand, Raw.children, List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hi
  all_goals interval_cases index <;> rfl

theorem Task.child_raw {task : Task} {index : Nat} {child : Task}
    (hc : task.expand[index]? = some child) : task.raw.children[index]? = some child.raw := by
  cases task <;> simpa [Task.expand, Task.raw, List.getElem?_map] using
    congrArg (Option.map Task.raw) hc

theorem Task.child_same_kind {task : Task} {index : Nat} {child : Task}
    (hc : task.expand[index]? = some child) : child.kind = task.kind := by
  cases task <;> simp only [Task.expand, List.getElem?_map] at hc
  all_goals
    rcases Option.map_eq_some_iff.mp hc with ⟨value, _, heq⟩
    cases heq
    rfl

end TriageResources

namespace TriageResourceRules
open TriageRuleModel (Kind Rule)
open TriageResources TriageRules TriageConcrete TriageBoundary TriageLocalSemantics

theorem child_interface (task : Task) (fresh index : Nat) (hi : index < task.expand.length) :
    layerNeighbor (ruleLayer task.rule fresh) (.iface 1 (index + 1)) =
      some (.real (.agent (fresh + (task.offset + index)) 0)) := by
  cases task <;> rename_i raw <;> cases raw <;>
    simp only [Task.expand, Raw.children, List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hi
  all_goals
    interval_cases index <;>
      simp [Task.rule, Task.offset, Raw.eraseRule, Raw.copyRule, rules, ruleLayer, Node.fromRule, layerNeighbor]

theorem copy_output (raw : Raw) (fresh output : Nat) (ho : output < 2) :
    layerNeighbor (ruleLayer raw.copyRule fresh) (.iface 0 (output + 1)) =
      some (.real (.agent (fresh + output) 0)) := by
  cases raw <;> interval_cases output <;>
    simp [Raw.copyRule, rules, ruleLayer, Node.fromRule, layerNeighbor]

theorem copy_root_kind (raw : Raw) (output : Nat) (ho : output < 2) :
    raw.copyRule.agents[output]? = some raw.kind := by
  cases raw <;> interval_cases output <;> rfl

theorem copy_child_wire (raw : Raw) (index output : Nat)
    (hi : index < raw.children.length) (ho : output < 2) :
    (TriageRuleModel.End.agent (2 + index) (output + 1), .agent output (index + 1)) ∈ raw.copyRule.wires := by
  cases raw <;> simp only [Raw.children, List.length_cons, List.length_nil] at hi
  all_goals interval_cases index <;> interval_cases output <;> simp only [Raw.copyRule] <;> decide

end TriageResourceRules
