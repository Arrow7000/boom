import Mathlib.Tactic.Tauto

/-!
Administrative copy and erase work for finite syntax trees. The four
constructors are exactly the agent kinds handled by the exported `Dup` and
`Erase` rules. A task on a constructor expands to one task per child; the
task's own node disappears. This module proves that any scheduling of these
administrative tasks terminates. It does not model the produced copied nets.
-/

namespace TriageResources

inductive Raw where
  | leaf : Raw
  | stem : Raw → Raw
  | fork : Raw → Raw → Raw
  | app : Raw → Raw → Raw
  deriving Repr, DecidableEq

def Raw.children : Raw → List Raw
  | .leaf => []
  | .stem child => [child]
  | .fork left right | .app left right => [left, right]

def Raw.size : Raw → Nat
  | .leaf => 1
  | .stem child => 1 + child.size
  | .fork left right | .app left right => 1 + left.size + right.size

theorem Raw.size_children (raw : Raw) :
    raw.size = 1 + (raw.children.map Raw.size).sum := by
  cases raw <;> simp [Raw.size, Raw.children, Nat.add_assoc]

inductive Task where
  | erase : Raw → Task
  | copy : Raw → Task
  deriving Repr, DecidableEq

def Task.size : Task → Nat
  | .erase raw | .copy raw => raw.size

def Task.expand : Task → List Task
  | .erase raw => raw.children.map Task.erase
  | .copy raw => raw.children.map Task.copy

theorem Task.expand_size (task : Task) :
    (task.expand.map Task.size).sum + 1 = task.size := by
  cases task with
  | erase raw =>
      simpa [Task.expand, Task.size, List.map_map, Function.comp_def,
        Nat.add_comm] using (Raw.size_children raw).symm
  | copy raw =>
      simpa [Task.expand, Task.size, List.map_map, Function.comp_def,
        Nat.add_comm] using (Raw.size_children raw).symm

def total (tasks : List Task) : Nat := (tasks.map Task.size).sum

/-- Pick any pending administrative task and replace it by its child tasks. -/
inductive Step : List Task → List Task → Prop where
  | expandOne (before after : List Task) (task : Task) :
      Step (before ++ task :: after) (before ++ task.expand ++ after)

theorem Step.decreases {before after : List Task} (h : Step before after) :
    total after < total before := by
  cases h
  rename_i front back item
  have hsize := Task.expand_size item
  simp only [total, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons] at *
  omega

theorem Step.wellFounded : WellFounded (fun next current => Step current next) := by
  exact Subrelation.wf (fun h => Step.decreases h) (measure total).wf

end TriageResources
