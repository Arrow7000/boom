import TriageMachine

/-!
Structural inspection by the abstract evaluator. The fixed prefix of an
encoded triage call reaches the argument evaluator without inspecting any of
the branch programs or the argument's children. The three following theorems
show that constructor choice and child extraction work for arbitrary syntax.
These are machine-level statements; the whole-net simulation is separate.
-/

namespace TriageInspection
open TriageMachine

theorem triage_reaches_arg (w x y arg : Syntax) (frames : List Frame) :
    run 13 (.eval (triage w x y arg) frames) =
      .eval arg (.triage w x y :: frames) := by
  rfl

/-- An exposed leaf chooses the first branch. The other branches are never
evaluated during this prefix. -/
theorem triage_leaf_run (w x y : Syntax) (frames : List Frame) :
    run 15 (.eval (triage w x y .leaf) frames) = .eval w frames := by
  rfl

/-- An exposed stem passes its unexamined child to the second branch. -/
theorem triage_stem_run (w x y u : Syntax) (frames : List Frame) :
    run 17 (.eval (triage w x y (stem u)) frames) =
      .eval (.app x u) frames := by
  rfl

/-- An exposed fork passes both unexamined children to the third branch. -/
theorem triage_fork_run (w x y u v : Syntax) (frames : List Frame) :
    run 19 (.eval (triage w x y (fork u v)) frames) =
      .eval (.app (.app y u) v) frames := by
  rfl

theorem triage_leaf_steps (w x y : Syntax) (frames : List Frame) :
    Steps (.eval (triage w x y .leaf) frames) (.eval w frames) := by
  simpa only [triage_leaf_run] using
    run_sound 15 (.eval (triage w x y .leaf) frames)

theorem triage_stem_steps (w x y u : Syntax) (frames : List Frame) :
    Steps (.eval (triage w x y (stem u)) frames) (.eval (.app x u) frames) := by
  simpa only [triage_stem_run] using
    run_sound 17 (.eval (triage w x y (stem u)) frames)

theorem triage_fork_steps (w x y u v : Syntax) (frames : List Frame) :
    Steps (.eval (triage w x y (fork u v)) frames)
      (.eval (.app (.app y u) v) frames) := by
  simpa only [triage_fork_run] using
    run_sound 19 (.eval (triage w x y (fork u v)) frames)

/-- The static values are finite, unlabeled trees. Their constructors are
represented by the three TC head forms, recursively at each child. -/
inductive Tree where
  | leaf : Tree
  | stem : Tree → Tree
  | fork : Tree → Tree → Tree
  deriving Repr, DecidableEq

def Tree.encode : Tree → Syntax
  | .leaf => .leaf
  | .stem child => TriageMachine.stem child.encode
  | .fork left right => TriageMachine.fork left.encode right.encode

def Tree.head : Tree → Head
  | .leaf => .leaf
  | .stem child => .stem child.encode
  | .fork left right => .fork left.encode right.encode

def Tree.headSteps : Tree → Nat
  | .leaf => 1
  | .stem _ => 3
  | .fork _ _ => 5

/-- Exposing a static tree's root has a fixed cost independent of its
children; their encoding remains intact under the head constructor. -/
theorem Tree.expose_head (tree : Tree) (frames : List Frame) :
    run tree.headSteps (.eval tree.encode frames) = .ret tree.head frames := by
  cases tree <;> rfl

/-- Distinct static trees have distinct source encodings. -/
theorem Tree.encode_injective : Function.Injective Tree.encode := by
  intro first second h
  induction first generalizing second with
  | leaf => cases second <;> simp_all [Tree.encode, TriageMachine.stem, TriageMachine.fork]
  | stem child ih =>
      cases second with
      | leaf => simp [Tree.encode, TriageMachine.stem] at h
      | stem other =>
          have hc : child.encode = other.encode := by
            simpa [Tree.encode, TriageMachine.stem] using h
          exact congrArg Tree.stem (ih hc)
      | fork left right =>
          simp [Tree.encode, TriageMachine.stem, TriageMachine.fork] at h
  | fork left right ihLeft ihRight =>
      cases second with
      | leaf => simp [Tree.encode, TriageMachine.fork] at h
      | stem other =>
          simp [Tree.encode, TriageMachine.stem, TriageMachine.fork] at h
      | fork otherLeft otherRight =>
          have hc : left.encode = otherLeft.encode ∧
              right.encode = otherRight.encode := by
            simpa [Tree.encode, TriageMachine.stem, TriageMachine.fork] using h
          exact congrArg₂ Tree.fork (ihLeft hc.1) (ihRight hc.2)

def Tree.branch (tree : Tree) (w x y : Syntax) : Syntax :=
  match tree with
  | .leaf => w
  | .stem child => .app x child.encode
  | .fork left right => .app (.app y left.encode) right.encode

/-- Every finite static tree admits a root inspection. The selected branch
receives its exact encoded children, with no reduction inside them. -/
theorem Tree.inspect (tree : Tree) (w x y : Syntax) (frames : List Frame) :
    Steps (.eval (triage w x y tree.encode) frames)
      (.eval (tree.branch w x y) frames) := by
  cases tree with
  | leaf => exact triage_leaf_steps w x y frames
  | stem child => exact triage_stem_steps w x y child.encode frames
  | fork left right =>
      exact triage_fork_steps w x y left.encode right.encode frames

theorem Tree.inspect_sound (tree : Tree) (w x y : Syntax) (frames : List Frame) :
    Relation.ReflTransGen Reduces
      (plug (triage w x y tree.encode).toTerm frames)
      (plug (tree.branch w x y).toTerm frames) := by
  exact Steps.sound (tree.inspect w x y frames)

end TriageInspection
