/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TreeCalculus

/-!
An abstract machine for the TC-like interaction-net example in `netties`.

`Syntax` corresponds to the source agents `Leaf` and `App`. `Head` corresponds
to the three values exposed by `Eval`: `Leaf`, `Stem`, and `Fork`. Its children
are still source syntax. The continuation frames correspond to `Call`, `Case`,
and `Triage` in the net system. Duplication and erasure are implicit here.

This file proves that every abstract machine transition preserves the source
term or performs one of the existing `Term.Reduces` steps. It does not yet
formalize the concrete port graph or prove that each graph interaction
implements an abstract machine transition.
-/

namespace TriageMachine

inductive Syntax where
  | leaf : Syntax
  | app : Syntax → Syntax → Syntax
  deriving Repr, DecidableEq

def Syntax.toTerm : Syntax → Term
  | .leaf => △
  | .app fn arg => fn.toTerm ⬝ arg.toTerm

inductive Head where
  | leaf : Head
  | stem : Syntax → Head
  | fork : Syntax → Syntax → Head
  deriving Repr, DecidableEq

def Head.toTerm : Head → Term
  | .leaf => △
  | .stem x => △ ⬝ x.toTerm
  | .fork x y => △ ⬝ x.toTerm ⬝ y.toTerm

inductive Frame where
  | apply : Syntax → Frame
  | inspect : Syntax → Syntax → Frame
  | triage : Syntax → Syntax → Syntax → Frame
  deriving Repr, DecidableEq

def Frame.plug (frame : Frame) (term : Term) : Term :=
  match frame with
  | .apply arg => term ⬝ arg.toTerm
  | .inspect y arg => △ ⬝ term ⬝ y.toTerm ⬝ arg.toTerm
  | .triage w x y => △ ⬝ (△ ⬝ w.toTerm ⬝ x.toTerm) ⬝ y.toTerm ⬝ term

def plug (term : Term) : List Frame → Term
  | [] => term
  | frame :: frames => plug (frame.plug term) frames

inductive State where
  | eval : Syntax → List Frame → State
  | ret : Head → List Frame → State
  | done : Head → State
  deriving Repr, DecidableEq

def State.toTerm : State → Term
  | .eval source frames => plug source.toTerm frames
  | .ret head frames => plug head.toTerm frames
  | .done head => head.toTerm

inductive Step : State → State → Prop where
  | evalLeaf {frames} :
      Step (.eval .leaf frames) (.ret .leaf frames)
  | evalApp {fn arg frames} :
      Step (.eval (.app fn arg) frames) (.eval fn (.apply arg :: frames))
  | applyLeaf {arg frames} :
      Step (.ret .leaf (.apply arg :: frames)) (.ret (.stem arg) frames)
  | applyStem {x arg frames} :
      Step (.ret (.stem x) (.apply arg :: frames)) (.ret (.fork x arg) frames)
  | applyFork {first second arg frames} :
      Step (.ret (.fork first second) (.apply arg :: frames))
        (.eval first (.inspect second arg :: frames))
  | inspectLeaf {y arg frames} :
      Step (.ret .leaf (.inspect y arg :: frames)) (.eval y frames)
  | inspectStem {x y arg frames} :
      Step (.ret (.stem x) (.inspect y arg :: frames))
        (.eval (.app (.app x arg) (.app y arg)) frames)
  | inspectFork {w x y arg frames} :
      Step (.ret (.fork w x) (.inspect y arg :: frames))
        (.eval arg (.triage w x y :: frames))
  | triageLeaf {w x y frames} :
      Step (.ret .leaf (.triage w x y :: frames)) (.eval w frames)
  | triageStem {w x y u frames} :
      Step (.ret (.stem u) (.triage w x y :: frames))
        (.eval (.app x u) frames)
  | triageFork {w x y u v frames} :
      Step (.ret (.fork u v) (.triage w x y :: frames))
        (.eval (.app (.app y u) v) frames)
  | finish {head} :
      Step (.ret head []) (.done head)

/-- An executable version of the abstract machine's transition table. -/
def next : State → Option State
  | .eval .leaf frames => some (.ret .leaf frames)
  | .eval (.app fn arg) frames => some (.eval fn (.apply arg :: frames))
  | .ret head [] => some (.done head)
  | .ret .leaf (.apply arg :: frames) => some (.ret (.stem arg) frames)
  | .ret (.stem x) (.apply arg :: frames) => some (.ret (.fork x arg) frames)
  | .ret (.fork first second) (.apply arg :: frames) =>
      some (.eval first (.inspect second arg :: frames))
  | .ret .leaf (.inspect y _ :: frames) => some (.eval y frames)
  | .ret (.stem x) (.inspect y arg :: frames) =>
      some (.eval (.app (.app x arg) (.app y arg)) frames)
  | .ret (.fork w x) (.inspect y arg :: frames) =>
      some (.eval arg (.triage w x y :: frames))
  | .ret .leaf (.triage w _ _ :: frames) => some (.eval w frames)
  | .ret (.stem u) (.triage _ x _ :: frames) =>
      some (.eval (.app x u) frames)
  | .ret (.fork u v) (.triage _ _ y :: frames) =>
      some (.eval (.app (.app y u) v) frames)
  | .done _ => none

def run : Nat → State → State
  | 0, state => state
  | fuel + 1, state =>
      match next state with
      | none => state
      | some state' => run fuel state'

def trace : Nat → State → List State
  | 0, state => [state]
  | fuel + 1, state =>
      state :: match next state with
        | none => []
        | some state' => trace fuel state'

theorem Frame.plug_reduces (frame : Frame) (h : Reduces a b) :
    Reduces (frame.plug a) (frame.plug b) := by
  cases frame with
  | apply arg => exact .congr_left h
  | inspect y arg =>
      change Reduces (△ ⬝ a ⬝ y.toTerm ⬝ arg.toTerm)
        (△ ⬝ b ⬝ y.toTerm ⬝ arg.toTerm)
      exact .congr_left (.congr_left (.congr_right h))
  | triage w x y =>
      change Reduces (△ ⬝ (△ ⬝ w.toTerm ⬝ x.toTerm) ⬝ y.toTerm ⬝ a)
        (△ ⬝ (△ ⬝ w.toTerm ⬝ x.toTerm) ⬝ y.toTerm ⬝ b)
      exact .congr_right h

theorem plug_reduces (frames : List Frame) (h : Reduces a b) :
    Reduces (plug a frames) (plug b frames) := by
  induction frames generalizing a b with
  | nil => exact h
  | cons frame frames ih => exact ih (frame.plug_reduces h)

theorem Step.sound {a b : State} (h : Step a b) :
    Relation.ReflTransGen Reduces a.toTerm b.toTerm := by
  cases h
  case evalLeaf => exact .refl
  case evalApp => exact .refl
  case applyLeaf => exact .refl
  case applyStem => exact .refl
  case applyFork => exact .refl
  case inspectFork => exact .refl
  case finish => exact .refl
  case inspectLeaf y arg frames =>
      apply Relation.ReflTransGen.single
      have hr : Reduces (△ ⬝ △ ⬝ y.toTerm ⬝ arg.toTerm) y.toTerm :=
        .rule .one
      exact plug_reduces frames hr
  case inspectStem x y arg frames =>
      apply Relation.ReflTransGen.single
      have hr : Reduces
          (△ ⬝ (△ ⬝ x.toTerm) ⬝ y.toTerm ⬝ arg.toTerm)
          (x.toTerm ⬝ arg.toTerm ⬝ (y.toTerm ⬝ arg.toTerm)) :=
        .rule .two
      exact plug_reduces frames hr
  case triageLeaf w x y frames =>
      apply Relation.ReflTransGen.single
      have hr : Reduces
          (△ ⬝ (△ ⬝ w.toTerm ⬝ x.toTerm) ⬝ y.toTerm ⬝ △)
          w.toTerm := .rule .threeA
      exact plug_reduces frames hr
  case triageStem w x y u frames =>
      apply Relation.ReflTransGen.single
      have hr : Reduces
          (△ ⬝ (△ ⬝ w.toTerm ⬝ x.toTerm) ⬝ y.toTerm ⬝ (△ ⬝ u.toTerm))
          (x.toTerm ⬝ u.toTerm) := .rule .threeB
      exact plug_reduces frames hr
  case triageFork w x y u v frames =>
      apply Relation.ReflTransGen.single
      have hr : Reduces
          (△ ⬝ (△ ⬝ w.toTerm ⬝ x.toTerm) ⬝ y.toTerm ⬝ (△ ⬝ u.toTerm ⬝ v.toTerm))
          (y.toTerm ⬝ u.toTerm ⬝ v.toTerm) := .rule .threeC
      exact plug_reduces frames hr

theorem Step.deterministic {a b c : State}
    (h₁ : Step a b) (h₂ : Step a c) : b = c := by
  cases h₁ <;> cases h₂ <;> rfl

theorem Step.next {a b : State} (h : Step a b) : next a = some b := by
  cases h <;> rfl

theorem next_sound {a b : State} (h : next a = some b) : Step a b := by
  cases a with
  | eval source frames =>
      cases source <;> simp only [next, Option.some.injEq] at h <;>
        subst b <;> constructor
  | ret head frames =>
      cases frames with
      | nil =>
          simp only [next, Option.some.injEq] at h
          subst b
          exact .finish
      | cons frame frames =>
          cases frame <;> cases head <;>
            simp only [next, Option.some.injEq] at h <;>
            subst b <;> constructor
  | done head => simp only [next, reduceCtorEq] at h

/-- Only an exposed head form can select a triage branch. In particular, an
`App` source term cannot be matched by triage before its head is evaluated. -/
theorem Step.triage_cases {head : Head} {w x y : Syntax} {frames : List Frame}
    {next : State} (h : Step (.ret head (.triage w x y :: frames)) next) :
    (head = .leaf ∧ next = .eval w frames) ∨
    (∃ u, head = .stem u ∧ next = .eval (.app x u) frames) ∨
    (∃ u v, head = .fork u v ∧ next = .eval (.app (.app y u) v) frames) := by
  cases h <;> simp

abbrev Steps := Relation.ReflTransGen Step

theorem run_sound (fuel : Nat) (state : State) :
    Steps state (run fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      unfold run
      cases h : next state with
      | none => exact .refl
      | some nextState =>
          exact Relation.ReflTransGen.trans
            (Relation.ReflTransGen.single (next_sound h)) (ih nextState)

theorem Steps.sound {a b : State} (h : Steps a b) :
    Relation.ReflTransGen Reduces a.toTerm b.toTerm := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact Relation.ReflTransGen.trans ih step.sound

theorem completed_eval_sound {source : Syntax} {head : Head}
    (h : Steps (.eval source []) (.done head)) :
    Relation.ReflTransGen Reduces source.toTerm head.toTerm :=
  Steps.sound h

def stem (x : Syntax) : Syntax := .app .leaf x
def fork (x y : Syntax) : Syntax := .app (stem x) y
def triage (w x y arg : Syntax) : Syntax := .app (fork (fork w x) y) arg

def pending : Syntax := .app (fork .leaf (stem .leaf)) .leaf
def demo : Syntax := triage .leaf .leaf (stem .leaf) (fork pending .leaf)

def isForkTriage : State → Bool
  | .ret (.fork _ _) (.triage _ _ _ :: _) => true
  | _ => false

def isPendingEval : State → Bool
  | .eval source _ => decide (source = pending)
  | _ => false

def triageBeforePending : List State → Bool
  | [] => false
  | state :: rest =>
      (isForkTriage state && rest.any isPendingEval) || triageBeforePending rest

/-- This is the source term in netties' "Triage: inspect, then run a child"
example. The abstract machine reaches the same exposed stem. -/
theorem demo_result : run 100 (.eval demo []) = .done (.stem .leaf) := by
  decide

theorem demo_observes_before_running_child :
    triageBeforePending (trace 100 (.eval demo [])) = true := by
  decide

theorem demo_tc_sound :
    Relation.ReflTransGen Reduces demo.toTerm (Head.stem .leaf).toTerm := by
  have h := run_sound 100 (.eval demo [])
  rw [demo_result] at h
  exact completed_eval_sound h

end TriageMachine
