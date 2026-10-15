/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageCaseCopy
import TriageCaseErase
import TriageCaseFork

/-! All three Case transitions, with concrete resources and continuations. -/

namespace TriageCaseSimulation
open TriageMachine (Syntax Head Frame)
open TriageConcrete TriageReduction TriageEncoding TriageDispatch TriageContinuations

/-- A concrete exposed head with its exact raw syntax children. -/
def HeadSources (net : Net) (id : Nat) : Head → Prop
  | .leaf => net.kind? id = some .leaf
  | .stem x => net.kind? id = some .stem ∧ Source net [] (.agent id 1) x
  | .fork w x => net.kind? id = some .fork ∧
      Source net [] (.agent id 1) w ∧ Source net [] (.agent id 2) x

def selected (head : Head) (y arg : Syntax) : Syntax :=
  match head with
  | .leaf => y
  | .stem x => .app (.app x arg) (.app y arg)
  | .fork _ _ => arg

def nextFrames (head : Head) (y : Syntax) (frames : List Frame) : List Frame :=
  match head with
  | .fork w x => .triage w x y :: frames
  | _ => frames

/-- Every abstract inspection transition has a finite concrete implementation
in an arbitrary valid represented surrounding net. Copying and erasure are
fully drained, and the entire successor continuation stack is represented. -/
theorem case_simulation {net : Net} (hv : net.valid = true)
    {caseId headId : Nat} {continuation : End} {head : Head} {y arg : Syntax} {frames : List Frame}
    (ha : net.Active caseId headId) (hcase : net.kind? caseId = some .case_)
    (hhead : HeadSources net headId head)
    (hcont : Linked net (.agent caseId 1) continuation)
    (hstack : Continuation net [] continuation frames)
    (hy : Source net [] (.agent caseId 2) y) (harg : Source net [] (.agent caseId 3) arg) :
    ∃ final input, Steps net final ∧ final.valid = true ∧
      EvalTask final (selected head y arg) input ∧
      Continuation final [] input (nextFrames head y frames) ∧
      TriageMachine.Step (.ret head (.inspect y arg :: frames))
        (.eval (selected head y arg) (nextFrames head y frames)) := by
  cases head with
  | leaf =>
      rcases TriageCaseErase.case_leaf hv ha hcase hhead hcont hstack hy harg with
        ⟨final, hsteps, hvalid, heval, hstack⟩
      exact ⟨final, continuation, hsteps, hvalid, heval, hstack, .inspectLeaf⟩
  | stem x =>
      rcases TriageCaseCopy.case_stem hv ha hcase hhead.1 hcont hstack hhead.2 hy harg with
        ⟨final, hsteps, hvalid, heval, hstack⟩
      exact ⟨final, continuation, hsteps, hvalid, heval, hstack, .inspectStem⟩
  | fork w x =>
      rcases TriageCaseFork.case_fork hv ha hcase hhead.1 hcont hstack hhead.2.1 hhead.2.2 hy harg with
        ⟨final, input, hstep, hvalid, heval, hstack⟩
      exact ⟨final, input, Relation.ReflTransGen.single hstep, hvalid, heval, hstack, .inspectFork⟩

/-- The implemented inspection transition is sound for the original TC
reduction relation under every represented continuation. -/
theorem case_tc_sound {net : Net} (hv : net.valid = true)
    {caseId headId : Nat} {continuation : End} {head : Head} {y arg : Syntax} {frames : List Frame}
    (ha : net.Active caseId headId) (hcase : net.kind? caseId = some .case_)
    (hhead : HeadSources net headId head)
    (hcont : Linked net (.agent caseId 1) continuation)
    (hstack : Continuation net [] continuation frames)
    (hy : Source net [] (.agent caseId 2) y) (harg : Source net [] (.agent caseId 3) arg) :
    ∃ final input, Steps net final ∧ final.valid = true ∧
      EvalTask final (selected head y arg) input ∧
      Continuation final [] input (nextFrames head y frames) ∧
      Relation.ReflTransGen Reduces
        (TriageMachine.State.ret head (.inspect y arg :: frames)).toTerm
        (TriageMachine.State.eval (selected head y arg) (nextFrames head y frames)).toTerm := by
  rcases case_simulation hv ha hcase hhead hcont hstack hy harg with
    ⟨final, input, hsteps, hvalid, heval, hstack, hmachine⟩
  exact ⟨final, input, hsteps, hvalid, heval, hstack, hmachine.sound⟩

end TriageCaseSimulation
