/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageCaseSimulation

/-! Concrete structural inspection, including all discarded-branch erasure. -/

namespace TriageDispatchResources
open TriageRuleModel (Kind Rule)
open TriageMachine (Syntax Head Frame)
open TriageResources TriageResourceJobs TriageResourceExecution TriagePendingSources TriageContinuations
open TriageConcrete TriageBoundary TriagePreservation TriageResidual TriageReduction TriageEncoding
open TriageLocalSemantics TriageDispatch
open TriageCaseSimulation (HeadSources)

structure Erasing (net : Net) (jobs : List Job) (terms : List Syntax) : Prop where
  forest : Forest net jobs
  sources : jobs.map (fun job => job.task.raw.toSyntax) = terms
  erasers : ∀ job ∈ jobs, job.task = .erase job.task.raw

theorem two_erases {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right first second firstSlot secondSlot : Nat}
    (hc : (rule, left, right) ∈ net.redexChoices) {a b : Syntax}
    (ha : Source net [] (.agent left (firstSlot + 1)) a)
    (hb : Source net [] (.agent left (secondSlot + 1)) b)
    (hkFirst : (net.replace rule left right).kind? first = some .erase)
    (hkSecond : (net.replace rule left right).kind? second = some .erase)
    (hnewFirst : layerNeighbor (ruleLayer rule net.nextId) (.iface 0 (firstSlot + 1)) =
      some (.real (.agent first 0)))
    (hnewSecond : layerNeighbor (ruleLayer rule net.nextId) (.iface 0 (secondSlot + 1)) =
      some (.real (.agent second 0)))
    (hne : first ≠ second) : ∃ jobs, Erasing (net.replace rule left right) jobs [a, b] := by
  rcases ha.erase_left_aux hv hc hkFirst hnewFirst with ⟨rawA, sourceA, heA, hjA⟩
  rcases hb.erase_left_aux hv hc hkSecond hnewSecond with ⟨rawB, sourceB, heB, hjB⟩
  let jobA : Job := ⟨.erase rawA, first, sourceA⟩
  let jobB : Job := ⟨.erase rawB, second, sourceB⟩
  refine ⟨[jobA, jobB], ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · simpa [jobA, jobB] using hne
  · intro job hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact hjA
    · exact hjB
  · simp [jobA, jobB, Task.raw, heA, heB]
  · intro job hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> rfl

def discarded (head : Head) (w x y : Syntax) : List Syntax :=
  match head with
  | .leaf => [x, y]
  | .stem _ => [w, y]
  | .fork _ _ => [w, x]

theorem head_observed {net : Net} {id : Nat} {head : Head} (h : HeadSources net id head) :
    Observed net id head := by
  cases head with
  | leaf => exact h
  | stem _ => exact ⟨h.1, h.2.rawInput⟩
  | fork _ _ => exact ⟨h.1, h.2.1.rawInput, h.2.2.rawInput⟩

theorem dispatch_choice {net : Net} {triageId headId : Nat} {head : Head}
    (ha : net.Active triageId headId) (ht : net.kind? triageId = some .triage)
    (hh : HeadSources net headId head) : (dispatchRule head, triageId, headId) ∈ net.redexChoices := by
  cases head with
  | leaf => exact Net.redexChoice_complete leafRule_mem ha ht hh
  | stem _ => exact Net.redexChoice_complete stemRule_mem ha ht hh.1
  | fork _ _ => exact Net.redexChoice_complete forkRule_mem ha ht hh.1

/-- Both unused branches become actual erasure jobs with their exact syntax. -/
theorem dispatch_erases {net : Net} (hv : net.valid = true)
    {triageId headId : Nat} {head : Head} {w x y : Syntax}
    (hc : (dispatchRule head, triageId, headId) ∈ net.redexChoices)
    (hw : Source net [] (.agent triageId 2) w)
    (hx : Source net [] (.agent triageId 3) x)
    (hy : Source net [] (.agent triageId 4) y) :
    ∃ jobs, Erasing (net.replace (dispatchRule head) triageId headId) jobs (discarded head w x y) := by
  cases head with
  | leaf =>
      apply two_erases hv hc hx hy
        (Net.replace_created_kind hv hc (index := 1) (kind := .erase) (by rfl))
        (Net.replace_created_kind hv hc (index := 2) (kind := .erase) (by rfl))
      · simp [dispatchRule, leafRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
      · simp [dispatchRule, leafRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
      · omega
  | stem u =>
      apply two_erases hv hc hw hy
        (Net.replace_created_kind hv hc (index := 2) (kind := .erase) (by rfl))
        (Net.replace_created_kind hv hc (index := 3) (kind := .erase) (by rfl))
      · simp [dispatchRule, stemRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
      · simp [dispatchRule, stemRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
      · omega
  | fork u v =>
      apply two_erases hv hc hw hx
        (Net.replace_created_kind hv hc (index := 3) (kind := .erase) (by rfl))
        (Net.replace_created_kind hv hc (index := 4) (kind := .erase) (by rfl))
      · simp [dispatchRule, forkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
      · simp [dispatchRule, forkRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
      · omega

/-- Every abstract triage transition has a concrete implementation that
drains both discarded branches and preserves the entire continuation stack.
The selected raw children are never required to be normalized. -/
theorem dispatch_simulation {net : Net} (hv : net.valid = true)
    {triageId headId : Nat} {continuation : End} {head : Head} {w x y : Syntax} {frames : List Frame}
    (ha : net.Active triageId headId) (ht : net.kind? triageId = some .triage)
    (hh : HeadSources net headId head)
    (hcont : Linked net (.agent triageId 1) continuation)
    (hstack : Continuation net [] continuation frames)
    (hw : Source net [] (.agent triageId 2) w)
    (hx : Source net [] (.agent triageId 3) x)
    (hy : Source net [] (.agent triageId 4) y) :
    ∃ core jobs final,
      core = net.replace (dispatchRule head) triageId headId ∧
      Erasing core jobs (discarded head w x y) ∧
      Run (cost jobs) core jobs final [] ∧ Steps net final ∧ final.valid = true ∧
      EvalTask final (selected head w x y) continuation ∧ Continuation final [] continuation frames ∧
      TriageMachine.Step (.ret head (.triage w x y :: frames)) (.eval (selected head w x y) frames) := by
  have hc := dispatch_choice ha ht hh
  let core := net.replace (dispatchRule head) triageId headId
  have hcore : core.valid = true := Net.redexChoice_preserves_valid hv hc
  rcases dispatch_from_inputs hv ha ht (head_observed hh) (hcont.neighbor (valid_wellFormed hv))
      hw.rawInput hx.rawInput hy.rawInput frames with ⟨hstep, heval, hmachine⟩
  rcases dispatch_erases hv hc hw hx hy with ⟨jobs, hjobs⟩
  have hout := continuation_child_outside (valid_wellFormed hv) ha hcont hstack
  have hstackCore : Continuation core jobs continuation frames :=
    (hstack.replace hv hc hout).jobs_mono (List.nil_subset jobs)
  rcases heval with ⟨evalId, root, hk, hr, hroot, hresult⟩
  have hsource := (Source.of_represents hcore (neighborIn_sound hroot) hr).jobs_mono (List.nil_subset jobs)
  rcases drain_evaluator hcore hjobs.forest hk hsource (neighborIn_sound hresult) hstackCore with
    ⟨final, hrun, hvalid, heval, hstack⟩
  exact ⟨core, jobs, final, rfl, hjobs, hrun,
    Relation.ReflTransGen.head hstep hrun.graph, hvalid, heval, hstack, hmachine⟩

end TriageDispatchResources
