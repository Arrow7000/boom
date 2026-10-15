/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageContinuations

/-! Concrete macro simulation of the argument-erasing Case/Leaf transition. -/

namespace TriageCaseErase
open TriageRuleModel (Kind Rule)
open TriageMachine (Syntax Frame)
open TriageResources TriageRawEncoding TriageResourceJobs TriageResourceExecution
open TriagePendingSources TriageContinuations TriageDispatch
open TriageConcrete TriageBoundary TriagePreservation TriageResidual TriageReduction TriageEncoding TriageLocalSemantics

def caseLeafRule : Rule := TriageRules.rules[7]
theorem caseLeafRule_mem : caseLeafRule ∈ TriageRules.rules := by decide

/-- The actual Case/Leaf interaction evaluates the selected branch, drains
the complete unused argument, and preserves the original continuation. -/
theorem case_leaf {net : Net} (hv : net.valid = true)
    {caseId leafId : Nat} {continuation : End} {y arg : Syntax} {frames : List Frame}
    (ha : net.Active caseId leafId) (hcase : net.kind? caseId = some .case_)
    (hleaf : net.kind? leafId = some .leaf)
    (hcont : Linked net (.agent caseId 1) continuation)
    (hstack : Continuation net [] continuation frames)
    (hy : Source net [] (.agent caseId 2) y) (harg : Source net [] (.agent caseId 3) arg) :
    ∃ final, Steps net final ∧ final.valid = true ∧ EvalTask final y continuation ∧
      Continuation final [] continuation frames := by
  have hc := Net.redexChoice_complete caseLeafRule_mem ha hcase hleaf
  let core := net.replace caseLeafRule caseId leafId
  have hcore : core.valid = true := Net.redexChoice_preserves_valid hv hc
  have hwf := valid_wellFormed hv
  rcases hy with ⟨rawY, hyEq, hy⟩
  rcases harg with ⟨rawArg, _, harg⟩
  rcases hy.complete with ⟨yRoot, hyLink, hyRaw⟩
  rcases harg.complete with ⟨argRoot, hargLink, hargRaw⟩
  rcases hargRaw.principal with ⟨argId, rfl⟩
  have hyOut := child_outside hwf ha (index := 1) hyLink hyRaw
  have hargOut := child_outside hwf ha (index := 2) hargLink hargRaw
  have hyNew := hyRaw.replace hv hc hyOut
  have hargNew := hargRaw.replace hv hc hargOut
  have hyWire : core.neighbor (.agent net.nextId 0) = some yRoot := by
    apply Net.replace_left_aux (slot := 1) hv hc (hyLink.neighbor hwf) hyOut
    simp [caseLeafRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hargWire : core.neighbor (.agent (net.nextId + 1) 0) = some (.agent argId 0) := by
    apply Net.replace_left_aux (slot := 2) hv hc (hargLink.neighbor hwf) hargOut
    simp [caseLeafRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have heval : core.kind? net.nextId = some .eval := by
    simpa using Net.replace_created_kind hv hc (index := 0) (kind := .eval) (by rfl)
  have herase := Net.replace_created_kind hv hc (index := 1) (kind := .erase) (by rfl)
  let job : Job := ⟨.erase rawArg, net.nextId + 1, argId⟩
  have hj : TriageResourceJobs.Realizes core job :=
    ⟨herase, ⟨⟨_, herase⟩, ⟨_, hargNew.kind⟩, hargWire⟩, hargNew⟩
  have hforest : Forest core [job] := ⟨by simp, by
    intro other hm; cases List.mem_singleton.mp hm; exact hj⟩
  have hsource : Source core [job] (.agent net.nextId 0) y :=
    ⟨rawY, hyEq, represented_reads hyNew _ (neighborIn_sound hyWire)⟩
  have hcontOut := continuation_child_outside hwf ha hcont hstack
  have hstackCore : Continuation core [job] continuation frames :=
    (hstack.replace hv hc hcontOut).jobs_mono (List.nil_subset [job])
  have hcontWire : core.neighbor (.agent net.nextId 1) = some continuation := by
    apply Net.replace_left_aux (slot := 0) hv hc (hcont.neighbor hwf) hcontOut
    simp [caseLeafRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  rcases drain_evaluator hcore hforest heval hsource (neighborIn_sound hcontWire) hstackCore with
    ⟨final, hrun, hvalid, hevalFinal, hstackFinal⟩
  exact ⟨final, Relation.ReflTransGen.head (Step.chosen hc) hrun.graph, hvalid, hevalFinal, hstackFinal⟩

end TriageCaseErase
