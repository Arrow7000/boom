/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageContinuations

/-! Concrete macro simulation of the argument-copying Case/Stem transition. -/

namespace TriageCaseCopy
open TriageRuleModel (Kind Rule)
open TriageMachine (Syntax Frame)
open TriageResources TriageRawEncoding TriageResourceRules TriageResourceJobs TriageResourceExecution
open TriagePendingSources TriageContinuations TriageDispatch
open TriageConcrete TriageBoundary TriagePreservation TriageResidual TriageReduction TriageEncoding TriageLocalSemantics

def caseStemRule : Rule := TriageRules.rules[8]
theorem caseStemRule_mem : caseStemRule ∈ TriageRules.rules := by decide

theorem reads_app {net : Net} {jobs : List Job} {demand : End} {id : Nat} {fn arg : Raw}
    (hl : Linked net demand (.agent id 0)) (hk : net.kind? id = some .app)
    (hf : Reads net jobs (.agent id 1) fn) (ha : Reads net jobs (.agent id 2) arg) :
    Reads net jobs demand (.app fn arg) := by
  refine Reads.node hl hk ?_
  intro index child hget
  cases index with
  | zero => cases Option.some.inj hget; exact hf
  | succ index =>
      cases index with
      | zero => cases Option.some.inj hget; exact ha
      | succ index => simp [Raw.children] at hget

/-- The actual Case/Stem interaction, followed by finite concrete copying,
starts evaluation of `(x arg) (y arg)` with the original continuation stack.
There is no size or normalization assumption on the raw argument. -/
theorem case_stem {net : Net} (hv : net.valid = true)
    {caseId stemId : Nat} {continuation : End} {x y arg : Syntax} {frames : List Frame}
    (ha : net.Active caseId stemId) (hcase : net.kind? caseId = some .case_)
    (hstem : net.kind? stemId = some .stem)
    (hcont : Linked net (.agent caseId 1) continuation)
    (hstack : Continuation net [] continuation frames)
    (hx : Source net [] (.agent stemId 1) x) (hy : Source net [] (.agent caseId 2) y)
    (harg : Source net [] (.agent caseId 3) arg) :
    ∃ final, Steps net final ∧ final.valid = true ∧
      EvalTask final (.app (.app x arg) (.app y arg)) continuation ∧
      Continuation final [] continuation frames := by
  have hc := Net.redexChoice_complete caseStemRule_mem ha hcase hstem
  let core := net.replace caseStemRule caseId stemId
  have hcore : core.valid = true := Net.redexChoice_preserves_valid hv hc
  have hwf := valid_wellFormed hv
  rcases hx with ⟨rawX, hxEq, hx⟩
  rcases hy with ⟨rawY, hyEq, hy⟩
  rcases harg with ⟨rawArg, hargEq, harg⟩
  rcases hx.complete with ⟨xRoot, hxLink, hxRaw⟩
  rcases hy.complete with ⟨yRoot, hyLink, hyRaw⟩
  rcases harg.complete with ⟨argRoot, hargLink, hargRaw⟩
  rcases hargRaw.principal with ⟨argId, rfl⟩
  have hxOut := child_outside hwf ha (index := 0) hxLink hxRaw
  have hyOut := child_outside hwf ha (index := 1) hyLink hyRaw
  have hargOut := child_outside hwf ha (index := 2) hargLink hargRaw
  have hxNew := hxRaw.replace hv hc hxOut
  have hyNew := hyRaw.replace hv hc hyOut
  have hargNew := hargRaw.replace hv hc hargOut
  have hxWire : core.neighbor (.agent (net.nextId + 1) 1) = some xRoot := by
    apply Net.replace_right_aux hv hc (hxLink.neighbor hwf) hxOut
    simp [caseStemRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hyWire : core.neighbor (.agent (net.nextId + 2) 1) = some yRoot := by
    apply Net.replace_left_aux (slot := 1) hv hc (hyLink.neighbor hwf) hyOut
    simp [caseStemRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hargWire : core.neighbor (.agent net.nextId 0) = some (.agent argId 0) := by
    apply Net.replace_left_aux (slot := 2) hv hc (hargLink.neighbor hwf) hargOut
    simp [caseStemRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  have hdup := Net.replace_created_kind hv hc (index := 0) (kind := .dup) (by rfl)
  have happ1 := Net.replace_created_kind hv hc (index := 1) (kind := .app) (by rfl)
  have happ2 := Net.replace_created_kind hv hc (index := 2) (kind := .app) (by rfl)
  have happ3 := Net.replace_created_kind hv hc (index := 3) (kind := .app) (by rfl)
  have heval := Net.replace_created_kind hv hc (index := 4) (kind := .eval) (by rfl)
  let job : Job := ⟨.copy rawArg, net.nextId, argId⟩
  have hj : TriageResourceJobs.Realizes core job := by
    have hd : core.kind? net.nextId = some .dup := by simpa using hdup
    exact ⟨hd, ⟨⟨_, hd⟩, ⟨_, hargNew.kind⟩, hargWire⟩, hargNew⟩
  have hforest : Forest core [job] := ⟨by simp, by
    intro other hm; cases List.mem_singleton.mp hm; exact hj⟩
  have hxReads : Reads core [job] (.agent (net.nextId + 1) 1) rawX :=
    represented_reads hxNew _ (neighborIn_sound hxWire)
  have hyReads : Reads core [job] (.agent (net.nextId + 2) 1) rawY :=
    represented_reads hyNew _ (neighborIn_sound hyWire)
  have hdup1 := Net.replace_internal_wire hv hc
    (first := 0) (firstSlot := 1) (second := 1) (secondSlot := 2) (by decide)
  have hdup2 := Net.replace_internal_wire hv hc
    (first := 0) (firstSlot := 2) (second := 2) (secondSlot := 2) (by decide)
  have harg1 : Reads core [job] (.agent (net.nextId + 1) 2) rawArg :=
    Reads.pending (List.mem_singleton_self _) rfl (by decide : 0 < 2)
      (by simpa using (neighborIn_sound hdup1).symm)
  have harg2 : Reads core [job] (.agent (net.nextId + 2) 2) rawArg :=
    Reads.pending (List.mem_singleton_self _) rfl (by decide : 1 < 2)
      (by simpa using (neighborIn_sound hdup2).symm)
  have hw31 := Net.replace_internal_wire hv hc
    (first := 3) (firstSlot := 1) (second := 1) (secondSlot := 0) (by decide)
  have hw32 := Net.replace_internal_wire hv hc
    (first := 3) (firstSlot := 2) (second := 2) (secondSlot := 0) (by decide)
  have hw43 := Net.replace_internal_wire hv hc
    (first := 4) (firstSlot := 0) (second := 3) (secondSlot := 0) (by decide)
  have hleft := reads_app (neighborIn_sound hw31) happ1 hxReads harg1
  have hright := reads_app (neighborIn_sound hw32) happ2 hyReads harg2
  have hsource := reads_app (neighborIn_sound hw43) happ3 hleft hright
  have hcontOut := continuation_child_outside hwf ha hcont hstack
  have hstackCore : Continuation core [] continuation frames := hstack.replace hv hc hcontOut
  have hcontWire : core.neighbor (.agent (net.nextId + 4) 1) = some continuation := by
    apply Net.replace_left_aux (slot := 0) hv hc (hcont.neighbor hwf) hcontOut
    simp [caseStemRule, TriageRules.rules, ruleLayer, Node.fromRule, layerNeighbor]
  rcases materialize hcore hforest with ⟨final, hrun, hvalid, hreads⟩
  have hanchor : Anchor core (.agent (net.nextId + 4) 0) := .agent heval (by decide)
  rcases hreads _ _ hanchor hsource with ⟨root, hrootLink, hrootRaw⟩
  have hevalFinal := run_control_kind hrun hcore heval (by decide)
  have hcontFinal := run_linked hrun hcore (Anchor.agent heval (by decide)) hstackCore.anchor
    (neighborIn_sound hcontWire)
  have hstackFinal := run_continuation hrun hcore hforest
    (hstackCore.jobs_mono (List.nil_subset [job]))
  refine ⟨final, Relation.ReflTransGen.head (Step.chosen hc) hrun.graph, hvalid, ?_, hstackFinal⟩
  refine ⟨net.nextId + 4, root, hevalFinal, ?_, hrootLink.neighbor (valid_wellFormed hvalid),
    hcontFinal.neighbor (valid_wellFormed hvalid)⟩
  simpa only [Raw.toSyntax, hxEq, hyEq, hargEq] using hrootRaw.represents

end TriageCaseCopy
