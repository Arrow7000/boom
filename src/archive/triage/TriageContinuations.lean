/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriagePendingSources
import TriageDispatch

/-! Concrete continuation stacks, including arguments with pending copies. -/

namespace TriageContinuations
open TriageRuleModel (Kind)
open TriageMachine (Syntax Frame)
open TriageResources TriageRawEncoding TriageResourceJobs TriageResourceExecution TriagePendingSources
open TriageConcrete TriageBoundary TriagePreservation TriageResidual TriageReduction TriageEncoding TriageLocalSemantics

def Source (net : Net) (jobs : List Job) (demand : End) (term : Syntax) : Prop :=
  ∃ raw, raw.toSyntax = term ∧ Reads net jobs demand raw

theorem Source.complete {net : Net} {demand : End} {term : Syntax} (h : Source net [] demand term) :
    ∃ root, Linked net demand root ∧ Represents net root term := by
  rcases h with ⟨raw, rfl, hr⟩
  rcases hr.complete with ⟨root, hl, hr⟩
  exact ⟨root, hl, hr.represents⟩

theorem Source.of_represents {net : Net} (hv : net.valid = true)
    {demand root : End} {term : Syntax} (hl : Linked net demand root) (hr : Represents net root term) :
    Source net [] demand term := by
  rcases hr.raw hv with ⟨raw, he, hraw⟩
  exact ⟨raw, he, represented_reads hraw _ hl⟩

theorem Source.rawInput {net : Net} {id slot : Nat} {term : Syntax}
    (h : Source net [] (.agent id slot) term) : TriageDispatch.RawInput net id slot term := h.complete

theorem Source.jobs_mono {net : Net} {first second : List Job} (hs : first ⊆ second)
    {demand : End} {term : Syntax} (h : Source net first demand term) : Source net second demand term := by
  rcases h with ⟨raw, he, hr⟩
  exact ⟨raw, he, hr.jobs_mono hs⟩

inductive Continuation (net : Net) (jobs : List Job) : End → List Frame → Prop where
  | halt : Continuation net jobs (.free 0) []
  | apply {id : Nat} {rest : End} {arg : Syntax} {frames : List Frame} :
      net.kind? id = some .call → Linked net (.agent id 1) rest → Source net jobs (.agent id 2) arg →
      Continuation net jobs rest frames → Continuation net jobs (.agent id 0) (.apply arg :: frames)
  | inspect {id : Nat} {rest : End} {y arg : Syntax} {frames : List Frame} :
      net.kind? id = some .case_ → Linked net (.agent id 1) rest →
      Source net jobs (.agent id 2) y → Source net jobs (.agent id 3) arg →
      Continuation net jobs rest frames → Continuation net jobs (.agent id 0) (.inspect y arg :: frames)
  | triage {id : Nat} {rest : End} {w x y : Syntax} {frames : List Frame} :
      net.kind? id = some .triage → Linked net (.agent id 1) rest →
      Source net jobs (.agent id 2) w → Source net jobs (.agent id 3) x → Source net jobs (.agent id 4) y →
      Continuation net jobs rest frames → Continuation net jobs (.agent id 0) (.triage w x y :: frames)

theorem Continuation.anchor {net : Net} {jobs : List Job} {input : End} {frames : List Frame}
    (h : Continuation net jobs input frames) : Anchor net input := by
  cases h with
  | halt => exact .free 0
  | apply hk _ _ _ => exact .agent hk (by decide)
  | inspect hk _ _ _ _ => exact .agent hk (by decide)
  | triage hk _ _ _ _ _ => exact .agent hk (by decide)

theorem Continuation.jobs_mono {net : Net} {first second : List Job} (hs : first ⊆ second)
    {input : End} {frames : List Frame} (h : Continuation net first input frames) :
    Continuation net second input frames := by
  induction h with
  | halt => exact .halt
  | apply hk hl ha _ ih => exact .apply hk hl (ha.jobs_mono hs) ih
  | inspect hk hl hy ha _ ih => exact .inspect hk hl (hy.jobs_mono hs) (ha.jobs_mono hs) ih
  | triage hk hl hw hx hy _ ih => exact .triage hk hl (hw.jobs_mono hs) (hx.jobs_mono hs) (hy.jobs_mono hs) ih

theorem control_progress {net target : Net} {jobs after : List Job}
    (hv : net.valid = true) (hp : Progress net jobs target after) {id : Nat} {kind : Kind}
    (hk : net.kind? id = some kind) (hm : kind ∈ controlKinds) : target.kind? id = some kind := by
  rcases hp.selected with ⟨before, job, suffix, children, rfl, rfl, rfl, hj, _, _⟩
  have hout := (Anchor.agent (slot := 0) hk hm).outside hj
  have hid : id ≠ job.control ∧ id ≠ job.source := by simpa [belongs] using hout
  exact Net.replace_retains_kind hv job.task.rule hk hid.1 hid.2

theorem linked_progress {net target : Net} {jobs after : List Job}
    (hp : Progress net jobs target after) {a b : End}
    (ha : Anchor net a) (hb : Anchor net b) (hl : Linked net a b) : Linked target a b := by
  rcases hp.selected with ⟨before, job, suffix, children, rfl, rfl, rfl, hj, _, _⟩
  exact hl.replace job.task.rule job.control job.source (ha.outside hj) (hb.outside hj)

theorem Source.progress {net target : Net} {jobs after : List Job}
    (hv : net.valid = true) (hf : Forest net jobs) (hp : Progress net jobs target after)
    {demand : End} {term : Syntax} (ha : Anchor net demand) (h : Source net jobs demand term) :
    Source target after demand term := by
  rcases h with ⟨raw, he, hr⟩
  exact ⟨raw, he, reads_progress hv hf hp ha hr⟩

/-- Administrative execution preserves the entire continuation stack and
all its logical argument sources, including arguments being copied. -/
theorem Continuation.progress {net target : Net} {jobs after : List Job}
    (hv : net.valid = true) (hf : Forest net jobs) (hp : Progress net jobs target after)
    {input : End} {frames : List Frame} (h : Continuation net jobs input frames) :
    Continuation target after input frames := by
  induction h with
  | halt => exact .halt
  | apply hk hl harg hrest ih =>
      exact .apply (control_progress hv hp hk (by decide))
        (linked_progress hp (.agent hk (by decide)) hrest.anchor hl)
        (harg.progress hv hf hp (.agent hk (by decide))) ih
  | inspect hk hl hy harg hrest ih =>
      exact .inspect (control_progress hv hp hk (by decide))
        (linked_progress hp (.agent hk (by decide)) hrest.anchor hl)
        (hy.progress hv hf hp (.agent hk (by decide)))
        (harg.progress hv hf hp (.agent hk (by decide))) ih
  | triage hk hl hw hx hy hrest ih =>
      exact .triage (control_progress hv hp hk (by decide))
        (linked_progress hp (.agent hk (by decide)) hrest.anchor hl)
        (hw.progress hv hf hp (.agent hk (by decide)))
        (hx.progress hv hf hp (.agent hk (by decide)))
        (hy.progress hv hf hp (.agent hk (by decide))) ih

theorem run_continuation {count : Nat} {net final : Net} {jobs after : List Job}
    (hrun : Run count net jobs final after) (hv : net.valid = true) (hf : Forest net jobs)
    {input : End} {frames : List Frame} (h : Continuation net jobs input frames) :
    Continuation final after input frames := by
  revert hv hf h
  induction hrun with
  | zero => intro _ _ h; exact h
  | step hp _ ih =>
      intro hv hf h
      exact ih (hp.graph.preserves_valid hv) hp.forest (h.progress hv hf hp)

theorem Source.run {count : Nat} {net final : Net} {jobs after : List Job}
    (hrun : Run count net jobs final after) (hv : net.valid = true) (hf : Forest net jobs)
    {demand : End} {term : Syntax} (ha : Anchor net demand) (h : Source net jobs demand term) :
    Source final after demand term := by
  rcases h with ⟨raw, he, hr⟩
  exact ⟨raw, he, run_reads hrun hv hf ha hr⟩

theorem run_control_kind {count : Nat} {net final : Net} {jobs after : List Job}
    (hrun : Run count net jobs final after) (hv : net.valid = true) {id : Nat} {kind : Kind}
    (hk : net.kind? id = some kind) (hm : kind ∈ controlKinds) : final.kind? id = some kind := by
  revert hv hk
  induction hrun with
  | zero => intro _ hk; exact hk
  | step hp _ ih => intro hv hk; exact ih (hp.graph.preserves_valid hv) (control_progress hv hp hk hm)

theorem run_linked {count : Nat} {net final : Net} {jobs after : List Job}
    (hrun : Run count net jobs final after) (hv : net.valid = true) {a b : End}
    (ha : Anchor net a) (hb : Anchor net b) (hl : Linked net a b) : Linked final a b := by
  revert hv ha hb hl
  induction hrun with
  | zero => intro _ _ _ hl; exact hl
  | step hp _ ih =>
      intro hv ha hb hl
      exact ih (hp.graph.preserves_valid hv) (anchor_progress hv hp ha) (anchor_progress hv hp hb)
        (linked_progress hp ha hb hl)

theorem drain_continuation {net : Net} (hv : net.valid = true) {jobs : List Job} (hf : Forest net jobs)
    {input : End} {frames : List Frame} (h : Continuation net jobs input frames) :
    ∃ final, Run (cost jobs) net jobs final [] ∧ final.valid = true ∧ Continuation final [] input frames := by
  rcases drain hv hf with ⟨final, hrun, hvalid⟩
  exact ⟨final, hrun, hvalid, run_continuation hrun hv hf h⟩

/-- Finish all represented resource jobs around a live evaluator. Its source,
result wire, and complete continuation survive together. -/
theorem drain_evaluator {net : Net} (hv : net.valid = true) {jobs : List Job} (hf : Forest net jobs)
    {evalId : Nat} {continuation : End} {term : Syntax} {frames : List Frame}
    (hk : net.kind? evalId = some .eval) (hs : Source net jobs (.agent evalId 0) term)
    (hl : Linked net (.agent evalId 1) continuation) (hc : Continuation net jobs continuation frames) :
    ∃ final, Run (cost jobs) net jobs final [] ∧ final.valid = true ∧
      TriageDispatch.EvalTask final term continuation ∧ Continuation final [] continuation frames := by
  rcases drain hv hf with ⟨final, hrun, hvalid⟩
  have hsource := hs.run hrun hv hf (.agent hk (by decide))
  rcases hsource.complete with ⟨root, hroot, hr⟩
  have hkind := run_control_kind hrun hv hk (by decide)
  have hlink := run_linked hrun hv (.agent hk (by decide)) hc.anchor hl
  exact ⟨final, hrun, hvalid,
    ⟨evalId, root, hkind, hr, hroot.neighbor (valid_wellFormed hvalid),
      hlink.neighbor (valid_wellFormed hvalid)⟩,
    run_continuation hrun hv hf hc⟩

theorem Continuation.principal {net : Net} {jobs : List Job} {input : End} {frames : List Frame}
    (h : Continuation net jobs input frames) : input = .free 0 ∨ ∃ id, input = .agent id 0 := by
  cases h with
  | halt => exact Or.inl rfl
  | apply | inspect | triage => exact Or.inr ⟨_, rfl⟩

theorem continuation_child_outside {net : Net} (hwf : net.wellFormed = true)
    {left right parent : Nat} {input : End} {frames : List Frame}
    (ha : net.Active left right) (hl : Linked net (.agent parent 1) input)
    (h : Continuation net [] input frames) : belongs left right input = false := by
  rcases h.principal with rfl | ⟨id, rfl⟩
  · rfl
  · rcases auxiliary_child_not_active hwf ha (by decide : 1 ≠ 0) hl with ⟨h1, h2⟩
    simp [belongs, h1, h2]

theorem Source.replace_aux {net : Net} (hv : net.valid = true)
    {rule : TriageRuleModel.Rule} {left right parent index : Nat}
    (hc : (rule, left, right) ∈ net.redexChoices)
    {term : Syntax} (h : Source net [] (.agent parent (index + 1)) term)
    (hout : belongs left right (.agent parent 0) = false) :
    Source (net.replace rule left right) [] (.agent parent (index + 1)) term := by
  rcases h with ⟨raw, heq, hr⟩
  rcases hr.complete with ⟨root, hl, hraw⟩
  have ha := (Net.redexChoice_sound (valid_wellFormed hv) hc).2.1
  have hchild := child_outside (valid_wellFormed hv) ha hl hraw
  have hnext := hraw.replace hv hc hchild
  have hlink := hl.replace rule left right hout hchild
  exact ⟨raw, heq, represented_reads hnext _ hlink⟩

theorem Source.replace_left_aux {net : Net} (hv : net.valid = true)
    {rule : TriageRuleModel.Rule} {left right slot : Nat}
    (hc : (rule, left, right) ∈ net.redexChoices) {term : Syntax} {demand : End}
    (h : Source net [] (.agent left (slot + 1)) term)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 0 (slot + 1)) = some (.real demand)) :
    Source (net.replace rule left right) [] demand term := by
  rcases h with ⟨raw, heq, hr⟩
  rcases hr.complete with ⟨root, hl, hraw⟩
  have ha := (Net.redexChoice_sound (valid_wellFormed hv) hc).2.1
  have hout := child_outside (valid_wellFormed hv) ha hl hraw
  have hnext := hraw.replace hv hc hout
  have hlink := Net.replace_left_aux hv hc (hl.neighbor (valid_wellFormed hv)) hout hnew
  exact ⟨raw, heq, represented_reads hnext _ (neighborIn_sound hlink)⟩

theorem Source.replace_right_aux {net : Net} (hv : net.valid = true)
    {rule : TriageRuleModel.Rule} {left right slot : Nat}
    (hc : (rule, left, right) ∈ net.redexChoices) {term : Syntax} {demand : End}
    (h : Source net [] (.agent right (slot + 1)) term)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 1 (slot + 1)) = some (.real demand)) :
    Source (net.replace rule left right) [] demand term := by
  rcases h with ⟨raw, heq, hr⟩
  rcases hr.complete with ⟨root, hl, hraw⟩
  have ha := (Net.redexChoice_sound (valid_wellFormed hv) hc).2.1
  have hout := child_outside (valid_wellFormed hv) ha hl hraw
  have hnext := hraw.replace hv hc hout
  have hlink := Net.replace_right_aux hv hc (hl.neighbor (valid_wellFormed hv)) hout hnew
  exact ⟨raw, heq, represented_reads hnext _ (neighborIn_sound hlink)⟩

/-- An unused raw input routed to a newly created eraser becomes an actual
represented resource job, ready for the universal draining theorem. -/
theorem Source.erase_left_aux {net : Net} (hv : net.valid = true)
    {rule : TriageRuleModel.Rule} {left right slot eraser : Nat}
    (hc : (rule, left, right) ∈ net.redexChoices) {term : Syntax}
    (h : Source net [] (.agent left (slot + 1)) term)
    (hk : (net.replace rule left right).kind? eraser = some .erase)
    (hnew : layerNeighbor (ruleLayer rule net.nextId) (.iface 0 (slot + 1)) =
      some (.real (.agent eraser 0))) :
    ∃ raw source, raw.toSyntax = term ∧
      TriageResourceJobs.Realizes (net.replace rule left right) ⟨.erase raw, eraser, source⟩ := by
  rcases h with ⟨raw, heq, hr⟩
  rcases hr.complete with ⟨root, hl, hraw⟩
  rcases hraw.principal with ⟨source, rfl⟩
  have ha := (Net.redexChoice_sound (valid_wellFormed hv) hc).2.1
  have hout := child_outside (valid_wellFormed hv) ha hl hraw
  have hnext := hraw.replace hv hc hout
  have hlink := Net.replace_left_aux hv hc (hl.neighbor (valid_wellFormed hv)) hout hnew
  exact ⟨raw, source, heq, hk, ⟨⟨_, hk⟩, ⟨_, hnext.kind⟩, hlink⟩, hnext⟩

/-- Every ordinary concrete interaction preserves an untouched materialized
continuation stack, including all its raw argument trees. -/
theorem Continuation.replace {net : Net} (hv : net.valid = true)
    {rule : TriageRuleModel.Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices)
    {input : End} {frames : List Frame} (h : Continuation net [] input frames)
    (hout : belongs left right input = false) :
    Continuation (net.replace rule left right) [] input frames := by
  have ha := (Net.redexChoice_sound (valid_wellFormed hv) hc).2.1
  revert hout
  induction h with
  | halt => intro _; exact .halt
  | @apply id rest arg frames hk hl harg hrest ih =>
      intro hout
      have hid : id ≠ left ∧ id ≠ right := by simpa [belongs] using hout
      have hr := continuation_child_outside (valid_wellFormed hv) ha hl hrest
      exact .apply (Net.replace_retains_kind hv rule hk hid.1 hid.2)
        (hl.replace rule left right hout hr) (harg.replace_aux hv hc hout) (ih hr)
  | @inspect id rest y arg frames hk hl hy harg hrest ih =>
      intro hout
      have hid : id ≠ left ∧ id ≠ right := by simpa [belongs] using hout
      have hr := continuation_child_outside (valid_wellFormed hv) ha hl hrest
      exact .inspect (Net.replace_retains_kind hv rule hk hid.1 hid.2)
        (hl.replace rule left right hout hr) (hy.replace_aux hv hc hout)
        (harg.replace_aux hv hc hout) (ih hr)
  | @triage id rest w x y frames hk hl hw hx hy hrest ih =>
      intro hout
      have hid : id ≠ left ∧ id ≠ right := by simpa [belongs] using hout
      have hr := continuation_child_outside (valid_wellFormed hv) ha hl hrest
      exact .triage (Net.replace_retains_kind hv rule hk hid.1 hid.2)
        (hl.replace rule left right hout hr) (hw.replace_aux hv hc hout)
        (hx.replace_aux hv hc hout) (hy.replace_aux hv hc hout) (ih hr)

end TriageContinuations
