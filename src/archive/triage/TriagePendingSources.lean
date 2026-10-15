import TriageResourceExecution

/-! Raw sources whose concrete copies are still under construction. -/

namespace TriagePendingSources
open TriageRuleModel (Kind)
open TriageResources TriageRawEncoding TriageResourceRules TriageResourceJobs TriageResourceExecution
open TriageConcrete TriageBoundary TriagePreservation TriageReduction TriageResidual TriageEncoding TriageLocalSemantics

inductive Reads (net : Net) (jobs : List Job) : End → Raw → Prop where
  | node {demand : End} {id : Nat} {raw : Raw} :
      Linked net demand (.agent id 0) → net.kind? id = some raw.kind →
      (∀ index child, raw.children[index]? = some child → Reads net jobs (.agent id (index + 1)) child) →
      Reads net jobs demand raw
  | pending {demand : End} {job : Job} {output : Nat} {raw : Raw} :
      job ∈ jobs → job.task = .copy raw → output < 2 →
      Linked net demand (.agent job.control (output + 1)) → Reads net jobs demand raw

theorem Reads.complete {net : Net} {demand : End} {raw : Raw} (h : Reads net [] demand raw) :
    ∃ root, Linked net demand root ∧ TriageRawEncoding.Realizes net root raw := by
  induction h with
  | node hl hk _ ih =>
      refine ⟨_, hl, TriageRawEncoding.Realizes.of_children hk ?_⟩
      intro index child hget
      exact ih index child hget
  | pending hm _ _ _ => cases hm

theorem Reads.jobs_mono {net : Net} {first second : List Job} (hs : first ⊆ second)
    {demand : End} {raw : Raw} (h : Reads net first demand raw) : Reads net second demand raw := by
  induction h with
  | node hl hk _ ih => exact .node hl hk ih
  | pending hm ht ho hl => exact .pending (hs hm) ht ho hl

theorem represented_reads {net : Net} {jobs : List Job} {root : End} {raw : Raw}
    (h : TriageRawEncoding.Realizes net root raw) :
    ∀ demand, Linked net demand root → Reads net jobs demand raw := by
  induction h with
  | leaf hk => intro demand hl; exact .node hl hk (by simp [Raw.children])
  | stem hk hl _ ih =>
      intro demand hlink
      refine Reads.node hlink ?_ ?_
      · exact hk
      · intro index child hget
        cases index with
        | zero => cases (Option.some.inj hget); exact ih _ hl
        | succ i => simp [Raw.children] at hget
  | fork hk hl hr _ _ ihl ihr | app hk hl hr _ _ ihl ihr =>
      intro demand hlink
      refine Reads.node hlink ?_ ?_
      · exact hk
      · intro index child hget
        cases index with
        | zero => cases (Option.some.inj hget); exact ihl _ hl
        | succ i =>
            cases i with
              | zero => cases (Option.some.inj hget); exact ihr _ hr
              | succ i => simp [Raw.children] at hget

theorem copy_child_job {children : List Job} {raw child : Raw} {index fresh : Nat}
    (ht : children.map Job.task = (Task.copy raw).expand)
    (hc : children.map Job.control = List.ofFn (fun i : Fin (Task.copy raw).expand.length => fresh + (2 + i.val)))
    (hget : raw.children[index]? = some child) :
    ∃ job ∈ children, job.task = .copy child ∧ job.control = fresh + (2 + index) := by
  have htask : (children[index]?).map Job.task = some (.copy child) := by
    rw [← List.getElem?_map, ht]
    simp [Task.expand, List.getElem?_map, hget]
  rcases Option.map_eq_some_iff.mp htask with ⟨job, hj, htj⟩
  have hctrl := congrArg (fun values : List Nat => values[index]?) hc
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hi, _⟩
  have hi' : index < (Task.copy raw).expand.length := by simpa [Task.expand] using hi
  simp only [List.getElem?_map, hj, Option.map_some, List.getElem?_ofFn, dif_pos hi', Option.some.injEq] at hctrl
  exact ⟨job, List.mem_of_getElem? hj, htj, hctrl⟩

theorem root_outside {net : Net} (hv : net.valid = true) {job : Job}
    (hj : TriageResourceJobs.Realizes net job) {demand : End} {id : Nat} {raw : Raw}
    (hl : Linked net demand (.agent id 0)) (hk : net.kind? id = some raw.kind)
    (hout : belongs job.control job.source demand = false) :
    belongs job.control job.source (.agent id 0) = false := by
  have hctrl : id ≠ job.control := by
    intro heq
    rw [heq, hj.control] at hk
    exact control_ne_raw job.task raw (Option.some.inj hk)
  have hsrc : id ≠ job.source := by
    intro heq
    have hback : net.neighbor (.agent job.source 0) = some (.agent job.control 0) :=
      neighborIn_symmetric (net.wellFormed_nodup (valid_wellFormed hv)) hj.active.2.2
    have hlink := hl.symm.neighbor (valid_wellFormed hv)
    rw [heq, hback] at hlink
    have hd : demand = .agent job.control 0 := (Option.some.inj hlink).symm
    simp [hd, belongs] at hout
  simp [belongs, hctrl, hsrc]

theorem copy_expands {net : Net} (hv : net.valid = true) {job : Job} {raw : Raw}
    (hj : TriageResourceJobs.Realizes net job) (htask : job.task = .copy raw)
    {before suffix children : List Job}
    (ht : children.map Job.task = job.task.expand)
    (hc : children.map Job.control = List.ofFn (fun i : Fin job.task.expand.length =>
      net.nextId + (job.task.offset + i.val)))
    {demand : End} {output : Nat} (ho : output < 2)
    (hl : Linked net demand (.agent job.control (output + 1)))
    (hout : belongs job.control job.source demand = false) :
    Reads (next net job) (before ++ children ++ suffix) demand raw := by
  have hrule : job.task.rule = raw.copyRule := by rw [htask]; rfl
  have hnext : (next net job).neighbor (.agent (net.nextId + output) 0) = some demand := by
    apply Net.replace_left_aux hv hj.choice (hl.symm.neighbor (valid_wellFormed hv)) hout
    simpa only [hrule] using copy_output raw net.nextId output ho
  have hkind := Net.replace_created_kind hv hj.choice (index := output) (kind := raw.kind)
    (by simpa only [hrule] using copy_root_kind raw output ho)
  refine Reads.node (neighborIn_sound hnext |>.symm) hkind ?_
  intro index child hget
  have ht' : children.map Job.task = (Task.copy raw).expand := by simpa only [htask] using ht
  have hc' : children.map Job.control = List.ofFn (fun i : Fin (Task.copy raw).expand.length =>
      net.nextId + (2 + i.val)) := by simpa only [htask, Task.offset] using hc
  rcases copy_child_job ht' hc' hget with ⟨childJob, hm, htj, hcj⟩
  have hmember : childJob ∈ before ++ children ++ suffix :=
    List.mem_append_left _ (List.mem_append_right _ hm)
  apply Reads.pending hmember htj ho
  rcases List.getElem?_eq_some_iff.mp hget with ⟨hi, _⟩
  have hwire := Net.replace_internal_wire hv hj.choice
    (by simpa only [hrule] using copy_child_wire raw index output hi ho)
  rw [hcj]
  exact (neighborIn_sound hwire).symm

/-- Resource expansion preserves sources observed outside its active pair. -/
theorem Reads.expand {net : Net} (hv : net.valid = true) {before suffix children : List Job} {job : Job}
    (hf : Forest net (before ++ job :: suffix)) (hj : TriageResourceJobs.Realizes net job)
    (ht : children.map Job.task = job.task.expand)
    (hc : children.map Job.control = List.ofFn (fun i : Fin job.task.expand.length =>
      net.nextId + (job.task.offset + i.val)))
    {demand : End} {raw : Raw} (h : Reads net (before ++ job :: suffix) demand raw)
    (hout : belongs job.control job.source demand = false) :
    Reads (next net job) (before ++ children ++ suffix) demand raw := by
  have hjob : job ∈ before ++ job :: suffix := List.mem_append_right _ (List.mem_cons_self ..)
  revert hout
  induction h with
  | @node demand id raw hl hk hchildren ih =>
      intro hout
      have hroot := root_outside hv hj hl hk hout
      have hid : id ≠ job.control ∧ id ≠ job.source := by simpa [belongs] using hroot
      refine Reads.node (hl.replace job.task.rule job.control job.source hout hroot)
        (Net.replace_retains_kind hv job.task.rule hk hid.1 hid.2) ?_
      intro index child hget
      exact ih index child hget hroot
  | @pending demand other output raw hm htask ho hl =>
      intro hout
      by_cases heq : other = job
      · subst other
        exact copy_expands hv hj htask ht hc ho hl hout
      · have hneq : other.control ≠ job.control := by
          intro hctrl
          exact heq (List.inj_on_of_nodup_map hf.controls hm hjob hctrl)
        have hother := hf.realizes other hm
        have hd := hother.disjoint hv hj hneq
        have hport : belongs job.control job.source (.agent other.control (output + 1)) = false := by
          simp [belongs, hd.1, hd.2.1]
        have hmem : other ∈ before ++ children ++ suffix := by
          simp only [List.mem_append, List.mem_cons] at hm ⊢
          rcases hm with hm | hm | hm
          · exact Or.inl (Or.inl hm)
          · exact False.elim (heq hm)
          · exact Or.inr hm
        exact Reads.pending hmem htask ho (hl.replace job.task.rule job.control job.source hout hport)

def controlKinds : List Kind := [.eval, .call, .case_, .triage]

inductive Anchor (net : Net) : End → Prop where
  | free (name : Nat) : Anchor net (.free name)
  | agent {id slot : Nat} {kind : Kind} : net.kind? id = some kind → kind ∈ controlKinds →
      Anchor net (.agent id slot)

theorem control_kind_distinct (task : Task) (raw : Raw) {kind : Kind} (hk : kind ∈ controlKinds) :
    kind ≠ task.kind ∧ kind ≠ raw.kind := by
  simp only [controlKinds, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> cases task <;> cases raw <;> simp [Task.kind, Raw.kind]

theorem Anchor.outside {net : Net} {job : Job} (hj : TriageResourceJobs.Realizes net job)
    {demand : End} (h : Anchor net demand) : belongs job.control job.source demand = false := by
  cases h with
  | free => rfl
  | @agent id slot kind hk hkind =>
      have hd := control_kind_distinct job.task job.task.raw hkind
      have hc : id ≠ job.control := by
        intro heq
        rw [heq, hj.control] at hk
        exact hd.1 (Option.some.inj hk).symm
      have hs : id ≠ job.source := by
        intro heq
        rw [heq, hj.raw.kind] at hk
        exact hd.2 (Option.some.inj hk).symm
      simp [belongs, hc, hs]

theorem Anchor.retained {net : Net} (hv : net.valid = true) {job : Job}
    (hj : TriageResourceJobs.Realizes net job) {demand : End} (h : Anchor net demand) :
    Anchor (next net job) demand := by
  have hout := h.outside hj
  cases h with
  | free name => exact .free name
  | @agent id slot kind hk hm =>
      have hid : id ≠ job.control ∧ id ≠ job.source := by simpa [belongs] using hout
      exact .agent (Net.replace_retains_kind hv job.task.rule hk hid.1 hid.2) hm

theorem anchor_progress {net target : Net} {jobs after : List Job}
    (hv : net.valid = true) (hp : Progress net jobs target after)
    {demand : End} (ha : Anchor net demand) : Anchor target demand := by
  rcases hp.selected with ⟨before, job, suffix, children, rfl, rfl, rfl, hj, _, _⟩
  exact ha.retained hv hj

theorem reads_progress {net target : Net} {jobs after : List Job}
    (hv : net.valid = true) (hf : Forest net jobs) (hp : Progress net jobs target after)
    {demand : End} {raw : Raw} (ha : Anchor net demand) (hr : Reads net jobs demand raw) :
    Reads target after demand raw := by
  rcases hp.selected with ⟨before, job, suffix, children, rfl, rfl, rfl, hj, ht, hc⟩
  exact hr.expand hv hf hj ht hc (ha.outside hj)

theorem run_reads {count : Nat} {net final : Net} {jobs after : List Job}
    (h : Run count net jobs final after) (hv : net.valid = true) (hf : Forest net jobs)
    {demand : End} {raw : Raw} (ha : Anchor net demand) (hr : Reads net jobs demand raw) :
    Reads final after demand raw := by
  revert hv hf ha hr
  induction h with
  | zero => intro _ _ _ hr; exact hr
  | step hp _ ih =>
      intro hv hf ha hr
      exact ih (hp.graph.preserves_valid hv) hp.forest (anchor_progress hv hp ha)
        (reads_progress hv hf hp ha hr)

/-- One concrete draining schedule materializes every anchored logical
source simultaneously, including sources containing pending copies. -/
theorem materialize {net : Net} (hv : net.valid = true) {jobs : List Job} (hf : Forest net jobs) :
    ∃ final, Run (cost jobs) net jobs final [] ∧ final.valid = true ∧
      ∀ demand raw, Anchor net demand → Reads net jobs demand raw →
        ∃ root, Linked final demand root ∧ TriageRawEncoding.Realizes final root raw := by
  rcases drain hv hf with ⟨final, hrun, hvalid⟩
  exact ⟨final, hrun, hvalid, fun _ _ ha hr => (run_reads hrun hv hf ha hr).complete⟩

/-- A pending copy produces two complete raw trees with the original
constructor structure and syntax after finitely many executable steps. -/
theorem copy_correct {net : Net} (hv : net.valid = true) {job : Job} {raw : Raw}
    (hj : TriageResourceJobs.Realizes net job) (ht : job.task = .copy raw)
    {first second : End} (hf : Anchor net first) (hs : Anchor net second)
    (hl : Linked net first (.agent job.control 1)) (hr : Linked net second (.agent job.control 2)) :
    ∃ final left right, Run raw.size net [job] final [] ∧ final.valid = true ∧
      Linked final first left ∧ TriageRawEncoding.Realizes final left raw ∧
      Linked final second right ∧ TriageRawEncoding.Realizes final right raw ∧ left ≠ right := by
  have hforest : Forest net [job] := ⟨by simp, by intro other hm; cases List.mem_singleton.mp hm; exact hj⟩
  rcases materialize hv hforest with ⟨final, hrun, hvalid, hread⟩
  rcases hread first raw hf (Reads.pending (List.mem_singleton_self _) ht (by decide : 0 < 2) hl) with
    ⟨left, hleft, hlraw⟩
  rcases hread second raw hs (Reads.pending (List.mem_singleton_self _) ht (by decide : 1 < 2) hr) with
    ⟨right, hright, hrraw⟩
  have hdistinct : first ≠ second := by
    intro heq
    have hp := hl.neighbor (valid_wellFormed hv)
    rw [heq, hr.neighbor (valid_wellFormed hv)] at hp
    have hslot := (End.agent.inj (Option.some.inj hp)).2
    omega
  have hroots : left ≠ right := by
    intro heq
    have hp := hleft.symm.neighbor (valid_wellFormed hvalid)
    rw [heq, hright.symm.neighbor (valid_wellFormed hvalid)] at hp
    exact hdistinct (Option.some.inj hp).symm
  exact ⟨final, left, right, by simpa [cost, TriageResources.total, ht, Task.size] using hrun,
    hvalid, hleft, hlraw, hright, hrraw, hroots⟩

/-- Erasure drains the entire represented job while preserving every raw
source observed at an evaluator, continuation, or free port. -/
theorem erase_correct {net : Net} (hv : net.valid = true) {job : Job} {raw : Raw}
    (hj : TriageResourceJobs.Realizes net job) (ht : job.task = .erase raw) :
    ∃ final, Run raw.size net [job] final [] ∧ final.valid = true ∧
      ∀ demand root source, Anchor net demand → Linked net demand root →
        TriageRawEncoding.Realizes net root source →
          ∃ result, Linked final demand result ∧ TriageRawEncoding.Realizes final result source := by
  have hforest : Forest net [job] := ⟨by simp, by intro other hm; cases List.mem_singleton.mp hm; exact hj⟩
  rcases materialize hv hforest with ⟨final, hrun, hvalid, hread⟩
  refine ⟨final, by simpa [cost, TriageResources.total, ht, Task.size] using hrun, hvalid, ?_⟩
  intro demand root source ha hl hr
  exact hread demand source ha (represented_reads hr demand hl)

end TriagePendingSources
