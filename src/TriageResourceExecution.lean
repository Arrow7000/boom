import TriageResourceJobs

/-! Finite concrete execution of represented resource forests. -/

namespace TriageResourceExecution
open TriageResources TriageConcrete TriageBoundary TriagePreservation TriageReduction TriageAllocation
open TriageResourceJobs

structure Forest (net : Net) (jobs : List Job) : Prop where
  controls : (jobs.map Job.control).Nodup
  realizes : ∀ job ∈ jobs, Realizes net job

def cost (jobs : List Job) : Nat := TriageResources.total (jobs.map Job.task)

theorem Forest.perm {net : Net} {first second : List Job}
    (h : Forest net first) (hp : first.Perm second) : Forest net second :=
  ⟨(hp.map Job.control).nodup_iff.mp h.controls, fun job hm => h.realizes job (hp.mem_iff.mpr hm)⟩

theorem Forest.expand_head {net : Net} (hv : net.valid = true) {job : Job} {rest : List Job}
    (h : Forest net (job :: rest)) :
    ∃ children : List Job, children.map Job.task = job.task.expand ∧ Forest (next net job) (children ++ rest) ∧
      children.map Job.control = List.ofFn (fun i : Fin job.task.expand.length =>
        net.nextId + (job.task.offset + i.val)) := by
  have hj := h.realizes job (List.mem_cons_self ..)
  rcases TriageResourceJobs.expand hv hj with ⟨children, ht, hc, hn, hfresh, hcontrollers⟩
  have hrest : ∀ other ∈ rest, Realizes net other :=
    fun other hm => h.realizes other (List.mem_cons_of_mem _ hm)
  have hnd := List.nodup_cons.mp h.controls
  have hneq : ∀ other ∈ rest, job.control ≠ other.control := by
    intro other hm heq
    exact hnd.1 (List.mem_map.mpr ⟨other, hm, heq.symm⟩)
  have hdisjoint : (children.map Job.control).Disjoint (rest.map Job.control) := by
    rw [List.disjoint_left]
    intro id hnew hold
    rcases List.mem_map.mp hnew with ⟨child, hm, rfl⟩
    rcases List.mem_map.mp hold with ⟨other, ho, heq⟩
    have hlo := active_id_bound hv (hrest other ho).control
    have hhi := hfresh child hm
    omega
  refine ⟨children, ht, ⟨?_, ?_⟩, hcontrollers⟩
  · simpa only [List.map_append] using List.nodup_append'.mpr ⟨hn, hnd.2, hdisjoint⟩
  · intro other hm
    rcases List.mem_append.mp hm with hchild | hold
    · exact hc other hchild
    · exact hj.retained hv (hrest other hold) (hneq other hold)

structure Progress (net : Net) (jobs : List Job) (target : Net) (after : List Job) : Prop where
  graph : TriageReduction.Step net target
  tasks : TriageResources.Step (jobs.map Job.task) (after.map Job.task)
  forest : Forest target after
  selected : ∃ before job suffix children, jobs = before ++ job :: suffix ∧
    target = next net job ∧ after = before ++ children ++ suffix ∧ Realizes net job ∧
    children.map Job.task = job.task.expand ∧
    children.map Job.control = List.ofFn (fun i : Fin job.task.expand.length =>
      net.nextId + (job.task.offset + i.val))

theorem task_step_cost {before after : List Task} (h : TriageResources.Step before after) :
    TriageResources.total after + 1 = TriageResources.total before := by
  cases h with
  | expandOne before after task =>
      have he := Task.expand_size task
      simp only [TriageResources.total, List.map_append, List.map_cons,
        List.sum_append, List.sum_cons]
      omega

theorem Progress.cost {net target : Net} {jobs after : List Job} (h : Progress net jobs target after) :
    cost after + 1 = cost jobs := task_step_cost h.tasks

/-- Any selected job may be expanded while preserving the remaining forest. -/
theorem Forest.expand_at {net : Net} (hv : net.valid = true)
    (before : List Job) (job : Job) (after : List Job) (h : Forest net (before ++ job :: after)) :
    ∃ children, Progress net (before ++ job :: after) (next net job) (before ++ children ++ after) := by
  have hh := h.perm (List.perm_middle : (before ++ job :: after).Perm (job :: (before ++ after)))
  rcases hh.expand_head hv with ⟨children, ht, hc, hcontrollers⟩
  have hj := hh.realizes job (List.mem_cons_self ..)
  refine ⟨children, hj.step, ?_, ?_, ?_⟩
  · simpa only [List.map_append, List.map_cons, ht] using
      TriageResources.Step.expandOne (before.map Job.task) (after.map Job.task) job.task
  · exact hc.perm (by
      simpa only [List.append_assoc] using List.perm_append_comm_assoc children before after)
  · exact ⟨before, job, after, children, rfl, rfl, rfl, hj, ht, hcontrollers⟩

theorem Forest.progress {net : Net} (hv : net.valid = true) {jobs : List Job}
    (h : Forest net jobs) (hne : jobs ≠ []) : ∃ target after, Progress net jobs target after := by
  cases jobs with
  | nil => exact False.elim (hne rfl)
  | cons job rest =>
      rcases h.expand_at hv [] job rest with ⟨children, hp⟩
      exact ⟨next net job, children ++ rest, by simpa using hp⟩

/-- A concrete administrative run records each graph step together with its
abstract resource-task refinement. Other computational redexes may remain. -/
inductive Run : Nat → Net → List Job → Net → List Job → Prop where
  | zero (net : Net) (jobs : List Job) : Run 0 net jobs net jobs
  | step {n : Nat} {first second final : Net} {jobs middle after : List Job} :
      Progress first jobs second middle → Run n second middle final after → Run (n + 1) first jobs final after

theorem Run.graph {n : Nat} {first final : Net} {jobs after : List Job}
    (h : Run n first jobs final after) : Steps first final := by
  induction h with
  | zero => exact .refl
  | step hp _ ih => exact Relation.ReflTransGen.head hp.graph ih

theorem Run.cost {n : Nat} {first final : Net} {jobs after : List Job}
    (h : Run n first jobs final after) : cost after + n = cost jobs := by
  induction h with
  | zero => omega
  | step hp _ ih => have hc := hp.cost; omega

/-- Every finite represented forest can be drained by actual executable
interactions. The exact number is the sum of the sizes of its raw payloads. -/
theorem drain {net : Net} (hv : net.valid = true) {jobs : List Job} (h : Forest net jobs) :
    ∃ final, Run (cost jobs) net jobs final [] ∧ final.valid = true := by
  suffices ∀ count, ∀ net jobs, cost jobs = count → net.valid = true → Forest net jobs →
      ∃ final, Run (cost jobs) net jobs final [] ∧ final.valid = true by
    exact this (cost jobs) net jobs rfl hv h
  intro count
  induction count using Nat.strong_induction_on with
  | h count ih =>
      intro net jobs hcount hv hf
      by_cases he : jobs = []
      · subst jobs
        exact ⟨net, Run.zero net [], hv⟩
      · rcases hf.progress hv he with ⟨target, after, hp⟩
        have hc := hp.cost
        have hlt : cost after < count := by omega
        have ht := hp.graph.preserves_valid hv
        rcases ih (cost after) hlt target after rfl ht hp.forest with ⟨final, hrun, hvalid⟩
        exact ⟨final, by simpa only [hc] using Run.step hp hrun, hvalid⟩

theorem single_job {net : Net} (hv : net.valid = true) {job : Job} (h : Realizes net job) :
    ∃ final, Run job.task.size net [job] final [] ∧ final.valid = true := by
  have hf : Forest net [job] := ⟨by simp, by intro other hm; simpa using (List.mem_singleton.mp hm ▸ h)⟩
  simpa [cost, TriageResources.total] using drain hv hf

theorem Progress.decreases {net target : Net} {jobs after : List Job} (h : Progress net jobs target after) :
    TriageResourceExecution.cost after < TriageResourceExecution.cost jobs := by have hc := h.cost; omega

theorem administrative_wellFounded : WellFounded (fun next current : Net × List Job =>
    Progress current.1 current.2 next.1 next.2) :=
  Subrelation.wf (fun h => Progress.decreases h) (measure fun state : Net × List Job => cost state.2).wf

end TriageResourceExecution
