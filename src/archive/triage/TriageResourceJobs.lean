/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageResourceRules
import TriageAllocation
import Mathlib.Data.List.OfFn

/-! Concrete active copy/erase jobs and their exact child-job expansion. -/

namespace TriageResourceJobs
open TriageResources TriageRawEncoding TriageResourceRules
open TriageConcrete TriageBoundary TriagePreservation TriageResidual TriageReduction
open TriageLocalSemantics TriageAllocation TriageEncoding

structure Job where
  task : Task
  control : Nat
  source : Nat
  deriving Repr, DecidableEq

structure Realizes (net : Net) (job : Job) : Prop where
  control : net.kind? job.control = some job.task.kind
  active : net.Active job.control job.source
  raw : TriageRawEncoding.Realizes net (.agent job.source 0) job.task.raw

def next (net : Net) (job : Job) : Net := net.replace job.task.rule job.control job.source

theorem Realizes.choice {net : Net} {job : Job} (h : Realizes net job) :
    (job.task.rule, job.control, job.source) ∈ net.redexChoices := by
  apply Net.redexChoice_complete job.task.rule_mem h.active
  · simpa only [Task.rule_left] using h.control
  · simpa only [Task.rule_right] using h.raw.kind

theorem Realizes.step {net : Net} {job : Job} (h : Realizes net job) : Step net (next net job) :=
  Step.chosen h.choice

theorem control_ne_raw (task : Task) (raw : Raw) : task.kind ≠ raw.kind := by
  cases task <;> cases raw <;> simp [Task.kind, Raw.kind]

theorem Realizes.disjoint {net : Net} (hv : net.valid = true) {first second : Job}
    (hf : Realizes net first) (hs : Realizes net second) (hne : first.control ≠ second.control) :
    first.control ≠ second.control ∧ first.control ≠ second.source ∧
      first.source ≠ second.control ∧ first.source ≠ second.source := by
  have hcs : first.control ≠ second.source := by
    intro heq
    have hk := hs.raw.kind
    rw [← heq, hf.control] at hk
    exact control_ne_raw first.task second.task.raw (Option.some.inj hk)
  have hsc : first.source ≠ second.control := by
    intro heq
    have hk := hf.raw.kind
    rw [heq, hs.control] at hk
    exact control_ne_raw second.task first.task.raw (Option.some.inj hk)
  refine ⟨hne, hcs, hsc, ?_⟩
  intro heq
  rcases Net.active_disjoint_or_equal (valid_wellFormed hv) hf.active hs.active
    (Or.inr (Or.inr (Or.inr heq))) with he | he
  · exact hne he.1
  · exact hcs he.1

theorem Realizes.retained {net : Net} (hv : net.valid = true) {first second : Job}
    (hf : Realizes net first) (hs : Realizes net second) (hne : first.control ≠ second.control) :
    Realizes (next net first) second := by
  rcases hs.disjoint hv hf (Ne.symm hne) with ⟨hcc, hcs, hsc, hss⟩
  refine ⟨Net.replace_retains_kind hv first.task.rule hs.control hcc hcs,
    Net.replace_retains_active hv hf.choice hs.active hcc hcs hsc hss, ?_⟩
  apply hs.raw.replace hv hf.choice
  simp [belongs, hsc, hss]

/-- One actual interaction creates exactly the abstract task's child jobs.
Every child retains its original complete raw payload; all new controllers
are distinct and freshly allocated. -/
theorem expand {net : Net} (hv : net.valid = true) {job : Job} (h : Realizes net job) :
    ∃ children : List Job,
      children.map Job.task = job.task.expand ∧
      (∀ child ∈ children, Realizes (next net job) child) ∧
      (children.map Job.control).Nodup ∧
      (∀ child ∈ children, net.nextId ≤ child.control) ∧
      children.map Job.control = List.ofFn (fun i : Fin job.task.expand.length =>
        net.nextId + (job.task.offset + i.val)) := by
  classical
  let count := job.task.expand.length
  have hinput : ∀ i : Fin count, ∃ id,
      Linked net (.agent job.source (i.val + 1)) (.agent id 0) ∧
        TriageRawEncoding.Realizes net (.agent id 0) (job.task.expand[i.val]).raw := by
    intro i
    have ht : job.task.expand[i.val]? = some job.task.expand[i.val] := List.getElem?_eq_getElem i.isLt
    rcases h.raw.children i.val _ (Task.child_raw ht) with ⟨root, hlink, hr⟩
    rcases hr.principal with ⟨id, rfl⟩
    exact ⟨id, hlink, hr⟩
  let sourceId := fun i : Fin count => Classical.choose (hinput i)
  let make := fun i : Fin count =>
    Job.mk (job.task.expand[i.val]) (net.nextId + (job.task.offset + i.val)) (sourceId i)
  let children := List.ofFn make
  have hmake : ∀ i : Fin count, Realizes (next net job) (make i) := by
    intro i
    have hin := Classical.choose_spec (hinput i)
    have ht : job.task.expand[i.val]? = some job.task.expand[i.val] := List.getElem?_eq_getElem i.isLt
    have hout := child_outside (valid_wellFormed hv) h.active hin.1 hin.2
    have hwire : (next net job).neighbor (.agent (net.nextId + (job.task.offset + i.val)) 0) =
        some (.agent (sourceId i) 0) := by
      exact Net.replace_right_aux hv h.choice (hin.1.neighbor (valid_wellFormed hv)) hout
        (child_interface job.task net.nextId i.val i.isLt)
    have hkind := Net.replace_created_kind hv h.choice (Task.child_kind i.isLt)
    have hraw := hin.2.replace hv h.choice hout
    have hctrl : (next net job).kind? (make i).control = some (make i).task.kind := by
      simpa only [make, Task.child_same_kind ht] using hkind
    refine ⟨hctrl, ⟨⟨_, hctrl⟩, ⟨_, hraw.kind⟩, hwire⟩, hraw⟩
  refine ⟨children, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [children, make, List.map_ofFn] using List.ofFn_getElem job.task.expand
  · intro child hc
    rcases List.mem_ofFn.mp hc with ⟨i, rfl⟩
    exact hmake i
  · rw [show children.map Job.control = List.ofFn (fun i : Fin count => net.nextId + (job.task.offset + i.val)) from
      List.map_ofFn make Job.control]
    apply List.nodup_ofFn.mpr
    intro i j heq
    apply Fin.ext
    change net.nextId + (job.task.offset + i.val) = net.nextId + (job.task.offset + j.val) at heq
    omega
  · intro child hc
    rcases List.mem_ofFn.mp hc with ⟨i, rfl⟩
    change net.nextId ≤ net.nextId + (job.task.offset + i.val)
    omega

  · exact List.map_ofFn make Job.control

end TriageResourceJobs
