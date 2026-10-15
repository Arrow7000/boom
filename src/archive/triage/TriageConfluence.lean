/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageEquivariance

/-!
Confluence of every finite executable reduction schedule from a valid net,
up to graph isomorphism. Renaming moves are used in the Church-Rosser proof
and then postponed, leaving actual executable steps on both joining paths.
-/

namespace TriageConfluence
open TriageConcrete TriagePreservation TriageReduction TriageResidual
open TriageEquivalence TriageEquivariance

theorem local_diamond {source first second : Net} (hv : source.valid = true)
    (hf : Step source first) (hs : Step source second) :
    ∃ firstJoin secondJoin, Relation.ReflGen Step first firstJoin ∧
      Relation.ReflGen Step second secondJoin ∧ Aligned firstJoin secondJoin := by
  cases hf with
  | @chosen firstRule a b hfirst =>
      cases hs with
      | @chosen secondRule c d hsecond =>
          by_cases heq : (firstRule, a, b) = (secondRule, c, d)
          · cases heq
            exact ⟨_, _, .refl, .refl, Aligned.refl _⟩
          · rcases Net.residual_schedules hv hfirst hsecond heq with ⟨hf, hs⟩
            exact ⟨_, _, .single hf, .single hs, double_aligned hv hfirst hsecond heq⟩

abbrev ValidNet := {net : Net // net.valid = true}

def Move (first second : ValidNet) : Prop := Step first.val second.val ∨ Aligned first.val second.val

theorem optional_valid {first second : Net} (hf : first.valid = true)
    (h : Relation.ReflGen Step first second) : second.valid = true := by
  cases h with
  | refl => exact hf
  | single hs => exact hs.preserves_valid hf

theorem optional_lift {first : ValidNet} {second : Net} (hs : second.valid = true)
    (h : Relation.ReflGen Step first.val second) : Relation.ReflGen Move first ⟨second, hs⟩ := by
  cases h with
  | refl => exact .refl
  | single hs => exact .single (Or.inl hs)

theorem Move.strong (source first second : ValidNet) (hf : Move source first) (hs : Move source second) :
    ∃ target, Relation.ReflGen Move first target ∧ Relation.ReflTransGen Move second target := by
  rcases hf with hf | hf <;> rcases hs with hs | hs
  · rcases local_diamond source.property hf hs with ⟨left, right, hl, hr, he⟩
    have hleft := optional_valid first.property hl
    have hright := optional_valid second.property hr
    exact ⟨⟨left, hleft⟩, optional_lift hleft hl,
      (optional_lift hright hr).to_reflTransGen.tail (Or.inr he.symm)⟩
  · rcases hs.transport source.property second.property hf with ⟨target, hstep, he⟩
    have hv := hstep.preserves_valid second.property
    exact ⟨⟨target, hv⟩, .single (Or.inr he), .single (Or.inl hstep)⟩
  · rcases hf.transport source.property first.property hs with ⟨target, hstep, he⟩
    have hv := hstep.preserves_valid first.property
    exact ⟨⟨target, hv⟩, .single (Or.inl hstep), .single (Or.inr he)⟩
  · exact ⟨first, .refl, .single (Or.inr (hs.symm.trans hf))⟩

/-- Renaming steps can be moved to the end of a mixed reduction path. -/
theorem postpone {first second : ValidNet} (h : Relation.ReflTransGen Move first second) :
    ∃ target, Steps first.val target ∧ Aligned target second.val := by
  induction h with
  | refl => exact ⟨first.val, .refl, Aligned.refl _⟩
  | @tail before after hpath hmove ih =>
      rcases ih with ⟨target, hsteps, hi⟩
      rcases hmove with hstep | heq
      · have ht := hsteps.preserves_valid first.property
        rcases hi.symm.transport before.property ht hstep with ⟨next, hnext, he⟩
        exact ⟨next, hsteps.tail hnext, he.symm⟩
      · exact ⟨target, hsteps, hi.trans heq⟩

theorem lift_steps {first second : Net} (h : Steps first second)
    (hf : first.valid = true) (hs : second.valid = true) :
    Relation.ReflTransGen Move ⟨first, hf⟩ ⟨second, hs⟩ := by
  induction h with
  | refl => exact .refl
  | @tail before after hpath hstep ih =>
      exact (ih (Steps.preserves_valid hpath hf)).tail (Or.inl hstep)

/-- Every pair of finite executable schedules from the same valid net has
executable joining schedules whose endpoints are isomorphic. -/
theorem confluence {source first second : Net} (hv : source.valid = true)
    (hf : Steps source first) (hs : Steps source second) :
    ∃ firstJoin secondJoin, Steps first firstJoin ∧ Steps second secondJoin ∧
      Equivalent firstJoin secondJoin := by
  have hfv := hf.preserves_valid hv
  have hsv := hs.preserves_valid hv
  rcases Relation.church_rosser Move.strong (lift_steps hf hv hfv) (lift_steps hs hv hsv) with
    ⟨target, hfirst, hsecond⟩
  rcases postpone hfirst with ⟨left, hl, heleft⟩
  rcases postpone hsecond with ⟨right, hr, heright⟩
  exact ⟨left, right, hl, hr, (heleft.trans heright.symm).equivalent⟩

theorem initial_confluence (source : TriageMachine.Syntax) {first second : Net}
    (hf : Steps (initial source) first) (hs : Steps (initial source) second) :
    ∃ firstJoin secondJoin, Steps first firstJoin ∧ Steps second secondJoin ∧
      Equivalent firstJoin secondJoin :=
  confluence (TriageInitial.initial_valid source) hf hs

def Normal (net : Net) : Prop := ∀ target, ¬Step net target

theorem Normal.steps_eq {first second : Net} (hn : Normal first) (hs : Steps first second) : second = first := by
  induction hs with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      exact False.elim (hn _ hstep)

theorem normal_of_step_none {net : Net} (hn : net.step? = none) : Normal net := by
  cases hc : net.firstRedex with
  | some choice => simp [Net.step?, hc] at hn
  | none =>
      have hempty : net.redexChoices = [] := List.head?_eq_none_iff.mp hc
      intro target hstep
      cases hstep with
      | chosen hchoice => simp [hempty] at hchoice

/-- Finished schedules have isomorphic results. Confluence makes no claim
that every source terminates, or that every infinite schedule is fair. -/
theorem normal_forms_equivalent {source first second : Net} (hv : source.valid = true)
    (hf : Steps source first) (hs : Steps source second) (hnf : Normal first) (hns : Normal second) :
    Equivalent first second := by
  rcases confluence hv hf hs with ⟨left, right, hl, hr, he⟩
  have hleft := hnf.steps_eq hl
  have hright := hns.steps_eq hr
  simpa only [hleft, hright] using he

/-- The actual syntax displayed after stopping is independent of the
reduction order, at every readback fuel bound. -/
theorem finished_readback {source first second : Net} (hv : source.valid = true)
    (hf : Steps source first) (hs : Steps source second)
    (hnf : first.step? = none) (hns : second.step? = none) (fuel : Nat) :
    first.outputSyntax fuel = second.outputSyntax fuel :=
  ((normal_forms_equivalent hv hf hs (normal_of_step_none hnf) (normal_of_step_none hns)).outputSyntax fuel).symm

theorem initial_finished_readback (source : TriageMachine.Syntax) {first second : Net}
    (hf : Steps (initial source) first) (hs : Steps (initial source) second)
    (hnf : first.step? = none) (hns : second.step? = none) (fuel : Nat) :
    first.outputSyntax fuel = second.outputSyntax fuel :=
  finished_readback (TriageInitial.initial_valid source) hf hs hnf hns fuel

theorem finished_runs {net : Net} (hv : net.valid = true) (firstFuel secondFuel readFuel : Nat)
    (hf : (net.run firstFuel).step? = none) (hs : (net.run secondFuel).step? = none) :
    (net.run firstFuel).outputSyntax readFuel = (net.run secondFuel).outputSyntax readFuel :=
  finished_readback hv (Net.run_steps firstFuel net) (Net.run_steps secondFuel net) hf hs readFuel

end TriageConfluence
