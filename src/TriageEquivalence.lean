import TriageInitial
import Mathlib.Logic.Equiv.Basic

/-!
Graph equivalence for concrete nets. Agent IDs may be renamed by a bijection;
agent and wire list order and the allocation counter are not observations.
Free-port names and agent port slots are fixed. The definition compares the
actual kind and neighbor functions used by the executable reducer.
-/

namespace TriageEquivalence
open TriageConcrete

def renameEnd (rename : Nat ≃ Nat) : End → End
  | .agent id slot => .agent (rename id) slot
  | .free name => .free name

@[simp] theorem renameEnd_refl (end_ : End) :
    renameEnd (Equiv.refl Nat) end_ = end_ := by cases end_ <;> rfl

@[simp] theorem renameEnd_symm (rename : Nat ≃ Nat) (end_ : End) :
    renameEnd rename.symm (renameEnd rename end_) = end_ := by
  cases end_ <;> simp [renameEnd]

@[simp] theorem renameEnd_apply_symm (rename : Nat ≃ Nat) (end_ : End) :
    renameEnd rename (renameEnd rename.symm end_) = end_ := by
  cases end_ <;> simp [renameEnd]

@[simp] theorem renameEnd_trans (first second : Nat ≃ Nat) (end_ : End) :
    renameEnd (first.trans second) end_ =
      renameEnd second (renameEnd first end_) := by cases end_ <;> rfl

theorem renameEnd_injective (rename : Nat ≃ Nat) :
    Function.Injective (renameEnd rename) := by
  intro first second heq
  have := congrArg (renameEnd rename.symm) heq
  simpa using this

structure Iso (rename : Nat ≃ Nat) (first second : Net) : Prop where
  kinds : ∀ id, second.kind? (rename id) = first.kind? id
  neighbors : ∀ end_, second.neighbor (renameEnd rename end_) =
    (first.neighbor end_).map (renameEnd rename)

def Equivalent (first second : Net) : Prop := ∃ rename, Iso rename first second

theorem Iso.refl (net : Net) : Iso (Equiv.refl Nat) net net where
  kinds := fun _ => rfl
  neighbors := by intro end_; cases hn : net.neighbor end_ <;> simp [hn]

theorem Iso.symm {rename : Nat ≃ Nat} {first second : Net}
    (h : Iso rename first second) : Iso rename.symm second first where
  kinds := by
    intro id
    simpa using (h.kinds (rename.symm id)).symm
  neighbors := by
    intro end_
    have hn := h.neighbors (renameEnd rename.symm end_)
    have hm := congrArg (Option.map (renameEnd rename.symm)) hn
    simpa [Option.map_map, Function.comp_def] using hm.symm

theorem Iso.trans {first second third : Net} {f g : Nat ≃ Nat}
    (hf : Iso f first second) (hg : Iso g second third) :
    Iso (f.trans g) first third where
  kinds := by intro id; exact (hg.kinds (f id)).trans (hf.kinds id)
  neighbors := by
    intro end_
    rw [renameEnd_trans, hg.neighbors, hf.neighbors]
    cases hn : first.neighbor end_ <;> simp [renameEnd_trans]

theorem Equivalent.refl (net : Net) : Equivalent net net := ⟨_, Iso.refl net⟩

theorem Equivalent.symm {first second : Net} (h : Equivalent first second) :
    Equivalent second first := by rcases h with ⟨rename, hi⟩; exact ⟨_, hi.symm⟩

theorem Equivalent.trans {first second third : Net}
    (hf : Equivalent first second) (hg : Equivalent second third) :
    Equivalent first third := by
  rcases hf with ⟨f, hfi⟩
  rcases hg with ⟨g, hgi⟩
  exact ⟨_, hfi.trans hgi⟩

theorem Iso.active {rename : Nat ≃ Nat} {first second : Net}
    (h : Iso rename first second) (left right : Nat) :
    first.Active left right ↔ second.Active (rename left) (rename right) := by
  simp only [Net.Active, h.kinds]
  have hn := h.neighbors (.agent left 0)
  change second.neighbor (.agent (rename left) 0) =
    (first.neighbor (.agent left 0)).map (renameEnd rename) at hn
  rw [hn]
  have heq : (first.neighbor (.agent left 0)).map (renameEnd rename) =
      some (.agent (rename right) 0) ↔
      first.neighbor (.agent left 0) = some (.agent right 0) := by
    cases first.neighbor (.agent left 0) with
    | none => simp
    | some end_ =>
        constructor
        · intro heq
          have hnode := Option.some.inj heq
          have : end_ = .agent right 0 := renameEnd_injective rename hnode
          rw [this]
        · intro heq; cases heq; rfl
  rw [heq]

theorem Iso.readRoot {rename : Nat ≃ Nat} {first second : Net}
    (h : Iso rename first second) (fuel : Nat) (end_ : End) :
    second.readRoot fuel (renameEnd rename end_) = first.readRoot fuel end_ := by
  induction fuel generalizing end_ with
  | zero => rfl
  | succ fuel ih =>
      cases end_ with
      | free name => rfl
      | agent id slot =>
          cases slot with
          | succ slot => rfl
          | zero =>
              simp only [renameEnd, Net.readRoot, h.kinds]
              cases hk : first.kind? id with
              | none => rfl
              | some kind =>
                  cases kind <;> dsimp only [Bind.bind, Option.bind]
                  all_goals
                    have hn1 := h.neighbors (.agent id 1)
                    change second.neighbor (.agent (rename id) 1) =
                      (first.neighbor (.agent id 1)).map (renameEnd rename) at hn1
                    rw [hn1]
                    cases hc1 : first.neighbor (.agent id 1) with
                    | none => rfl
                    | some child =>
                        simp only [Option.map_some, ih]
                        all_goals
                          have hn2 := h.neighbors (.agent id 2)
                          change second.neighbor (.agent (rename id) 2) =
                            (first.neighbor (.agent id 2)).map (renameEnd rename) at hn2
                          rw [hn2]
                          cases hc2 : first.neighbor (.agent id 2) with
                          | none => rfl
                          | some child2 => simp only [Option.map_some, ih]
theorem Iso.outputSyntax {rename : Nat ≃ Nat} {first second : Net}
    (h : Iso rename first second) (fuel : Nat) :
    second.outputSyntax fuel = first.outputSyntax fuel := by
  have hn := h.neighbors (.free 0)
  unfold Net.outputSyntax
  rw [show renameEnd rename (.free 0) = End.free 0 from rfl] at hn
  rw [hn]
  cases first.neighbor (.free 0) with
  | none => rfl
  | some end_ => simpa only [Option.map_some, Option.bind_some] using h.readRoot fuel end_

theorem Equivalent.outputSyntax {first second : Net}
    (h : Equivalent first second) (fuel : Nat) :
    second.outputSyntax fuel = first.outputSyntax fuel := by
  rcases h with ⟨rename, hi⟩
  exact hi.outputSyntax fuel

end TriageEquivalence
