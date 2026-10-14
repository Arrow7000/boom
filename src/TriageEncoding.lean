import TriageResidual

/-!
A structural relation between sourceTerm and concrete agent/port graphs. Its
readback theorem and source-builder theorem hold for every finite sourceTerm.
This supplies the source side of the semantic simulation; it does not yet
describe evaluator continuations or resource agents during execution.
-/

namespace TriageEncoding
open TriageConcrete TriageRuleModel TriageMachine TriageInitial
open TriageBoundary TriagePreservation TriageResidual TriageReduction

def Linked (net : Net) (first second : TriageConcrete.End) : Prop :=
  (first, second) ∈ net.wires ∨ (second, first) ∈ net.wires

inductive Represents (net : Net) : TriageConcrete.End → Syntax → Prop where
  | leaf {id : Nat} : (id, Kind.leaf) ∈ net.agents →
      Represents net (.agent id 0) .leaf
  | stem {id : Nat} {child : TriageConcrete.End} {sourceTerm : Syntax} :
      (id, Kind.stem) ∈ net.agents → Linked net (.agent id 1) child →
      Represents net child sourceTerm → Represents net (.agent id 0) (TriageMachine.stem sourceTerm)
  | fork {id : Nat} {left right : TriageConcrete.End} {fn arg : Syntax} :
      (id, Kind.fork) ∈ net.agents → Linked net (.agent id 1) left →
      Linked net (.agent id 2) right → Represents net left fn → Represents net right arg →
      Represents net (.agent id 0) (TriageMachine.fork fn arg)
  | app {id : Nat} {left right : TriageConcrete.End} {fn arg : Syntax} :
      (id, Kind.app) ∈ net.agents → Linked net (.agent id 1) left →
      Linked net (.agent id 2) right → Represents net left fn → Represents net right arg →
      Represents net (.agent id 0) (.app fn arg)

structure Extends (first second : Net) : Prop where
  agents : first.agents ⊆ second.agents
  wires : first.wires ⊆ second.wires

theorem Extends.refl (net : Net) : Extends net net := ⟨fun _ h => h, fun _ h => h⟩
theorem Extends.trans {first second third : Net}
    (hf : Extends first second) (hs : Extends second third) : Extends first third :=
  ⟨fun _ h => hs.agents (hf.agents h), fun _ h => hs.wires (hf.wires h)⟩

theorem fresh_extends (net : Net) (kind : Kind) : Extends net (net.fresh kind).2 :=
  ⟨fun _ h => List.mem_append_left _ h, fun _ h => h⟩

theorem connect_extends (net : Net) (a b : TriageConcrete.End) :
    Extends net (net.connect a b) :=
  ⟨fun _ h => h, fun _ h => List.mem_append_left _ h⟩

theorem Linked.extends {first second : Net} (h : Extends first second)
    {a b : TriageConcrete.End} (hl : Linked first a b) : Linked second a b :=
  hl.elim (fun hw => Or.inl (h.wires hw)) (fun hw => Or.inr (h.wires hw))

theorem Represents.extends {first second : Net} (h : Extends first second)
    {root : TriageConcrete.End} {sourceTerm : Syntax} (hr : Represents first root sourceTerm) :
    Represents second root sourceTerm := by
  induction hr with
  | leaf hk => exact .leaf (h.agents hk)
  | stem hk hl _ ih => exact .stem (h.agents hk) (hl.extends h) ih
  | fork hk hl hr _ _ ihl ihr => exact .fork (h.agents hk) (hl.extends h) (hr.extends h) ihl ihr
  | app hk hl hr _ _ ihl ihr => exact .app (h.agents hk) (hl.extends h) (hr.extends h) ihl ihr

theorem build_extends (source : Syntax) (net : Net) :
    Extends net (build source net).2 := by
  induction source generalizing net with
  | leaf => exact fresh_extends net .leaf
  | app fn arg ihFn ihArg =>
      rw [build_app_eq]
      exact (fresh_extends net .app).trans ((ihFn _).trans ((ihArg _).trans
        ((connect_extends _ _ _).trans (connect_extends _ _ _))))

theorem build_represents (source : Syntax) (net : Net) :
    Represents (build source net).2 (build source net).1 source := by
  induction source generalizing net with
  | leaf =>
      rw [build_leaf_eq]
      apply Represents.leaf
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | app fn arg ihFn ihArg =>
      rw [build_app_eq]
      let base := (net.fresh .app).2
      let first := build fn base
      let second := build arg first.2
      let final := (second.2.connect (.agent net.nextId 1) first.1).connect
        (.agent net.nextId 2) second.1
      have hbase : Extends base final := (build_extends fn base).trans
        ((build_extends arg first.2).trans
          ((connect_extends _ _ _).trans (connect_extends _ _ _)))
      have hsecond : Extends second.2 final :=
        (connect_extends _ _ _).trans (connect_extends _ _ _)
      apply Represents.app (left := first.1) (right := second.1)
      · apply hbase.agents
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · left
        exact (connect_extends _ _ _).wires
          (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      · left
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
      · exact (ihFn base).extends ((build_extends arg first.2).trans hsecond)
      · exact (ihArg first.2).extends hsecond

def depth : Syntax → Nat
  | .leaf => 1
  | .app fn arg => 1 + max (depth fn) (depth arg)

theorem Linked.neighbor {net : Net} (hwf : net.wellFormed = true)
    {a b : TriageConcrete.End} (h : Linked net a b) : net.neighbor a = some b := by
  rcases h with hab | hba
  · exact neighborIn_of_mem (net.wellFormed_nodup hwf) hab
  · exact neighborIn_of_mem_right (net.wellFormed_nodup hwf) hba

theorem Represents.readRoot {net : Net} (hwf : net.wellFormed = true)
    {root : TriageConcrete.End} {sourceTerm : Syntax} (h : Represents net root sourceTerm)
    (fuel : Nat) (hfuel : depth sourceTerm ≤ fuel) : net.readRoot fuel root = some sourceTerm := by
  have hids := (net.wellFormed_iff.mp hwf).1
  induction h generalizing fuel with
  | leaf hk =>
      cases fuel with
      | zero => simp [depth] at hfuel
      | succ fuel => simp [Net.readRoot, Net.kind_of_mem hids hk]
  | @stem id child childTerm hk hl _ ih =>
      cases fuel with
      | zero => simp [TriageMachine.stem, depth] at hfuel
      | succ fuel =>
          have hc : depth childTerm ≤ fuel := by
            simp only [TriageMachine.stem, depth] at hfuel
            omega
          simp [Net.readRoot, Net.kind_of_mem hids hk, hl.neighbor hwf, ih fuel hc]
  | @fork id left right fn arg hk hl hr _ _ ihl ihr =>
      cases fuel with
      | zero => simp [TriageMachine.fork, TriageMachine.stem, depth] at hfuel
      | succ fuel =>
          have hc : depth fn ≤ fuel ∧ depth arg ≤ fuel := by
            simp only [TriageMachine.fork, TriageMachine.stem, depth] at hfuel
            omega
          simp [Net.readRoot, Net.kind_of_mem hids hk, hl.neighbor hwf,
            hr.neighbor hwf, ihl fuel hc.1, ihr fuel hc.2]
  | @app id left right fn arg hk hl hr _ _ ihl ihr =>
      cases fuel with
      | zero => simp [depth] at hfuel
      | succ fuel =>
          have hc : depth fn ≤ fuel ∧ depth arg ≤ fuel := by
            simp only [depth] at hfuel
            omega
          simp [Net.readRoot, Net.kind_of_mem hids hk, hl.neighbor hwf,
            hr.neighbor hwf, ihl fuel hc.1, ihr fuel hc.2]

theorem initial_represents (source : Syntax) :
    Represents (initial source) (build source {}).1 source := by
  apply (build_represents source {}).extends
  exact (fresh_extends _ .eval).trans
    ((connect_extends _ _ _).trans (connect_extends _ _ _))

/-- Reading the source side of the initial evaluator reconstructs every
source exactly, without any bound on the size of the term. -/
theorem initial_source_readback (source : Syntax) (fuel : Nat)
    (hfuel : depth source ≤ fuel) :
    (initial source).readRoot fuel (build source {}).1 = some source :=
  (initial_represents source).readRoot (valid_wellFormed (initial_valid source)) fuel hfuel

theorem Represents.unique {net : Net} (hwf : net.wellFormed = true)
    {root : TriageConcrete.End} {first second : Syntax}
    (hf : Represents net root first) (hs : Represents net root second) :
    first = second := by
  have hfr := hf.readRoot hwf (max (depth first) (depth second)) (Nat.le_max_left ..)
  have hsr := hs.readRoot hwf (max (depth first) (depth second)) (Nat.le_max_right ..)
  exact Option.some.inj (hfr.symm.trans hsr)

theorem Linked.rename {first second : Net} {rename : Nat ≃ Nat}
    (h : TriageEquivalence.Iso rename first second) (hwf : first.wellFormed = true)
    {a b : TriageConcrete.End} (hl : Linked first a b) :
    Linked second (TriageEquivalence.renameEnd rename a) (TriageEquivalence.renameEnd rename b) := by
  have hn := h.neighbors a
  rw [hl.neighbor hwf] at hn
  exact neighborIn_sound hn

/-- Structural representation is independent of the numeric agent IDs. -/
theorem Represents.rename {first second : Net} {rename : Nat ≃ Nat}
    (h : TriageEquivalence.Iso rename first second) (hwf : first.wellFormed = true)
    {root : TriageConcrete.End} {source : Syntax} (hr : Represents first root source) :
    Represents second (TriageEquivalence.renameEnd rename root) source := by
  have hkind : ∀ id kind, (id, kind) ∈ first.agents → (rename id, kind) ∈ second.agents := by
    intro id kind hm
    apply Net.kind_mem
    rw [h.kinds]
    exact Net.kind_of_mem (first.wellFormed_iff.mp hwf).1 hm
  induction hr with
  | leaf hk => exact .leaf (hkind _ _ hk)
  | stem hk hl _ ih => exact .stem (hkind _ _ hk) (hl.rename h hwf) ih
  | fork hk hl hr _ _ ihl ihr =>
      exact .fork (hkind _ _ hk) (hl.rename h hwf) (hr.rename h hwf) ihl ihr
  | app hk hl hr _ _ ihl ihr =>
      exact .app (hkind _ _ hk) (hl.rename h hwf) (hr.rename h hwf) ihl ihr

theorem Represents.principal {net : Net} {root : TriageConcrete.End} {source : Syntax}
    (h : Represents net root source) : ∃ id, root = .agent id 0 := by
  cases h <;> exact ⟨_, rfl⟩

theorem Linked.symm {net : Net} {a b : TriageConcrete.End}
    (h : Linked net a b) : Linked net b a := h.elim Or.inr Or.inl

/-- A source child attached to an auxiliary port cannot be an agent of any
active pair: its principal port is already attached to that auxiliary port. -/
theorem auxiliary_child_not_active {net : Net} (hwf : net.wellFormed = true)
    {left right parent slot child : Nat} (hactive : net.Active left right)
    (hslot : slot ≠ 0) (hlink : Linked net (.agent parent slot) (.agent child 0)) :
    child ≠ left ∧ child ≠ right := by
  have hchild := hlink.symm.neighbor hwf
  have hleft := hactive.2.2
  have hright : net.neighbor (.agent right 0) = some (.agent left 0) :=
    neighborIn_symmetric (net.wellFormed_nodup hwf) hleft
  constructor
  · intro heq
    rw [heq, hleft] at hchild
    have hs := (TriageConcrete.End.agent.inj (Option.some.inj hchild)).2
    exact hslot hs.symm
  · intro heq
    rw [heq, hright] at hchild
    have hs := (TriageConcrete.End.agent.inj (Option.some.inj hchild)).2
    exact hslot hs.symm

theorem represented_child_outside {net : Net} (hwf : net.wellFormed = true)
    {left right parent slot : Nat} {child : TriageConcrete.End} {source : Syntax}
    (hactive : net.Active left right) (hslot : slot ≠ 0)
    (hlink : Linked net (.agent parent slot) child) (hr : Represents net child source) :
    belongs left right child = false := by
  rcases hr.principal with ⟨id, rfl⟩
  rcases auxiliary_child_not_active hwf hactive hslot hlink with ⟨hl, hr⟩
  simp [belongs, hl, hr]

theorem Linked.replace {net : Net} (rule : Rule) (left right : Nat)
    {a b : TriageConcrete.End} (h : Linked net a b)
    (ha : belongs left right a = false) (hb : belongs left right b = false) :
    Linked (net.replace rule left right) a b := by
  rcases h with hab | hba
  · exact Or.inl (Net.replace_retains_wire net rule left right hab ha hb)
  · exact Or.inr (Net.replace_retains_wire net rule left right hba hb ha)

/-- Every represented source whose root is outside the contracted pair is
preserved exactly. Its internal source agents cannot be active pairs, even
when the encoded source would be reducible as a tree-calculus term. -/
theorem Represents.replace {net : Net} (hvalid : net.valid = true)
    {rule : Rule} {left right : Nat}
    (hchoice : (rule, left, right) ∈ net.redexChoices)
    {root : TriageConcrete.End} {source : Syntax} (h : Represents net root source)
    (hroot : belongs left right root = false) :
    Represents (net.replace rule left right) root source := by
  have hwf := valid_wellFormed hvalid
  have hactive := (Net.redexChoice_sound hwf hchoice).2.1
  have hkind : ∀ id kind, (id, kind) ∈ net.agents →
      belongs left right (.agent id 0) = false →
      (id, kind) ∈ (net.replace rule left right).agents := by
    intro id kind hk hb
    have hi : id ≠ left ∧ id ≠ right := by simpa [belongs] using hb
    exact Net.kind_mem (Net.replace_retains_kind hvalid rule
      (Net.kind_of_mem (net.wellFormed_iff.mp hwf).1 hk) hi.1 hi.2)
  revert hroot
  induction h with
  | leaf hk => intro hb; exact .leaf (hkind _ _ hk hb)
  | @stem id child childTerm hk hl hr ih =>
      intro hb
      have hc := represented_child_outside hwf hactive (by decide : 1 ≠ 0) hl hr
      have hb1 : belongs left right (.agent id 1) = false := hb
      exact .stem (hkind _ _ hk hb) (hl.replace rule left right hb1 hc) (ih hc)
  | @fork id fnRoot argRoot fn arg hk hl hr hfn harg ihl ihr =>
      intro hb
      have hfnOutside := represented_child_outside hwf hactive (by decide : 1 ≠ 0) hl hfn
      have hargOutside := represented_child_outside hwf hactive (by decide : 2 ≠ 0) hr harg
      have hb1 : belongs left right (.agent id 1) = false := hb
      have hb2 : belongs left right (.agent id 2) = false := hb
      exact .fork (hkind _ _ hk hb) (hl.replace rule left right hb1 hfnOutside)
        (hr.replace rule left right hb2 hargOutside) (ihl hfnOutside) (ihr hargOutside)
  | @app id fnRoot argRoot fn arg hk hl hr hfn harg ihl ihr =>
      intro hb
      have hfnOutside := represented_child_outside hwf hactive (by decide : 1 ≠ 0) hl hfn
      have hargOutside := represented_child_outside hwf hactive (by decide : 2 ≠ 0) hr harg
      have hb1 : belongs left right (.agent id 1) = false := hb
      have hb2 : belongs left right (.agent id 2) = false := hb
      exact .app (hkind _ _ hk hb) (hl.replace rule left right hb1 hfnOutside)
        (hr.replace rule left right hb2 hargOutside) (ihl hfnOutside) (ihr hargOutside)

end TriageEncoding
