/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageReduction

/-!
Validity of source-net construction. During construction, a finite set of
holes records precisely the expected ports that are still unconnected.
-/

namespace TriageInitial
open TriageConcrete TriagePreservation TriageReduction

structure OpenValid (net : Net) (holes : Finset End) : Prop where
  ids : (net.agents.map Prod.fst).Nodup
  wires : net.used.Nodup
  fresh : net.freshIds = true
  legal : ∀ end_ ∈ holes, end_ ∈ net.expected
  covered : ∀ end_, end_ ∈ net.used ↔ end_ ∈ net.expected ∧ end_ ∉ holes

theorem OpenValid.closed {net : Net} (h : OpenValid net ∅) : net.valid = true := by
  have hwf : net.wellFormed = true := by
    apply (Net.wellFormed_iff net).mpr
    exact ⟨h.ids, h.wires,
      (fun end_ hmem => ((h.covered end_).mp hmem).1),
      (fun end_ hmem => (h.covered end_).mpr ⟨hmem, by simp⟩)⟩
  simp [Net.valid, hwf, h.fresh]

theorem expected_agent_bound {net : Net} (hfresh : net.freshIds = true)
    {id slot : Nat} (hmem : End.agent id slot ∈ net.expected) :
    id < net.nextId := by
  rw [Net.expected_eq_ports] at hmem
  rcases List.mem_append.mp hmem with hport | hfree
  · rcases (ports_agent_iff net.agents id slot).mp hport with ⟨kind, hentry, _⟩
    have hf : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
      simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using hfresh
    exact hf (id, kind) hentry
  · simp at hfree

def freshPorts (net : Net) (kind : TriageRuleModel.Kind) : List End :=
  (List.range (kind.arity + 1)).map (End.agent net.nextId)

theorem freshPorts_nodup (net : Net) (kind : TriageRuleModel.Kind) :
    (freshPorts net kind).Nodup :=
  List.nodup_range.map (by intro a b heq; exact (End.agent.inj heq).2)

theorem freshPorts_not_expected {net : Net} (hfresh : net.freshIds = true)
    (kind : TriageRuleModel.Kind) {end_ : End}
    (hnew : end_ ∈ freshPorts net kind) : end_ ∉ net.expected := by
  rcases List.mem_map.mp hnew with ⟨slot, _, rfl⟩
  intro hlegal
  have hlt := expected_agent_bound hfresh hlegal
  omega

theorem fresh_expected (net : Net) (kind : TriageRuleModel.Kind) (end_ : End) :
    end_ ∈ (net.fresh kind).2.expected ↔
      end_ ∈ net.expected ∨ end_ ∈ freshPorts net kind := by
  simp only [Net.fresh, Net.expected_eq_ports, ports, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
    freshPorts]
  tauto

theorem OpenValid.fresh_agent {net : Net} {holes : Finset End}
    (h : OpenValid net holes) (kind : TriageRuleModel.Kind) :
    OpenValid (net.fresh kind).2
      (holes ∪ (freshPorts net kind).toFinset) := by
  have hidFresh : net.nextId ∉ net.agents.map Prod.fst := by
    intro hmem
    rcases List.mem_map.mp hmem with ⟨⟨id, oldKind⟩, hentry, heq⟩
    have hf : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
      simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using h.fresh
    have hlt := hf (id, oldKind) hentry
    change id = net.nextId at heq
    omega
  constructor
  · have hd : (net.agents.map Prod.fst).Disjoint [net.nextId] := by
      rw [List.disjoint_left]
      intro id hold hnew
      have heq := List.mem_singleton.mp hnew
      subst id
      exact hidFresh hold
    simpa only [Net.fresh, List.map_append, List.map_cons, List.map_nil] using
      List.nodup_append'.2 ⟨h.ids, by simp, hd⟩
  · exact h.wires
  · have hf : ∀ entry ∈ net.agents, entry.1 < net.nextId := by
      simpa only [Net.freshIds, List.all_eq_true, decide_eq_true_eq] using h.fresh
    simp only [Net.fresh, Net.freshIds, List.all_eq_true, decide_eq_true_eq]
    intro entry hmem
    rcases List.mem_append.mp hmem with hold | hnew
    · have hlt := hf entry hold
      omega
    · have heq := List.mem_singleton.mp hnew
      subst entry
      simp
  · intro end_ hmem
    rcases Finset.mem_union.mp hmem with hold | hnew
    · exact (fresh_expected net kind end_).mpr (Or.inl (h.legal end_ hold))
    · exact (fresh_expected net kind end_).mpr
        (Or.inr (List.mem_toFinset.mp hnew))
  · intro end_
    change end_ ∈ net.used ↔ _
    rw [h.covered, fresh_expected]
    simp only [Finset.mem_union, List.mem_toFinset]
    have hn : end_ ∈ freshPorts net kind → end_ ∉ net.expected :=
      freshPorts_not_expected h.fresh kind
    tauto

theorem OpenValid.connect_holes {net : Net} {holes : Finset End}
    (h : OpenValid net holes) {a b : End}
    (ha : a ∈ holes) (hb : b ∈ holes) (hne : a ≠ b) :
    OpenValid (net.connect a b) ((holes.erase a).erase b) := by
  have haUnused : a ∉ net.used := by
    intro hmem
    exact ((h.covered a).mp hmem).2 ha
  have hbUnused : b ∉ net.used := by
    intro hmem
    exact ((h.covered b).mp hmem).2 hb
  constructor
  · exact h.ids
  · have hp : ([a, b] : List End).Nodup := by simpa using hne
    have hd : net.used.Disjoint [a, b] := by
      rw [List.disjoint_left]
      intro end_ hused hpair
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
      rcases hpair with rfl | rfl
      · exact haUnused hused
      · exact hbUnused hused
    simpa [Net.connect, Net.used, wireEnds, List.flatMap_append] using
      List.nodup_append'.2 ⟨h.wires, hp, hd⟩
  · exact h.fresh
  · intro end_ hmem
    exact h.legal end_ (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hmem))
  · intro end_
    have haLegal := h.legal a ha
    have hbLegal := h.legal b hb
    have hc := h.covered end_
    simp only [Net.connect, Net.used, wireEnds, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false, Finset.mem_erase]
    change (end_ ∈ net.used ∨ end_ = a ∨ end_ = b) ↔ _
    constructor
    · rintro (hused | rfl | rfl)
      · have hu := hc.mp hused
        exact ⟨hu.1, by tauto⟩
      · exact ⟨haLegal, by simp [hne]⟩
      · exact ⟨hbLegal, by simp [hne.symm]⟩
    · rintro ⟨hlegal, hnot⟩
      by_cases hea : end_ = a
      · exact Or.inr (Or.inl hea)
      · by_cases heb : end_ = b
        · exact Or.inr (Or.inr heb)
        · left
          exact hc.mpr ⟨hlegal, by tauto⟩

theorem OpenValid.new_port_not_hole {net : Net} {holes : Finset End}
    (h : OpenValid net holes) (slot : Nat) :
    End.agent net.nextId slot ∉ holes := by
  intro hmem
  have hlt := expected_agent_bound h.fresh (h.legal _ hmem)
  omega

theorem freshPorts_leaf (net : Net) :
    (freshPorts net .leaf).toFinset = {End.agent net.nextId 0} := by
  simp [freshPorts, TriageRuleModel.Kind.arity, List.range_succ]

theorem freshPorts_app (net : Net) :
    (freshPorts net .app).toFinset =
      {End.agent net.nextId 0, End.agent net.nextId 1, End.agent net.nextId 2} := by
  simp [freshPorts, TriageRuleModel.Kind.arity, List.range_succ]

theorem freshPorts_eval (net : Net) :
    (freshPorts net .eval).toFinset =
      {End.agent net.nextId 0, End.agent net.nextId 1} := by
  simp [freshPorts, TriageRuleModel.Kind.arity, List.range_succ]

theorem build_leaf_eq (net : Net) :
    build .leaf net = (.agent net.nextId 0, (net.fresh .leaf).2) := rfl

theorem build_app_eq (fn arg : TriageMachine.Syntax) (net : Net) :
    build (.app fn arg) net =
      let id := net.nextId
      let first := build fn (net.fresh .app).2
      let second := build arg first.2
      (.agent id 0, (second.2.connect (.agent id 1) first.1).connect
        (.agent id 2) second.1) := rfl

theorem build_open_valid (source : TriageMachine.Syntax) (net : Net)
    (holes : Finset End) (h : OpenValid net holes) :
    let result := build source net
    OpenValid result.2 (insert result.1 holes) ∧ result.1 ∉ holes := by
  induction source generalizing net holes with
  | leaf =>
      rw [build_leaf_eq]
      have hf := h.fresh_agent .leaf
      rw [freshPorts_leaf] at hf
      exact ⟨by simpa using hf, h.new_port_not_hole 0⟩
  | app fn arg ihFn ihArg =>
      let id := net.nextId
      let a0 : End := .agent id 0
      let a1 : End := .agent id 1
      let a2 : End := .agent id 2
      let baseHoles := holes ∪ (freshPorts net .app).toFinset
      let net0 := (net.fresh .app).2
      have hnet0 : OpenValid net0 baseHoles := h.fresh_agent .app
      cases hfn : build fn net0 with
      | mk fnRoot net1 =>
          have hfnValid := ihFn net0 baseHoles hnet0
          rw [hfn] at hfnValid
          cases harg : build arg net1 with
          | mk argRoot net2 =>
              have hargValid := ihArg net1 (insert fnRoot baseHoles) hfnValid.1
              rw [harg] at hargValid
              have ha0 : a0 ∈ baseHoles := by
                simp [baseHoles, freshPorts_app, a0, id]
              have ha1 : a1 ∈ baseHoles := by
                simp [baseHoles, freshPorts_app, a1, id]
              have ha2 : a2 ∈ baseHoles := by
                simp [baseHoles, freshPorts_app, a2, id]
              have hf0 : fnRoot ≠ a0 := by intro heq; exact hfnValid.2 (heq ▸ ha0)
              have hf1 : fnRoot ≠ a1 := by intro heq; exact hfnValid.2 (heq ▸ ha1)
              have hf2 : fnRoot ≠ a2 := by intro heq; exact hfnValid.2 (heq ▸ ha2)
              have hg : argRoot ≠ fnRoot ∧ argRoot ∉ baseHoles := by
                simpa only [Finset.mem_insert, not_or] using hargValid.2
              have hg0 : argRoot ≠ a0 := by intro heq; exact hg.2 (heq ▸ ha0)
              have hg1 : argRoot ≠ a1 := by intro heq; exact hg.2 (heq ▸ ha1)
              have hg2 : argRoot ≠ a2 := by intro heq; exact hg.2 (heq ▸ ha2)
              have hconnect1 := hargValid.1.connect_holes
                (a := a1) (b := fnRoot)
                (by simp [ha1]) (by simp) hf1.symm
              have hconnect2 := hconnect1.connect_holes
                (a := a2) (b := argRoot)
                (by simp [Finset.mem_erase, ha2, hf2.symm, a1, a2])
                (by simp [Finset.mem_erase, hg.1, hg1]) hg2.symm
              have hfinalHoles :
                  ((((insert argRoot (insert fnRoot baseHoles)).erase a1).erase fnRoot).erase a2).erase argRoot =
                    insert a0 holes := by
                have hn1 : a1 ∉ holes := h.new_port_not_hole 1
                have hn2 : a2 ∉ holes := h.new_port_not_hole 2
                have h01 : a0 ≠ a1 := by simp [a0, a1]
                have h02 : a0 ≠ a2 := by simp [a0, a2]
                have h12 : a1 ≠ a2 := by simp [a1, a2]
                have hbase : baseHoles = insert a0 (insert a1 (insert a2 holes)) := by
                  simp [baseHoles, freshPorts_app, a0, a1, a2, id]
                have hfH : fnRoot ∉ holes := by
                  intro hm
                  exact hfnValid.2 (Finset.mem_union.mpr (Or.inl hm))
                have hgH : argRoot ∉ holes := by
                  intro hm
                  exact hg.2 (Finset.mem_union.mpr (Or.inl hm))
                simp [hbase, Finset.erase_insert_of_ne,
                  hf0, hf1, hf2, hg0, hg1, hg2, hg.1,
                  hfH, hgH, h01, h02, h12, hn1, hn2]
              rw [hfinalHoles] at hconnect2
              rw [build_app_eq]
              dsimp only
              rw [show (net.fresh .app).2 = net0 from rfl, hfn]
              dsimp only
              rw [harg]
              exact ⟨hconnect2, h.new_port_not_hole 0⟩

theorem empty_open_valid : OpenValid ({} : Net) {End.free 0} := by
  constructor <;>
    simp [Net.expected, Net.used, wireEnds, Net.freshIds]

theorem initial_eq (source : TriageMachine.Syntax) :
    initial source =
      let built := build source ({} : Net)
      let evalId := built.2.nextId
      let evalNet := (built.2.fresh .eval).2
      (evalNet.connect built.1 (.agent evalId 0)).connect
        (.agent evalId 1) (.free 0) := rfl

/-- Every finite source syntax builds a valid closed concrete net. -/
theorem initial_valid (source : TriageMachine.Syntax) :
    (initial source).valid = true := by
  cases hb : build source ({} : Net) with
  | mk root built =>
      have hbuild := build_open_valid source ({} : Net) {End.free 0} empty_open_valid
      rw [hb] at hbuild
      let e0 : End := .agent built.nextId 0
      let e1 : End := .agent built.nextId 1
      let evalNet := (built.fresh .eval).2
      let evalHoles := insert root {End.free 0} ∪ (freshPorts built .eval).toFinset
      have heval : OpenValid evalNet evalHoles := hbuild.1.fresh_agent .eval
      have hroot : root ∈ evalHoles := by simp [evalHoles]
      have he0 : e0 ∈ evalHoles := by simp [evalHoles, freshPorts_eval, e0]
      have he1 : e1 ∈ evalHoles := by simp [evalHoles, freshPorts_eval, e1]
      have hfree : End.free 0 ∈ evalHoles := by simp [evalHoles]
      have hr0 : root ≠ e0 := by
        intro heq
        exact hbuild.1.new_port_not_hole 0 (heq ▸ Finset.mem_insert_self ..)
      have hr1 : root ≠ e1 := by
        intro heq
        exact hbuild.1.new_port_not_hole 1 (heq ▸ Finset.mem_insert_self ..)
      have hrf : root ≠ End.free 0 := by
        simpa only [Finset.mem_singleton] using hbuild.2
      have h01 : e0 ≠ e1 := by simp [e0, e1]
      have hc1 := heval.connect_holes hroot he0 hr0
      have hc2 := hc1.connect_holes (a := e1) (b := .free 0)
        (by simp [Finset.mem_erase, he1, hr1.symm, h01.symm])
        (by simp [Finset.mem_erase, hfree, e0, hrf.symm])
        (by simp [e1])
      have hclosed : (((evalHoles.erase root).erase e0).erase e1).erase (.free 0) = ∅ := by
        ext end_
        simp only [evalHoles, freshPorts_eval, Finset.mem_erase,
          Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.notMem_empty]
        dsimp only [e0, e1]
        tauto
      rw [hclosed] at hc2
      rw [initial_eq, hb]
      exact hc2.closed

theorem initial_schedule_valid (source : TriageMachine.Syntax)
    {result : Net} (hsteps : Steps (initial source) result) :
    result.valid = true := Steps.preserves_valid hsteps (initial_valid source)

theorem initial_run_valid (source : TriageMachine.Syntax) (fuel : Nat) :
    ((initial source).run fuel).valid = true :=
  Net.run_preserves_valid fuel (initial_valid source)

theorem initial_trace_valid (source : TriageMachine.Syntax) (fuel : Nat) :
    ((initial source).trace fuel).all Net.valid = true :=
  Net.trace_valid fuel (initial_valid source)

end TriageInitial
