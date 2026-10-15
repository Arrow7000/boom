/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageBoundary
import Mathlib.Data.Finset.Card

/-!
A declarative account of the alternating interface traversal performed by
`TriageConcrete.follow`. The executable function uses fuel; `Walk` records
the exact number of layer edges on a successful path.
-/

namespace TriagePaths
open TriageConcrete TriageBoundary

def selected (outer inner : Layer) (useInner : Bool) : Layer :=
  if useInner then inner else outer

inductive Walk (outer inner : Layer) : Nat → Node → Bool → End → Prop where
  | stop {node useInner end_} :
      layerNeighbor (selected outer inner useInner) node =
        some (.real end_) →
      Walk outer inner 1 node useInner end_
  | hop {n node useInner side slot end_} :
      layerNeighbor (selected outer inner useInner) node =
        some (.iface side slot) →
      Walk outer inner n (.iface side slot) (!useInner) end_ →
      Walk outer inner (n + 1) node useInner end_

theorem follow_sound (outer inner : Layer) :
    ∀ fuel node useInner end_,
      follow outer inner fuel node useInner = some end_ →
      ∃ n, n ≤ fuel ∧ Walk outer inner n node useInner end_ := by
  intro fuel
  induction fuel with
  | zero =>
      intro node useInner end_ h
      simp [follow] at h
  | succ fuel ih =>
      intro node useInner end_ h
      change (layerNeighbor (selected outer inner useInner) node).bind
        (fun next => match next with
          | .real endpoint => some endpoint
          | .iface _ _ => follow outer inner fuel next (!useInner)) =
        some end_ at h
      cases hnext : layerNeighbor (selected outer inner useInner) node with
      | none => simp [hnext] at h
      | some next =>
          cases next with
          | real endpoint =>
              simp [hnext] at h
              subst end_
              exact ⟨1, by omega, Walk.stop hnext⟩
          | iface side slot =>
              have hrest : follow outer inner fuel (.iface side slot)
                  (!useInner) = some end_ := by
                simpa [hnext] using h
              rcases ih _ _ _ hrest with ⟨n, hbound, hwalk⟩
              exact ⟨n + 1, by omega, Walk.hop hnext hwalk⟩

theorem follow_complete (outer inner : Layer) {n node useInner end_}
    (hwalk : Walk outer inner n node useInner end_) :
    ∀ fuel, n ≤ fuel →
      follow outer inner fuel node useInner = some end_ := by
  induction hwalk with
  | stop hnext =>
      intro fuel hbound
      cases fuel with
      | zero => omega
      | succ fuel =>
          change (layerNeighbor (selected outer inner _) _).bind _ = _
          simp [hnext]
  | hop hnext _ ih =>
      intro fuel hbound
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hsmaller := Nat.le_of_succ_le_succ hbound
          change (layerNeighbor (selected outer inner _) _).bind _ = _
          simpa [hnext] using ih fuel hsmaller

theorem Walk.endpoint_unique {outer inner : Layer}
    {n m : Nat} {node : Node} {useInner : Bool} {first second : End}
    (hfirst : Walk outer inner n node useInner first)
    (hsecond : Walk outer inner m node useInner second) :
    first = second := by
  induction hfirst generalizing m second with
  | stop hnext =>
      cases hsecond with
      | stop hnext' =>
          rw [hnext] at hnext'
          simpa using hnext'
      | hop hnext' _ =>
          rw [hnext] at hnext'
          cases hnext'
  | hop hnext _ ih =>
      cases hsecond with
      | stop hnext' =>
          rw [hnext] at hnext'
          cases hnext'
      | hop hnext' hrest =>
          rw [hnext] at hnext'
          injection hnext' with heq
          cases heq
          exact ih hrest

theorem Walk.length_unique {outer inner : Layer}
    {n m : Nat} {node : Node} {useInner : Bool} {first second : End}
    (hfirst : Walk outer inner n node useInner first)
    (hsecond : Walk outer inner m node useInner second) :
    n = m := by
  induction hfirst generalizing m second with
  | stop hnext =>
      cases hsecond with
      | stop _ => rfl
      | hop hnext' _ =>
          rw [hnext] at hnext'
          cases hnext'
  | hop hnext _ ih =>
      cases hsecond with
      | stop hnext' =>
          rw [hnext] at hnext'
          cases hnext'
      | hop hnext' hrest =>
          rw [hnext] at hnext'
          injection hnext' with heq
          cases heq
          exact congrArg Nat.succ (ih hrest)

def trace (outer inner : Layer) : Nat → Node → Bool → List (Node × Bool)
  | 0, _, _ => []
  | fuel + 1, node, useInner =>
      (node, useInner) ::
        match layerNeighbor (selected outer inner useInner) node with
        | some (.iface side slot) =>
            trace outer inner fuel (.iface side slot) (!useInner)
        | _ => []

theorem Walk.trace_length {outer inner : Layer}
    {n : Nat} {node : Node} {useInner : Bool} {end_ : End}
    (hwalk : Walk outer inner n node useInner end_) :
    (trace outer inner n node useInner).length = n := by
  induction hwalk with
  | stop hnext => simp [trace, hnext]
  | hop hnext _ ih => simp [trace, hnext, ih]

theorem Walk.trace_member {outer inner : Layer}
    {n : Nat} {node : Node} {useInner : Bool} {end_ : End}
    (hwalk : Walk outer inner n node useInner end_) :
    ∀ {state : Node × Bool},
      state ∈ trace outer inner n node useInner →
      ∃ m, m ≤ n ∧ Walk outer inner m state.1 state.2 end_ := by
  induction hwalk with
  | stop hnext =>
      intro state hmem
      simp [trace, hnext] at hmem
      subst state
      exact ⟨1, le_rfl, Walk.stop hnext⟩
  | hop hnext hrest ih =>
      intro state hmem
      simp only [trace, hnext, List.mem_cons] at hmem
      rcases hmem with hhere | htail
      · subst state
        exact ⟨_, le_rfl, Walk.hop hnext hrest⟩
      · rcases ih htail with ⟨m, hbound, hwalk⟩
        exact ⟨m, by omega, hwalk⟩

theorem Walk.trace_nodup {outer inner : Layer}
    {n : Nat} {node : Node} {useInner : Bool} {end_ : End}
    (hwalk : Walk outer inner n node useInner end_) :
    (trace outer inner n node useInner).Nodup := by
  induction hwalk with
  | stop hnext => simp [trace, hnext]
  | hop hnext hrest ih =>
      rename_i steps current direction side slot final
      have hnot : (current, direction) ∉
          trace outer inner steps (.iface side slot) (!direction) := by
        intro hmem
        rcases Walk.trace_member hrest hmem with ⟨m, hbound, hshort⟩
        have heq := Walk.length_unique (Walk.hop hnext hrest) hshort
        omega
      simp [trace, hnext, hnot, ih]

theorem Walk.length_le_universe {outer inner : Layer}
    {n : Nat} {node : Node} {useInner : Bool} {end_ : End}
    (hwalk : Walk outer inner n node useInner end_)
    (states : List (Node × Bool)) (hstates : states.Nodup)
    (hsubset : ∀ state ∈ trace outer inner n node useInner,
      state ∈ states) :
    n ≤ states.length := by
  have hfin : (trace outer inner n node useInner).toFinset ⊆
      states.toFinset := by
    intro state hmem
    exact List.mem_toFinset.mpr
      (hsubset state (List.mem_toFinset.mp hmem))
  have hcard := Finset.card_le_card hfin
  rw [List.toFinset_card_of_nodup (Walk.trace_nodup hwalk),
    List.toFinset_card_of_nodup hstates,
    Walk.trace_length hwalk] at hcard
  exact hcard

def ruleStates (rule : TriageRuleModel.Rule) : List (Node × Bool) :=
  (ruleIfaces rule).map (fun node => (node, false)) ++
  (ruleIfaces rule).map (fun node => (node, true))

theorem ruleStates_length (rule : TriageRuleModel.Rule) :
    (ruleStates rule).length =
      2 * (rule.left.arity + rule.right.arity) := by
  simp [ruleStates, ruleIfaces_length]
  omega

theorem ruleStates_nodup (rule : TriageRuleModel.Rule) :
    (ruleStates rule).Nodup := by
  apply List.nodup_append'.2
  constructor
  · exact (ruleIfaces_nodup rule).map (by intro a b h; exact (Prod.mk.inj h).1)
  constructor
  · exact (ruleIfaces_nodup rule).map (by intro a b h; exact (Prod.mk.inj h).1)
  · rw [List.disjoint_left]
    intro state hfalse htrue
    rcases List.mem_map.mp hfalse with ⟨_, _, heqFalse⟩
    rcases List.mem_map.mp htrue with ⟨_, _, heqTrue⟩
    rw [← heqFalse] at heqTrue
    cases heqTrue

theorem mem_ruleStates {rule : TriageRuleModel.Rule}
    {node : Node} {direction : Bool}
    (hnode : node ∈ ruleIfaces rule) :
    (node, direction) ∈ ruleStates rule := by
  cases direction <;>
    simp [ruleStates, hnode]

theorem ruleStates_node_mem {rule : TriageRuleModel.Rule}
    {state : Node × Bool}
    (hstate : state ∈ ruleStates rule) :
    state.1 ∈ ruleIfaces rule := by
  rcases List.mem_append.mp hstate with hfalse | htrue
  · rcases List.mem_map.mp hfalse with ⟨node, hnode, heq⟩
    have hn := congrArg Prod.fst heq
    exact hn ▸ hnode
  · rcases List.mem_map.mp htrue with ⟨node, hnode, heq⟩
    have hn := congrArg Prod.fst heq
    exact hn ▸ hnode

theorem Walk.trace_subset_ruleStates {outer inner : Layer}
    (rule : TriageRuleModel.Rule)
    (hclosed : ∀ current direction side slot,
      layerNeighbor (selected outer inner direction) current =
        some (.iface side slot) →
      Node.iface side slot ∈ ruleIfaces rule)
    {n : Nat} {node : Node} {direction : Bool} {end_ : End}
    (hwalk : Walk outer inner n node direction end_) :
    node ∈ ruleIfaces rule →
    ∀ state ∈ trace outer inner n node direction,
      state ∈ ruleStates rule := by
  induction hwalk with
  | stop hnext =>
      intro hstart state hmem
      simp [trace, hnext] at hmem
      subst state
      exact mem_ruleStates hstart
  | hop hnext hrest ih =>
      rename_i steps current useInner side slot final
      intro hstart state hmem
      simp only [trace, hnext, List.mem_cons] at hmem
      rcases hmem with hhere | htail
      · subst state
        exact mem_ruleStates hstart
      · exact ih (hclosed current useInner side slot hnext) state htail

theorem Walk.length_le_rule_fuel {outer inner : Layer}
    (rule : TriageRuleModel.Rule)
    (hclosed : ∀ current direction side slot,
      layerNeighbor (selected outer inner direction) current =
        some (.iface side slot) →
      Node.iface side slot ∈ ruleIfaces rule)
    {n : Nat} {node : Node} {direction : Bool} {end_ : End}
    (hwalk : Walk outer inner n node direction end_)
    (hstart : node ∈ ruleIfaces rule) :
    n ≤ 2 * (rule.left.arity + rule.right.arity) := by
  have hbound := hwalk.length_le_universe (ruleStates rule)
    (ruleStates_nodup rule)
    (hwalk.trace_subset_ruleStates rule hclosed hstart)
  simpa [ruleStates_length] using hbound

theorem concrete_iface_closed {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) :
    ∀ current direction side slot,
      layerNeighbor
        (selected (oldLayer net left right)
          (ruleLayer rule net.nextId) direction) current =
        some (.iface side slot) →
      Node.iface side slot ∈ ruleIfaces rule := by
  intro current direction side slot hnext
  cases direction with
  | false =>
      have hmem := layerNeighbor_target_mem hnext
      exact oldLayer_iface_mem_ruleIfaces hwf rule hactive
        hleftkind hrightkind hmem
  | true =>
      have hmem := layerNeighbor_target_mem hnext
      exact ruleLayer_iface_mem_ruleIfaces hrule net.nextId side slot hmem

/-- Any terminating concrete interface walk fits within the fuel chosen by
`Net.replace`; extra fuel cannot change its endpoint. -/
theorem concrete_follow_fuel_sufficient {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    {side slot : Nat}
    (hstart : Node.iface side slot ∈ ruleIfaces rule)
    (direction : Bool) (end_ : End)
    (hexists : ∃ fuel,
      follow (oldLayer net left right) (ruleLayer rule net.nextId)
        fuel (.iface side slot) direction = some end_) :
    follow (oldLayer net left right) (ruleLayer rule net.nextId)
      (2 * (rule.left.arity + rule.right.arity) + 2)
      (.iface side slot) direction = some end_ := by
  rcases hexists with ⟨fuel, hfollow⟩
  rcases follow_sound _ _ fuel _ _ _ hfollow with
    ⟨n, _, hwalk⟩
  have hbound := hwalk.length_le_rule_fuel rule
    (concrete_iface_closed hwf hrule hactive hleftkind hrightkind)
    hstart
  apply follow_complete _ _ hwalk
  omega

inductive Chain {α : Type} (step : α → Option α) : Nat → α → Prop where
  | done {state} : step state = none → Chain step 0 state
  | next {n state successor} :
      step state = some successor →
      Chain step n successor →
      Chain step (n + 1) state

/-- A finite injective partial transition cannot loop when its starting
state has no predecessor. -/
theorem Chain.exists_bounded {α : Type} [DecidableEq α]
    (step : α → Option α)
    (hinjective : ∀ a b target,
      step a = some target → step b = some target → a = b)
    (states : List α) (start : α)
    (hclosed : ∀ state ∈ states, ∀ successor,
      step state = some successor → successor ∈ states)
    (hstart : start ∈ states)
    (hnoPred : ∀ state ∈ states, step state ≠ some start) :
    ∃ n, n ≤ states.length ∧ Chain step n start := by
  suffices general : ∀ size (states : List α) (start : α),
      states.length = size →
      (∀ state ∈ states, ∀ successor,
        step state = some successor → successor ∈ states) →
      start ∈ states →
      (∀ state ∈ states, step state ≠ some start) →
      ∃ n, n ≤ states.length ∧ Chain step n start from
    general states.length states start rfl hclosed hstart hnoPred
  intro size
  induction size using Nat.strong_induction_on with
  | h size ih =>
      intro states start hsize hclosed hstart hnoPred
      cases hstep : step start with
      | none =>
          exact ⟨0, by omega, Chain.done hstep⟩
      | some successor =>
          let smaller := states.filter (fun state => decide (state ≠ start))
          have hsuccessor : successor ∈ states :=
            hclosed start hstart successor hstep
          have hne : successor ≠ start := by
            intro heq
            exact hnoPred start hstart (heq ▸ hstep)
          have hsmallMem : successor ∈ smaller := by
            exact List.mem_filter.mpr ⟨hsuccessor, by simpa using hne⟩
          have hsmaller : smaller.length < size := by
            rw [← hsize]
            exact List.length_filter_lt_length_iff_exists.mpr
              ⟨start, hstart, by simp⟩
          have hsmallClosed : ∀ state ∈ smaller, ∀ target,
              step state = some target → target ∈ smaller := by
            intro state hmem target htarget
            have hold : state ∈ states := (List.mem_filter.mp hmem).1
            have htargetMem := hclosed state hold target htarget
            have htargetNe : target ≠ start := by
              intro heq
              exact hnoPred state hold (heq ▸ htarget)
            exact List.mem_filter.mpr
              ⟨htargetMem, by simpa using htargetNe⟩
          have hsmallNoPred : ∀ state ∈ smaller,
              step state ≠ some successor := by
            intro state hmem htarget
            have heq := hinjective state start successor htarget hstep
            have hneStart : state ≠ start := by
              simpa using (List.mem_filter.mp hmem).2
            exact hneStart heq
          rcases ih smaller.length hsmaller smaller successor rfl
            hsmallClosed hsmallMem hsmallNoPred with ⟨n, hbound, hchain⟩
          exact ⟨n + 1, by omega, Chain.next hstep hchain⟩

def nextIface? (outer inner : Layer) (state : Node × Bool) :
    Option (Node × Bool) :=
  match state.1 with
  | .real _ => none
  | .iface _ _ =>
      match layerNeighbor (selected outer inner state.2) state.1 with
      | some (.iface side slot) => some (.iface side slot, !state.2)
      | _ => none

theorem layerNeighbor_injective {layer : Layer}
    (hn : (layerEnds layer).Nodup)
    {a b target : Node}
    (ha : layerNeighbor layer a = some target)
    (hb : layerNeighbor layer b = some target) : a = b := by
  have hta := layerNeighbor_symmetric hn ha
  have htb := layerNeighbor_symmetric hn hb
  exact Option.some.inj (hta.symm.trans htb)

theorem nextIface?_sound {outer inner : Layer}
    {state target : Node × Bool}
    (h : nextIface? outer inner state = some target) :
    (∃ side slot, state.1 = .iface side slot) ∧
    (∃ side slot, target.1 = .iface side slot) ∧
    target.2 = !state.2 ∧
    layerNeighbor (selected outer inner state.2) state.1 =
      some target.1 := by
  rcases state with ⟨node, direction⟩
  cases node with
  | real end_ => simp [nextIface?] at h
  | iface side slot =>
      refine ⟨⟨side, slot, rfl⟩, ?_⟩
      unfold nextIface? at h
      simp only at h
      cases hnext : layerNeighbor (selected outer inner direction)
          (.iface side slot) with
      | none => simp [hnext] at h
      | some next =>
          cases next with
          | real end_ => simp [hnext] at h
          | iface nextSide nextSlot =>
              simp [hnext] at h
              subst target
              refine ⟨⟨nextSide, nextSlot, rfl⟩, rfl, ?_⟩
              simp

theorem nextIface?_injective {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup) :
    ∀ a b target,
      nextIface? outer inner a = some target →
      nextIface? outer inner b = some target → a = b := by
  intro a b target ha hb
  have sa := nextIface?_sound ha
  have sb := nextIface?_sound hb
  have hdir : a.2 = b.2 := by
    have heq : (!a.2) = (!b.2) := sa.2.2.1.symm.trans sb.2.2.1
    simpa using congrArg Bool.not heq
  have hn : (layerEnds (selected outer inner a.2)).Nodup := by
    cases hd : a.2 with
    | false => simpa [selected, hd] using houter
    | true => simpa [selected, hd] using hinner
  have hnode : a.1 = b.1 :=
    layerNeighbor_injective hn sa.2.2.2
      (by simpa only [← hdir] using sb.2.2.2)
  exact Prod.ext hnode hdir

theorem concrete_nextIface_closed {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) :
    ∀ state ∈ ruleStates rule, ∀ successor,
      nextIface? (oldLayer net left right)
        (ruleLayer rule net.nextId) state = some successor →
      successor ∈ ruleStates rule := by
  intro state _ successor hstep
  have hs := nextIface?_sound hstep
  rcases hs.2.1 with ⟨side, slot, hnode⟩
  have hallowed : Node.iface side slot ∈ ruleIfaces rule :=
    concrete_iface_closed hwf hrule hactive hleftkind hrightkind
      state.1 state.2 side slot (hnode ▸ hs.2.2.2)
  have := mem_ruleStates (direction := successor.2) hallowed
  have hpair : successor = (.iface side slot, successor.2) := by
    rcases successor with ⟨node, dir⟩
    exact congrArg (fun n : Node => (n, dir)) hnode
  rw [hpair]
  exact this

theorem concrete_iface_in_both {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    {node : Node} (hnode : node ∈ ruleIfaces rule) :
    node ∈ layerEnds (oldLayer net left right) ∧
      node ∈ layerEnds (ruleLayer rule net.nextId) := by
  rcases ruleIfaces_mem_cases hnode with
    ⟨slot, hslot, rfl⟩ | ⟨slot, hslot, rfl⟩
  · exact matched_left_aux hwf hrule hleftkind hslot
  · exact matched_right_aux hwf hrule hactive hrightkind hslot

theorem concrete_selected_total {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    {node : Node} (hnode : node ∈ ruleIfaces rule)
    (direction : Bool) :
    ∃ target,
      layerNeighbor
        (selected (oldLayer net left right)
          (ruleLayer rule net.nextId) direction) node =
        some target := by
  have hb := concrete_iface_in_both hwf hrule hactive
    hleftkind hrightkind hnode
  cases direction with
  | false =>
      simpa [selected] using
        layerNeighbor_total (oldLayer_nodup hwf left right) hb.1
  | true =>
      simpa [selected] using
        layerNeighbor_total (ruleLayer_nodup hrule net.nextId) hb.2

theorem nextIface?_no_pred_of_real_partner {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    {side slot : Nat} {direction : Bool} {end_ : End}
    (hreal : layerNeighbor (selected outer inner (!direction))
      (.iface side slot) = some (.real end_)) :
    ∀ state,
      nextIface? outer inner state ≠
        some (.iface side slot, direction) := by
  intro state hstep
  have hs := nextIface?_sound hstep
  have hdir : state.2 = !direction := by
    have heq : direction = !state.2 := hs.2.2.1
    have hnot := congrArg Bool.not heq
    simpa using hnot.symm
  have hn : (layerEnds (selected outer inner (!direction))).Nodup := by
    cases hd : direction with
    | false => simpa [selected, hd] using hinner
    | true => simpa [selected, hd] using houter
  have hforward : layerNeighbor
      (selected outer inner (!direction)) state.1 =
      some (.iface side slot) := by
    simpa only [hdir] using hs.2.2.2
  have hback := layerNeighbor_symmetric hn hforward
  rw [hreal] at hback
  rcases hs.1 with ⟨sourceSide, sourceSlot, hsource⟩
  rw [hsource] at hback
  cases hback

theorem concrete_chain_walk {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    {n : Nat} {state : Node × Bool}
    (hchain : Chain
      (nextIface? (oldLayer net left right)
        (ruleLayer rule net.nextId)) n state) :
    state ∈ ruleStates rule →
    ∃ end_, Walk (oldLayer net left right)
      (ruleLayer rule net.nextId) (n + 1) state.1 state.2 end_ := by
  induction hchain with
  | done hnone =>
      rename_i current
      intro hstate
      have hnode := ruleStates_node_mem hstate
      rcases concrete_selected_total hwf hrule hactive
          hleftkind hrightkind hnode current.2 with
        ⟨target, hnext⟩
      cases target with
      | real end_ =>
          exact ⟨end_, Walk.stop hnext⟩
      | iface side slot =>
          rcases ruleIfaces_mem_cases hnode with
            ⟨sourceSlot, _, hsource⟩ | ⟨sourceSlot, _, hsource⟩ <;>
            rw [hsource] at hnext <;>
            simp [nextIface?, hsource, hnext] at hnone
  | next hstep htail ih =>
      rename_i steps current successor
      intro hstate
      have hsuccessor : _ :=
        concrete_nextIface_closed hwf hrule hactive
          hleftkind hrightkind _ hstate _ hstep
      rcases ih hsuccessor with ⟨end_, hwalk⟩
      have hs := nextIface?_sound hstep
      rcases hs.2.1 with ⟨side, slot, htarget⟩
      have hforward : layerNeighbor
          (selected (oldLayer net left right)
            (ruleLayer rule net.nextId) current.2) current.1 =
          some (.iface side slot) := by
        simpa only [htarget] using hs.2.2.2
      rw [htarget, hs.2.2.1] at hwalk
      exact ⟨end_, Walk.hop hforward hwalk⟩

/-- Every exposed interface boundary reaches another real port. A closed
interface loop cannot be entered from such a boundary. -/
theorem concrete_exposed_follow_terminates {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    {side slot : Nat}
    (hstart : Node.iface side slot ∈ ruleIfaces rule)
    (direction : Bool) {source : End}
    (hreal : layerNeighbor
      (selected (oldLayer net left right)
        (ruleLayer rule net.nextId) (!direction))
      (.iface side slot) = some (.real source)) :
    ∃ target,
      follow (oldLayer net left right) (ruleLayer rule net.nextId)
        (2 * (rule.left.arity + rule.right.arity) + 2)
        (.iface side slot) direction = some target := by
  let outer := oldLayer net left right
  let inner := ruleLayer rule net.nextId
  let states := ruleStates rule
  let start : Node × Bool := (.iface side slot, direction)
  have houter : (layerEnds outer).Nodup := oldLayer_nodup hwf left right
  have hinner : (layerEnds inner).Nodup := ruleLayer_nodup hrule net.nextId
  have hstartMem : start ∈ states := mem_ruleStates hstart
  have hnoPred : ∀ state ∈ states,
      nextIface? outer inner state ≠ some start := by
    intro state _
    exact nextIface?_no_pred_of_real_partner houter hinner hreal state
  rcases Chain.exists_bounded (nextIface? outer inner)
      (nextIface?_injective houter hinner) states start
      (concrete_nextIface_closed hwf hrule hactive
        hleftkind hrightkind) hstartMem hnoPred with
    ⟨n, hbound, hchain⟩
  rcases concrete_chain_walk hwf hrule hactive
      hleftkind hrightkind hchain hstartMem with ⟨target, hwalk⟩
  have hlength : n + 1 ≤
      2 * (rule.left.arity + rule.right.arity) + 2 := by
    dsimp [states] at hbound
    rw [ruleStates_length] at hbound
    omega
  exact ⟨target, follow_complete _ _ hwalk _ hlength⟩

inductive ReverseChain {α : Type} (step : α → Option α) :
    Nat → α → α → Prop where
  | zero {state} : ReverseChain step 0 state state
  | snoc {n start middle terminal} :
      ReverseChain step n start middle →
      step middle = some terminal →
      ReverseChain step (n + 1) start terminal

theorem ReverseChain.prepend {α : Type} {step : α → Option α}
    {n : Nat} {successor terminal : α}
    (hchain : ReverseChain step n successor terminal)
    {start : α} (hstep : step start = some successor) :
    ReverseChain step (n + 1) start terminal := by
  induction hchain with
  | zero => exact ReverseChain.snoc ReverseChain.zero hstep
  | snoc hprefix hlast ih =>
      exact ReverseChain.snoc (ih hstep) hlast

theorem Chain.toReverse {α : Type} {step : α → Option α}
    {n : Nat} {start : α} (hchain : Chain step n start) :
    ∃ terminal, ReverseChain step n start terminal ∧
      step terminal = none := by
  induction hchain with
  | done hnone => exact ⟨_, ReverseChain.zero, hnone⟩
  | next hstep _ ih =>
      rcases ih with ⟨terminal, hreverse, hnone⟩
      exact ⟨terminal, hreverse.prepend hstep, hnone⟩

theorem ReverseChain.start_unique {α : Type} {step : α → Option α}
    (hinjective : ∀ a b target,
      step a = some target → step b = some target → a = b)
    {n m : Nat} {first second terminal : α}
    (hfirst : ReverseChain step n first terminal)
    (hsecond : ReverseChain step m second terminal)
    (hnoFirst : ∀ state, step state ≠ some first)
    (hnoSecond : ∀ state, step state ≠ some second) :
    first = second := by
  induction hfirst generalizing m second with
  | zero =>
      cases hsecond with
      | zero => rfl
      | snoc _ hlast => exact False.elim (hnoFirst _ hlast)
  | snoc hprefix hlast ih =>
      cases hsecond with
      | zero => exact False.elim (hnoSecond _ hlast)
      | snoc hprefix' hlast' =>
          have heq := hinjective _ _ _ hlast hlast'
          cases heq
          exact ih hprefix' hnoFirst hnoSecond

end TriagePaths
