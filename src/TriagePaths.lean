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

end TriagePaths
