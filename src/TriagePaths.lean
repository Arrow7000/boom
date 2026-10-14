import TriageBoundary

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

end TriagePaths
