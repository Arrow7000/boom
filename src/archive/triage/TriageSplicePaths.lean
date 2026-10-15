import TriagePaths

/-!
Endpoint properties of alternating paths through two matching layers.
These lemmas connect the executable walks to the exposed real ports joined
by a rule splice.
-/

namespace TriageSplicePaths
open TriageConcrete TriageBoundary TriagePaths

theorem nextIface_of_neighbor {outer inner : Layer}
    {side slot nextSide nextSlot : Nat} {direction : Bool}
    (hnext : layerNeighbor (selected outer inner direction)
      (.iface side slot) = some (.iface nextSide nextSlot)) :
    nextIface? outer inner (.iface side slot, direction) =
      some (.iface nextSide nextSlot, !direction) := by
  simp [nextIface?, hnext]

theorem Walk.toReverse {outer inner : Layer}
    {n : Nat} {node : Node} {direction : Bool} {target : End}
    (hwalk : Walk outer inner n node direction target) :
    (∃ side slot, node = .iface side slot) →
    ∃ steps terminal,
      n = steps + 1 ∧
      ReverseChain (nextIface? outer inner) steps
        (node, direction) terminal ∧
      layerNeighbor (selected outer inner terminal.2) terminal.1 =
        some (.real target) := by
  induction hwalk with
  | stop hnext =>
      intro _
      exact ⟨0, _, rfl, ReverseChain.zero, hnext⟩
  | hop hnext hrest ih =>
      rename_i steps current useInner side slot final
      intro hshape
      rcases ih ⟨side, slot, rfl⟩ with
        ⟨count, terminal, hlength, hreverse, hterminal⟩
      rcases hshape with ⟨sourceSide, sourceSlot, rfl⟩
      have hstep := nextIface_of_neighbor hnext
      exact ⟨count + 1, terminal, by omega,
        hreverse.prepend hstep, hterminal⟩

theorem selected_nodup {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup) (direction : Bool) :
    (layerEnds (selected outer inner direction)).Nodup := by
  cases direction with
  | false => simpa [selected] using houter
  | true => simpa [selected] using hinner

theorem terminal_state_unique {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False)
    {first second : Node × Bool} {target : End}
    (hfirst : layerNeighbor (selected outer inner first.2) first.1 =
      some (.real target))
    (hsecond : layerNeighbor (selected outer inner second.2) second.1 =
      some (.real target)) : first = second := by
  rcases first with ⟨firstNode, firstDir⟩
  rcases second with ⟨secondNode, secondDir⟩
  cases firstDir <;> cases secondDir <;>
    simp [selected] at hfirst hsecond
  · exact Prod.ext (layerNeighbor_injective houter hfirst hsecond) rfl
  · exact False.elim (hdisjoint target
      (layerNeighbor_target_mem hfirst) (layerNeighbor_target_mem hsecond))
  · exact False.elim (hdisjoint target
      (layerNeighbor_target_mem hsecond) (layerNeighbor_target_mem hfirst))
  · exact Prod.ext (layerNeighbor_injective hinner hfirst hsecond) rfl

def Route (outer inner : Layer) (source target : End) : Prop :=
  ∃ side slot direction n,
    layerNeighbor (selected outer inner (!direction)) (.iface side slot) =
      some (.real source) ∧
    Walk outer inner n (.iface side slot) direction target

theorem Route.target_injective {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False)
    {first second target : End}
    (hfirst : Route outer inner first target)
    (hsecond : Route outer inner second target) : first = second := by
  rcases hfirst with ⟨side, slot, direction, n, hsource, hwalk⟩
  rcases hsecond with ⟨side', slot', direction', m, hsource', hwalk'⟩
  rcases Walk.toReverse hwalk ⟨side, slot, rfl⟩ with
    ⟨steps, terminal, _, hreverse, hterminal⟩
  rcases Walk.toReverse hwalk' ⟨side', slot', rfl⟩ with
    ⟨steps', terminal', _, hreverse', hterminal'⟩
  have hterminalEq := terminal_state_unique houter hinner hdisjoint
    hterminal hterminal'
  rw [← hterminalEq] at hreverse'
  have hstartEq := ReverseChain.start_unique
    (nextIface?_injective houter hinner) hreverse hreverse'
    (nextIface?_no_pred_of_real_partner houter hinner hsource)
    (nextIface?_no_pred_of_real_partner houter hinner hsource')
  have hnode := congrArg Prod.fst hstartEq
  have hdir := congrArg Prod.snd hstartEq
  change Node.iface side slot = Node.iface side' slot' at hnode
  change direction = direction' at hdir
  rw [← hnode, ← hdir] at hsource'
  exact Node.real.inj (Option.some.inj (hsource.symm.trans hsource'))

def flip (state : Node × Bool) : Node × Bool := (state.1, !state.2)

@[simp] theorem flip_flip (state : Node × Bool) : flip (flip state) = state := by
  cases state
  simp [flip]

theorem nextIface_reverse {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    {state target : Node × Bool}
    (hstep : nextIface? outer inner state = some target) :
    nextIface? outer inner (flip target) = some (flip state) := by
  have hs := nextIface?_sound hstep
  have hback := layerNeighbor_symmetric
    (selected_nodup houter hinner state.2) hs.2.2.2
  have hdir : (!target.2) = state.2 := by
    rw [hs.2.2.1]
    simp
  rcases hs.1 with ⟨side, slot, hsource⟩
  rcases hs.2.1 with ⟨nextSide, nextSlot, htarget⟩
  have hback' : layerNeighbor (selected outer inner (!target.2))
      (.iface nextSide nextSlot) = some (.iface side slot) := by
    simpa only [hdir, hsource, htarget] using hback
  have h := nextIface_of_neighbor hback'
  simpa [flip, hsource, htarget, hs.2.2.1] using h

theorem ReverseChain.reverse_flip {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    {n : Nat} {start terminal : Node × Bool}
    (hchain : ReverseChain (nextIface? outer inner) n start terminal) :
    ReverseChain (nextIface? outer inner) n
      (flip terminal) (flip start) := by
  induction hchain with
  | zero => exact ReverseChain.zero
  | snoc _ hlast ih =>
      exact ih.prepend (nextIface_reverse houter hinner hlast)

theorem ReverseChain.terminal_iface {outer inner : Layer}
    {n : Nat} {start terminal : Node × Bool}
    (hchain : ReverseChain (nextIface? outer inner) n start terminal)
    (hstart : ∃ side slot, start.1 = .iface side slot) :
    ∃ side slot, terminal.1 = .iface side slot := by
  cases hchain with
  | zero => exact hstart
  | snoc _ hlast => exact (nextIface?_sound hlast).2.1

theorem ReverseChain.append_walk {outer inner : Layer}
    {n : Nat} {start terminal : Node × Bool}
    (hchain : ReverseChain (nextIface? outer inner) n start terminal) :
    ∀ {m target}, Walk outer inner m terminal.1 terminal.2 target →
      Walk outer inner (n + m) start.1 start.2 target := by
  induction hchain with
  | zero => intro m target hwalk; simpa using hwalk
  | snoc hprefix hlast ih =>
      rename_i count source middle final
      intro m target hwalk
      have hs := nextIface?_sound hlast
      rcases hs.2.1 with ⟨side, slot, hnode⟩
      have hneighbor : layerNeighbor (selected outer inner middle.2)
          middle.1 = some (.iface side slot) := by
        simpa only [hnode] using hs.2.2.2
      rw [hnode, hs.2.2.1] at hwalk
      have hmid := Walk.hop hneighbor hwalk
      have hfull := ih hmid
      convert hfull using 1; omega

theorem Route.symmetric {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    {source target : End} (hroute : Route outer inner source target) :
    Route outer inner target source := by
  rcases hroute with ⟨side, slot, direction, n, hsource, hwalk⟩
  rcases Walk.toReverse hwalk ⟨side, slot, rfl⟩ with
    ⟨steps, terminal, _, hreverse, hterminal⟩
  rcases ReverseChain.terminal_iface hreverse ⟨side, slot, rfl⟩ with
    ⟨terminalSide, terminalSlot, hnode⟩
  have hflipped := ReverseChain.reverse_flip houter hinner hreverse
  have hstop : Walk outer inner 1
      (flip (.iface side slot, direction)).1
      (flip (.iface side slot, direction)).2 source := Walk.stop hsource
  have hback := ReverseChain.append_walk hflipped hstop
  refine ⟨terminalSide, terminalSlot, !terminal.2, steps + 1, ?_, ?_⟩
  · simpa only [Bool.not_not, hnode] using hterminal
  · simpa only [flip, hnode] using hback

theorem Route.source_unique {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False)
    {source first second : End}
    (hfirst : Route outer inner source first)
    (hsecond : Route outer inner source second) : first = second :=
  Route.target_injective houter hinner hdisjoint
    (Route.symmetric houter hinner hfirst)
    (Route.symmetric houter hinner hsecond)

theorem layerNeighbor_irreflexive {layer : Layer}
    (hn : (layerEnds layer).Nodup) (node : Node) :
    layerNeighbor layer node ≠ some node := by
  intro h
  rcases layerNeighbor_sound h with hedge | hedge <;>
    have hp := (List.nodup_flatMap.mp hn).1 (node, node) hedge <;>
    simp at hp

theorem nextIface_not_flip {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup) (state : Node × Bool) :
    nextIface? outer inner state ≠ some (flip state) := by
  intro hstep
  have hs := nextIface?_sound hstep
  exact layerNeighbor_irreflexive
    (selected_nodup houter hinner state.2) state.1 hs.2.2.2

theorem ReverseChain.first_step {α : Type} {step : α → Option α}
    {n : Nat} {start terminal : α}
    (hchain : ReverseChain step n start terminal) (hn : n ≠ 0) :
    ∃ successor count, n = count + 1 ∧
      step start = some successor ∧
      ReverseChain step count successor terminal := by
  induction hchain with
  | zero => exact False.elim (hn rfl)
  | snoc hprefix hlast ih =>
      rename_i count source middle final
      by_cases hz : count = 0
      · subst count
        cases hprefix
        exact ⟨final, 0, rfl, hlast, ReverseChain.zero⟩
      · rcases ih hz with ⟨successor, remaining, hlength, hfirst, htail⟩
        exact ⟨successor, remaining + 1, by omega,
          hfirst, ReverseChain.snoc htail hlast⟩

theorem ReverseChain.not_flip {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    {n : Nat} {start terminal : Node × Bool}
    (hchain : ReverseChain (nextIface? outer inner) n start terminal) :
    terminal ≠ flip start := by
  induction n using Nat.strong_induction_on generalizing start terminal with
  | h length ih =>
      intro hflip
      cases hchain with
      | zero =>
          have hdir := congrArg Prod.snd hflip
          change start.2 = !start.2 at hdir
          cases hd : start.2 <;> simp [hd] at hdir
      | snoc hprefix hlast =>
          rename_i count middle
          rw [hflip] at hlast
          by_cases hz : count = 0
          · subst count
            cases hprefix
            exact nextIface_not_flip houter hinner start hlast
          · rcases ReverseChain.first_step hprefix hz with
              ⟨successor, remaining, hlength, hfirst, htail⟩
            have hback := nextIface_reverse houter hinner hlast
            rw [flip_flip] at hback
            have hsuccessor : successor = flip middle :=
              Option.some.inj (hfirst.symm.trans hback)
            have htailFlip : middle = flip successor := by
              rw [hsuccessor, flip_flip]
            exact ih remaining (by omega) htail htailFlip

theorem Route.irreflexive {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False)
    (source : End) : ¬Route outer inner source source := by
  intro hroute
  rcases hroute with ⟨side, slot, direction, n, hsource, hwalk⟩
  rcases Walk.toReverse hwalk ⟨side, slot, rfl⟩ with
    ⟨steps, terminal, _, hreverse, hterminal⟩
  have hsame : terminal = flip (.iface side slot, direction) :=
    terminal_state_unique houter hinner hdisjoint hterminal hsource
  exact ReverseChain.not_flip houter hinner hreverse hsame

end TriageSplicePaths
