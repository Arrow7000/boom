import TriageContraction

/-! Complete alternating splices implement contraction of interface vertices. -/

namespace TriageSpliceContraction
open TriageConcrete TriageBoundary TriagePaths TriageSplicePaths TriageSplice
open TriageContraction

def Joined (outer inner : Layer) (a b : Node) : Prop :=
  layerNeighbor outer a = some b ∨ layerNeighbor inner a = some b

def Hidden : Node → Prop
  | .iface _ _ => True
  | .real _ => False

theorem joined_symm {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    {a b : Node} (h : Joined outer inner a b) : Joined outer inner b a :=
  h.elim (fun h => Or.inl (layerNeighbor_symmetric ho h))
    (fun h => Or.inr (layerNeighbor_symmetric hi h))

theorem selected_joined {outer inner : Layer} {direction : Bool} {a b : Node}
    (h : layerNeighbor (selected outer inner direction) a = some b) : Joined outer inner a b := by
  cases direction with
  | false => exact Or.inl h
  | true => exact Or.inr h

theorem layerNeighbor_source_mem {layer : Layer} {a b : Node}
    (h : layerNeighbor layer a = some b) : a ∈ layerEnds layer := by
  rcases layerNeighbor_sound h with hab | hba
  · exact left_mem_layerEnds hab
  · exact right_mem_layerEnds hba

theorem real_partner_unique {outer inner : Layer}
    (hd : ∀ end_, Node.real end_ ∈ layerEnds outer → Node.real end_ ∈ layerEnds inner → False)
    {source : End} {a b : Node}
    (ha : Joined outer inner (.real source) a) (hb : Joined outer inner (.real source) b) : a = b := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Option.some.inj (ha.symm.trans hb)
  · exact False.elim (hd source (layerNeighbor_source_mem ha) (layerNeighbor_source_mem hb))
  · exact False.elim (hd source (layerNeighbor_source_mem hb) (layerNeighbor_source_mem ha))
  · exact Option.some.inj (ha.symm.trans hb)

theorem joined_two_partners {outer inner : Layer} {direction : Bool} {node previous next target : Node}
    (hp : layerNeighbor (selected outer inner (!direction)) node = some previous)
    (hn : layerNeighbor (selected outer inner direction) node = some next)
    (ht : Joined outer inner node target) : target = previous ∨ target = next := by
  cases direction <;> simp only [Bool.not_false, Bool.not_true, selected, if_true] at hp hn
  all_goals
    rcases ht with ht | ht
    all_goals first
      | exact Or.inl (Option.some.inj (ht.symm.trans hp))
      | exact Or.inr (Option.some.inj (ht.symm.trans hn))

theorem Walk.trace_head {outer inner : Layer} {n : Nat} {node : Node} {direction : Bool} {target : End}
    (h : Walk outer inner n node direction target) :
    node ∈ (trace outer inner n node direction).map Prod.fst := by
  cases h <;> simp [trace, *]

theorem Walk.trace_hidden {outer inner : Layer} {n : Nat} {node : Node} {direction : Bool} {target : End}
    (h : Walk outer inner n node direction target) (hn : Hidden node) :
    ∀ point ∈ (trace outer inner n node direction).map Prod.fst, Hidden point := by
  induction h with
  | stop hnext => simpa [trace, hnext] using hn
  | hop hnext _ ih =>
      intro point hp
      simp only [trace, hnext, List.map_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hn
      · exact ih trivial point hp

/-- The two edges incident at each internal interface are exactly the
backward and forward edges of the alternating walk. Its terminal real port
has only the backward edge. -/
theorem Walk.segment_closed {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    (hd : ∀ end_, Node.real end_ ∈ layerEnds outer → Node.real end_ ∈ layerEnds inner → False)
    {n : Nat} {node previous : Node} {direction : Bool} {target : End}
    (h : Walk outer inner n node direction target)
    (hp : layerNeighbor (selected outer inner (!direction)) node = some previous) :
    ∀ point ∈ (trace outer inner n node direction).map Prod.fst ++ [.real target],
      ∀ next, Joined outer inner point next →
        next = previous ∨ next ∈ (trace outer inner n node direction).map Prod.fst ++ [.real target] := by
  induction h generalizing previous with
  | @stop node direction target hn =>
      intro point hpoint next he
      simp only [trace, hn, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hpoint ⊢
      rcases hpoint with rfl | rfl
      · rcases joined_two_partners hp hn he with hprev | hnext
        · exact Or.inl hprev
        · exact Or.inr (Or.inr hnext)
      · have ht := joined_symm ho hi (selected_joined hn)
        exact Or.inr (Or.inl (real_partner_unique hd he ht))
  | @hop n node direction side slot target hn hrest ih =>
      have hback := layerNeighbor_symmetric (selected_nodup ho hi direction) hn
      have hback' : layerNeighbor (selected outer inner (!(!direction))) (.iface side slot) = some node := by
        simpa using hback
      intro point hpoint next he
      simp only [trace, hn, List.map_cons, List.cons_append, List.mem_cons] at hpoint ⊢
      rcases hpoint with rfl | hpoint
      · rcases joined_two_partners hp hn he with hprev | hnext
        · exact Or.inl hprev
        · right; right
          rw [hnext]
          exact List.mem_append_left _ (Walk.trace_head hrest)
      · rcases ih hback' point hpoint next he with hprev | hnext
        · exact Or.inr (Or.inl hprev)
        · exact Or.inr (Or.inr hnext)

theorem Path.closed {edge : Node → Node → Prop} {hidden inside : Node → Prop}
    (hc : ∀ a, inside a → ∀ b, edge a b → inside b)
    {a b : Node} (hp : Path edge hidden a b) (ha : inside a) : inside b := by
  induction hp with
  | nil => exact ha
  | single he => exact hc _ ha _ he
  | cons he _ _ ih => exact ih (hc _ ha _ he)

def Semantic (outer inner : Layer) (source target : End) : Prop :=
  Joined outer inner (.real source) (.real target) ∨ Route outer inner source target

theorem semantic_symm {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    {a b : End} (h : Semantic outer inner a b) : Semantic outer inner b a :=
  h.elim (fun h => Or.inl (joined_symm ho hi h)) (fun h => Or.inr (Route.symmetric ho hi h))

/-- A component containing a real endpoint has at most two real endpoints.
The finite alternating path supplies a closed set containing its component. -/
theorem semantic_component {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    (hd : ∀ end_, Node.real end_ ∈ layerEnds outer → Node.real end_ ∈ layerEnds inner → False)
    {a b c : End} (hs : Semantic outer inner a b)
    (hp : Path (Joined outer inner) Hidden (.real a) (.real c)) : c = a ∨ c = b := by
  rcases hs with hdirect | hroute
  · let inside := fun node : Node => node = .real a ∨ node = .real b
    have hclosed : ∀ node, inside node → ∀ next, Joined outer inner node next → inside next := by
      intro node hnode next he
      rcases hnode with rfl | rfl
      · exact Or.inr (real_partner_unique hd he hdirect)
      · exact Or.inl (real_partner_unique hd he (joined_symm ho hi hdirect))
    have hc := Path.closed hclosed hp (Or.inl rfl)
    simpa only [inside, Node.real.injEq] using hc
  · rcases hroute with ⟨side, slot, direction, n, hsource, hwalk⟩
    let nodes := Node.real a :: (trace outer inner n (.iface side slot) direction).map Prod.fst ++ [.real b]
    have hclosed : ∀ node, node ∈ nodes → ∀ next, Joined outer inner node next → next ∈ nodes := by
      intro node hnode next he
      rcases List.mem_cons.mp hnode with rfl | hnode
      · have hedge := joined_symm ho hi (selected_joined hsource)
        have heq := real_partner_unique hd he hedge
        rw [heq]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (Walk.trace_head hwalk))
      · rcases Walk.segment_closed ho hi hd hwalk hsource node hnode next he with hprev | hnext
        · exact List.mem_cons.mpr (Or.inl hprev)
        · exact List.mem_cons_of_mem _ hnext
    have hc := Path.closed hclosed hp (List.mem_cons_self ..)
    simp only [nodes, List.mem_cons, List.mem_append, List.not_mem_nil, or_false, Node.real.injEq, or_assoc] at hc
    rcases hc with heq | hc | heq
    · exact Or.inl heq
    · have hn := Walk.trace_hidden hwalk trivial (.real c) hc
      exact False.elim hn
    · exact Or.inr heq

theorem Walk.path {outer inner : Layer} {n : Nat} {node : Node} {direction : Bool} {target : End}
    (h : Walk outer inner n node direction target) :
    Path (Joined outer inner) Hidden node (.real target) := by
  induction h with
  | stop he => exact .single (selected_joined he)
  | hop he _ ih => exact .cons (selected_joined he) trivial ih

theorem semantic_path {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    {a b : End} (h : Semantic outer inner a b) :
    Path (Joined outer inner) Hidden (.real a) (.real b) := by
  rcases h with hdirect | ⟨side, slot, direction, n, hsource, hwalk⟩
  · exact .single hdirect
  · exact .cons (joined_symm ho hi (selected_joined hsource)) trivial (Walk.path hwalk)

theorem composed_semantic {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    (hd : ∀ end_, Node.real end_ ∈ layerEnds outer → Node.real end_ ∈ layerEnds inner → False)
    (fuel : Nat) {a b : End}
    (hn : neighborIn (direct outer ++ direct inner ++ spliceStarts outer inner fuel) a = some b) :
    Semantic outer inner a b := by
  have hedge : ∀ a b, (a, b) ∈ direct outer ++ direct inner ++ spliceStarts outer inner fuel →
      Semantic outer inner a b := by
    intro a b hw
    rcases List.mem_append.mp hw with hdir | hsplice
    · left
      rcases List.mem_append.mp hdir with hout | hin
      · exact Or.inl (layerNeighbor_of_mem ho (direct_mem_iff.mp hout))
      · exact Or.inr (layerNeighbor_of_mem hi (direct_mem_iff.mp hin))
    · exact Or.inr ((spliceStarts_matching ho hi hd fuel).2 _ hsplice)
  rcases neighborIn_sound hn with hab | hba
  · exact hedge a b hab
  · exact semantic_symm ho hi (hedge b a hba)

/-- With the already proved endpoint coverage, the executable splice is
exactly contraction of the shared interface. -/
theorem composed_iff_contract {outer inner : Layer}
    (ho : (layerEnds outer).Nodup) (hi : (layerEnds inner).Nodup)
    (hd : ∀ end_, Node.real end_ ∈ layerEnds outer → Node.real end_ ∈ layerEnds inner → False)
    (fuel : Nat) (hc : ∀ end_, end_ ∈ wireEnds (spliceStarts outer inner fuel) ↔
      end_ ∈ exposedEnds outer inner) (a b : End) :
    neighborIn (direct outer ++ direct inner ++ spliceStarts outer inner fuel) a = some b ↔
      Contract (Joined outer inner) Hidden (.real a) (.real b) := by
  have hmatch := composed_matching ho hi hd fuel
  constructor
  · intro hn
    refine ⟨?_, by simp [Hidden], by simp [Hidden], semantic_path ho hi (composed_semantic ho hi hd fuel hn)⟩
    intro heq
    have hab : a = b := Node.real.inj heq
    subst b
    exact neighborIn_irreflexive hmatch hn
  · rintro ⟨hne, _, _, hp⟩
    have hused : Node.real a ∈ layerEnds outer ∨ Node.real a ∈ layerEnds inner := by
      have firstEdge : ∃ next, Joined outer inner (.real a) next := by
        cases hp with
        | nil => exact False.elim (hne rfl)
        | single he => exact ⟨_, he⟩
        | cons he _ _ => exact ⟨_, he⟩
      rcases firstEdge with ⟨_, he | he⟩
      · exact Or.inl (layerNeighbor_source_mem he)
      · exact Or.inr (layerNeighbor_source_mem he)
    have hcovered := (composed_coverage fuel hc a).mpr hused
    rcases neighborIn_total hmatch hcovered with ⟨target, htarget⟩
    have heq := semantic_component ho hi hd (composed_semantic ho hi hd fuel htarget) hp
    rcases heq with heq | heq
    · exact False.elim (hne (congrArg Node.real heq.symm))
    · simpa [heq] using htarget

end TriageSpliceContraction
