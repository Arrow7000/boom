import TriageSplicePaths

/-!
Properties of the actual wire list emitted by the alternating splice.
The undirected duplicate filter is verified against the endpoint relation,
then applied to `spliceStarts`.
-/

namespace TriageSplice
open TriageConcrete TriageBoundary TriagePaths TriageSplicePaths

theorem sameWire_endpoints {first second : Wire}
    (h : sameWire first second = true) (end_ : End) :
    end_ ∈ [first.1, first.2] ↔ end_ ∈ [second.1, second.2] := by
  simp only [sameWire, decide_eq_true_eq] at h
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp [ha, hb, or_comm]

theorem relation_wire_collision {R : End → End → Prop}
    (hsymmetric : ∀ a b, R a b → R b a)
    (hunique : ∀ a b c, R a b → R a c → b = c)
    {a b x y : End} (hab : R a b) (hxy : R x y)
    (hshare : a = x ∨ a = y ∨ b = x ∨ b = y) :
    sameWire (a, b) (x, y) = true := by
  rcases hshare with hax | hay | hbx | hby
  · subst x
    have hby := hunique a b y hab hxy
    simp [sameWire, hby]
  · subst y
    have hbx := hunique a b x hab (hsymmetric x a hxy)
    simp [sameWire, hbx]
  · subst x
    have hay := hunique b a y (hsymmetric a b hab) hxy
    simp [sameWire, hay]
  · subst y
    have hax := hunique b a x (hsymmetric a b hab) (hsymmetric x b hxy)
    simp [sameWire, hax]

theorem uniqueWires_matching {R : End → End → Prop}
    (hsymmetric : ∀ a b, R a b → R b a)
    (hunique : ∀ a b c, R a b → R a c → b = c)
    (hirreflexive : ∀ a, ¬R a a)
    (wires : List Wire) (hwires : ∀ wire ∈ wires, R wire.1 wire.2) :
    (wireEnds (uniqueWires wires)).Nodup ∧
    (∀ wire ∈ uniqueWires wires, R wire.1 wire.2) := by
  let insert := fun (acc : List Wire) (wire : Wire) =>
    if acc.any (sameWire wire) then acc else acc ++ [wire]
  have invariant : ∀ (remaining acc : List Wire),
      (wireEnds acc).Nodup →
      (∀ wire ∈ acc, R wire.1 wire.2) →
      (∀ wire ∈ remaining, R wire.1 wire.2) →
      (wireEnds (remaining.foldl insert acc)).Nodup ∧
      (∀ wire ∈ remaining.foldl insert acc, R wire.1 wire.2) := by
    intro remaining
    induction remaining with
    | nil => intro acc hn ha _; exact ⟨hn, ha⟩
    | cons wire rest ih =>
        intro acc hn ha hr
        have hwire := hr wire (List.mem_cons_self ..)
        have hrest : ∀ edge ∈ rest, R edge.1 edge.2 := by
          intro edge hmem
          exact hr edge (List.mem_cons_of_mem _ hmem)
        simp only [List.foldl_cons]
        by_cases hseen : acc.any (sameWire wire) = true
        · simpa [insert, hseen] using ih acc hn ha hrest
        · have hne : wire.1 ≠ wire.2 := by
            intro heq
            exact hirreflexive wire.2 (heq ▸ hwire)
          have hdisjoint : (wireEnds acc).Disjoint [wire.1, wire.2] := by
            rw [List.disjoint_left]
            intro end_ hold hnew
            rcases List.mem_flatMap.mp hold with ⟨edge, hedge, hend⟩
            rcases wire with ⟨a, b⟩
            rcases edge with ⟨x, y⟩
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hend hnew
            have hshare : a = x ∨ a = y ∨ b = x ∨ b = y := by
              rcases hend with hx | hy <;> rcases hnew with h_a | h_b <;>
                simp_all
            have hsame := relation_wire_collision hsymmetric hunique
              hwire (ha (x, y) hedge) hshare
            exact hseen (List.any_eq_true.mpr ⟨(x, y), hedge, hsame⟩)
          have hadded : (wireEnds (acc ++ [wire])).Nodup := by
            have hpair : ([wire.1, wire.2] : List End).Nodup := by
              simpa using hne
            simpa [wireEnds, List.flatMap_append] using
              List.nodup_append'.2 ⟨hn, hpair, hdisjoint⟩
          have haddedR : ∀ edge ∈ acc ++ [wire], R edge.1 edge.2 := by
            intro edge hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · exact ha edge hold
            · simpa using (List.mem_singleton.mp hnew) ▸ hwire
          simpa [insert, hseen] using ih (acc ++ [wire]) hadded haddedR hrest
  exact invariant wires [] (by simp [wireEnds]) (by simp) hwires

theorem uniqueWires_endpoints (wires : List Wire) (end_ : End) :
    end_ ∈ wireEnds (uniqueWires wires) ↔ end_ ∈ wireEnds wires := by
  let insert := fun (acc : List Wire) (wire : Wire) =>
    if acc.any (sameWire wire) then acc else acc ++ [wire]
  have invariant : ∀ remaining acc,
      end_ ∈ wireEnds (remaining.foldl insert acc) ↔
        end_ ∈ wireEnds acc ∨ end_ ∈ wireEnds remaining := by
    intro remaining
    induction remaining with
    | nil => intro acc; simp [wireEnds]
    | cons wire rest ih =>
        intro acc
        simp only [List.foldl_cons]
        by_cases hseen : acc.any (sameWire wire) = true
        · have hcovered : end_ ∈ [wire.1, wire.2] → end_ ∈ wireEnds acc := by
            intro hmem
            rcases List.any_eq_true.mp hseen with ⟨edge, hedge, hsame⟩
            exact List.mem_flatMap.mpr
              ⟨edge, hedge, (sameWire_endpoints hsame end_).mp hmem⟩
          simp only [insert, hseen, if_true]
          rw [ih acc]
          have hcons : end_ ∈ wireEnds (wire :: rest) ↔
              end_ ∈ [wire.1, wire.2] ∨ end_ ∈ wireEnds rest := by
            simp only [wireEnds, List.flatMap_cons, List.mem_append]
          rw [hcons]
          tauto
        · have h := ih (acc ++ [wire])
          simpa [insert, hseen, wireEnds, List.flatMap_append, or_assoc,
            or_left_comm, or_comm] using h
  simpa [uniqueWires, wireEnds] using invariant wires []

theorem starts_mem_iff {layer : Layer} {source : End} {node : Node} :
    (source, node) ∈ starts layer ↔
      (∃ side slot, node = .iface side slot) ∧
      ((Node.real source, node) ∈ layer ∨ (node, Node.real source) ∈ layer) := by
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨⟨a, b⟩, hedge, hentry⟩
    cases a with
    | real left =>
        cases b with
        | real right => simp at hentry
        | iface side slot =>
            simp only [List.mem_singleton, Prod.mk.injEq] at hentry
            rcases hentry with ⟨rfl, rfl⟩
            exact ⟨⟨side, slot, rfl⟩, Or.inl hedge⟩
    | iface side slot =>
        cases b with
        | real right =>
            simp only [List.mem_singleton, Prod.mk.injEq] at hentry
            rcases hentry with ⟨rfl, rfl⟩
            exact ⟨⟨side, slot, rfl⟩, Or.inr hedge⟩
        | iface otherSide otherSlot => simp at hentry
  · rintro ⟨⟨side, slot, rfl⟩, hedge | hedge⟩
    · exact List.mem_flatMap.mpr
        ⟨(_, _), hedge, by simp⟩
    · exact List.mem_flatMap.mpr
        ⟨(_, _), hedge, by simp⟩

theorem starts_sound {layer : Layer}
    (hn : (layerEnds layer).Nodup) {source : End} {node : Node}
    (hmem : (source, node) ∈ starts layer) :
    (∃ side slot, node = .iface side slot) ∧
      layerNeighbor layer node = some (.real source) := by
  rcases starts_mem_iff.mp hmem with ⟨hshape, hedge | hedge⟩
  · exact ⟨hshape, layerNeighbor_of_mem_right hn hedge⟩
  · exact ⟨hshape, layerNeighbor_of_mem hn hedge⟩

theorem starts_complete {layer : Layer} {source : End} {side slot : Nat}
    (h : layerNeighbor layer (.iface side slot) = some (.real source)) :
    (source, Node.iface side slot) ∈ starts layer := by
  exact starts_mem_iff.mpr ⟨⟨side, slot, rfl⟩,
    (layerNeighbor_sound h).symm⟩

def rawSplice (outer inner : Layer) (fuel : Nat) : List Wire :=
  ((starts outer).filterMap fun (start, iface) =>
    (follow outer inner fuel iface true).map fun target => (start, target)) ++
  ((starts inner).filterMap fun (start, iface) =>
    (follow outer inner fuel iface false).map fun target => (start, target))

theorem spliceStarts_eq_unique (outer inner : Layer) (fuel : Nat) :
    spliceStarts outer inner fuel = uniqueWires (rawSplice outer inner fuel) := rfl

theorem rawSplice_routes {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup) (fuel : Nat) :
    ∀ edge ∈ rawSplice outer inner fuel,
      Route outer inner edge.1 edge.2 := by
  intro edge hmem
  rcases List.mem_append.mp hmem with hold | hnew
  · rcases List.mem_filterMap.mp hold with ⟨⟨source, node⟩, hstart, hout⟩
    rcases starts_sound houter hstart with ⟨⟨side, slot, rfl⟩, hsource⟩
    cases hfollow : follow outer inner fuel (.iface side slot) true with
    | none => simp [hfollow] at hout
    | some target =>
        simp [hfollow] at hout
        subst edge
        rcases follow_sound _ _ _ _ _ _ hfollow with ⟨n, _, hwalk⟩
        exact ⟨side, slot, true, n, hsource, hwalk⟩
  · rcases List.mem_filterMap.mp hnew with ⟨⟨source, node⟩, hstart, hout⟩
    rcases starts_sound hinner hstart with ⟨⟨side, slot, rfl⟩, hsource⟩
    cases hfollow : follow outer inner fuel (.iface side slot) false with
    | none => simp [hfollow] at hout
    | some target =>
        simp [hfollow] at hout
        subst edge
        rcases follow_sound _ _ _ _ _ _ hfollow with ⟨n, _, hwalk⟩
        exact ⟨side, slot, false, n, hsource, hwalk⟩

theorem spliceStarts_matching {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False) (fuel : Nat) :
    (wireEnds (spliceStarts outer inner fuel)).Nodup ∧
    (∀ edge ∈ spliceStarts outer inner fuel,
      Route outer inner edge.1 edge.2) := by
  rw [spliceStarts_eq_unique]
  exact uniqueWires_matching (R := Route outer inner)
    (fun _ _ h => Route.symmetric houter hinner h)
    (fun _ _ _ hab hac => Route.source_unique houter hinner hdisjoint hab hac)
    (Route.irreflexive houter hinner hdisjoint)
    _ (rawSplice_routes houter hinner fuel)

def exposedEnds (outer inner : Layer) : List End :=
  (starts outer).map Prod.fst ++ (starts inner).map Prod.fst

theorem route_source_exposed {outer inner : Layer} {source target : End}
    (hroute : Route outer inner source target) :
    source ∈ exposedEnds outer inner := by
  rcases hroute with ⟨side, slot, direction, _, hsource, _⟩
  cases direction with
  | false =>
      have hs : (source, Node.iface side slot) ∈ starts inner :=
        starts_complete (by simpa [selected] using hsource)
      exact List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨_, hs, rfl⟩))
  | true =>
      have hs : (source, Node.iface side slot) ∈ starts outer :=
        starts_complete (by simpa [selected] using hsource)
      exact List.mem_append.mpr
        (Or.inl (List.mem_map.mpr ⟨_, hs, rfl⟩))

theorem spliceStarts_endpoint_exposed {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False) (fuel : Nat)
    {end_ : End} (hmem : end_ ∈ wireEnds (spliceStarts outer inner fuel)) :
    end_ ∈ exposedEnds outer inner := by
  rcases List.mem_flatMap.mp hmem with ⟨edge, hedge, hport⟩
  have hr := (spliceStarts_matching houter hinner hdisjoint fuel).2 edge hedge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with heq | heq
  · rw [heq]
    exact route_source_exposed hr
  · rw [heq]
    exact route_source_exposed (Route.symmetric houter hinner hr)

theorem rawSplice_contains {outer inner : Layer} {fuel : Nat}
    {source target : End} {node : Node} {direction : Bool}
    (hstart : (source, node) ∈ starts (selected outer inner (!direction)))
    (hfollow : follow outer inner fuel node direction = some target) :
    (source, target) ∈ rawSplice outer inner fuel := by
  cases direction with
  | false =>
      apply List.mem_append.mpr
      right
      apply List.mem_filterMap.mpr
      exact ⟨(source, node), by simpa [selected] using hstart,
        by simp [hfollow]⟩
  | true =>
      apply List.mem_append.mpr
      left
      apply List.mem_filterMap.mpr
      exact ⟨(source, node), by simpa [selected] using hstart,
        by simp [hfollow]⟩

theorem concrete_splice_covers_start {net : Net}
    (hwf : net.wellFormed = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right)
    {source : End} {node : Node} (direction : Bool)
    (hstart : (source, node) ∈ starts
      (selected (oldLayer net left right)
        (ruleLayer rule net.nextId) (!direction))) :
    source ∈ wireEnds (spliceStarts (oldLayer net left right)
      (ruleLayer rule net.nextId)
      (2 * (rule.left.arity + rule.right.arity) + 2)) := by
  have houter := oldLayer_nodup hwf left right
  have hinner := ruleLayer_nodup hrule net.nextId
  rcases starts_sound (selected_nodup houter hinner (!direction)) hstart with
    ⟨⟨side, slot, rfl⟩, hsource⟩
  have hallowed : Node.iface side slot ∈ ruleIfaces rule := by
    have hmem := layerNeighbor_target_mem
      (layerNeighbor_symmetric
        (selected_nodup houter hinner (!direction)) hsource)
    cases direction with
    | false =>
        exact ruleLayer_iface_mem_ruleIfaces hrule net.nextId side slot hmem
    | true =>
        exact oldLayer_iface_mem_ruleIfaces hwf rule hactive
          hleftkind hrightkind hmem
  rcases concrete_exposed_follow_terminates hwf hrule hactive
    hleftkind hrightkind hallowed direction hsource with ⟨target, hfollow⟩
  have hraw := rawSplice_contains hstart hfollow
  rw [spliceStarts_eq_unique]
  exact (uniqueWires_endpoints _ source).mpr (left_mem_wireEnds hraw)

/-- The actual splice uses each exposed boundary port exactly once. -/
theorem concrete_splice_matching_and_coverage {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) :
    let outer := oldLayer net left right
    let inner := ruleLayer rule net.nextId
    let fuel := 2 * (rule.left.arity + rule.right.arity) + 2
    (wireEnds (spliceStarts outer inner fuel)).Nodup ∧
    (∀ end_, end_ ∈ wireEnds (spliceStarts outer inner fuel) ↔
      end_ ∈ exposedEnds outer inner) := by
  have hwf : net.wellFormed = true := by
    have h : net.wellFormed = true ∧ net.freshIds = true := by
      simpa [Net.valid] using hvalid
    exact h.1
  have houter := oldLayer_nodup hwf left right
  have hinner := ruleLayer_nodup hrule net.nextId
  have hdisjoint := old_rule_real_disjoint hvalid rule left right
  constructor
  · exact (spliceStarts_matching houter hinner hdisjoint _).1
  · intro end_
    constructor
    · exact spliceStarts_endpoint_exposed houter hinner hdisjoint _
    · intro hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · rcases List.mem_map.mp hold with ⟨⟨source, node⟩, hstart, heq⟩
        change source = end_ at heq
        subst source
        exact concrete_splice_covers_start hwf hrule hactive
          hleftkind hrightkind true hstart
      · rcases List.mem_map.mp hnew with ⟨⟨source, node⟩, hstart, heq⟩
        change source = end_ at heq
        subst source
        exact concrete_splice_covers_start hwf hrule hactive
          hleftkind hrightkind false hstart

theorem direct_mem_iff {layer : Layer} {a b : End} :
    (a, b) ∈ direct layer ↔ (Node.real a, Node.real b) ∈ layer := by
  constructor
  · intro hmem
    rcases List.mem_filterMap.mp hmem with ⟨⟨x, y⟩, hedge, hout⟩
    cases x <;> cases y <;> simp at hout
    rcases hout with ⟨rfl, rfl⟩
    exact hedge
  · intro hedge
    exact List.mem_filterMap.mpr ⟨(_, _), hedge, rfl⟩

theorem direct_endpoint_real_mem {layer : Layer} {end_ : End}
    (hmem : end_ ∈ wireEnds (direct layer)) :
    Node.real end_ ∈ layerEnds layer := by
  exact (direct_ends_sublist layer).subset (List.mem_map.mpr ⟨end_, hmem, rfl⟩)

theorem start_endpoint_real_mem {layer : Layer} {end_ : End}
    (hmem : end_ ∈ (starts layer).map Prod.fst) :
    Node.real end_ ∈ layerEnds layer := by
  rcases List.mem_map.mp hmem with ⟨⟨source, node⟩, hstart, heq⟩
  change source = end_ at heq
  subst source
  rcases starts_mem_iff.mp hstart with ⟨_, hedge | hedge⟩
  · exact left_mem_layerEnds hedge
  · exact right_mem_layerEnds hedge

theorem real_endpoint_partition (layer : Layer) (end_ : End) :
    Node.real end_ ∈ layerEnds layer ↔
      end_ ∈ wireEnds (direct layer) ∨
      end_ ∈ (starts layer).map Prod.fst := by
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨⟨a, b⟩, hedge, hport⟩
    cases a with
    | real left =>
        cases b with
        | real right =>
            have hd := direct_mem_iff.mpr hedge
            have heq : end_ = left ∨ end_ = right := by simpa using hport
            left
            rcases heq with rfl | rfl
            · exact left_mem_wireEnds hd
            · exact right_mem_wireEnds hd
        | iface side slot =>
            have heq : end_ = left := by simpa using hport
            subst end_
            right
            have hs : (left, Node.iface side slot) ∈ starts layer :=
              starts_mem_iff.mpr ⟨⟨side, slot, rfl⟩, Or.inl hedge⟩
            exact List.mem_map.mpr ⟨_, hs, rfl⟩
    | iface side slot =>
        cases b with
        | real right =>
            have heq : end_ = right := by simpa using hport
            subst end_
            right
            have hs : (right, Node.iface side slot) ∈ starts layer :=
              starts_mem_iff.mpr ⟨⟨side, slot, rfl⟩, Or.inr hedge⟩
            exact List.mem_map.mpr ⟨_, hs, rfl⟩
        | iface otherSide otherSlot => simp at hport
  · rintro (hdirect | hstart)
    · exact direct_endpoint_real_mem hdirect
    · exact start_endpoint_real_mem hstart

theorem direct_starts_disjoint {layer : Layer}
    (hn : (layerEnds layer).Nodup) :
    (wireEnds (direct layer)).Disjoint ((starts layer).map Prod.fst) := by
  rw [List.disjoint_left]
  intro end_ hdirect hstart
  rcases List.mem_flatMap.mp hdirect with ⟨⟨a, b⟩, hedge, hport⟩
  have hedge' := direct_mem_iff.mp hedge
  rcases List.mem_map.mp hstart with ⟨⟨source, node⟩, hs, heq⟩
  change source = end_ at heq
  subst source
  rcases starts_sound hn hs with ⟨⟨side, slot, rfl⟩, hneighbor⟩
  have hiface := layerNeighbor_symmetric hn hneighbor
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with heq | heq
  · have hreal := layerNeighbor_of_mem hn hedge'
    rw [← heq, hiface] at hreal
    cases hreal
  · have hreal := layerNeighbor_of_mem_right hn hedge'
    rw [← heq, hiface] at hreal
    cases hreal

theorem directs_disjoint {outer inner : Layer}
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False) :
    (wireEnds (direct outer)).Disjoint (wireEnds (direct inner)) := by
  rw [List.disjoint_left]
  intro end_ hold hnew
  exact hdisjoint end_ (direct_endpoint_real_mem hold) (direct_endpoint_real_mem hnew)

theorem directs_exposed_disjoint {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False) :
    (wireEnds (direct outer ++ direct inner)).Disjoint (exposedEnds outer inner) := by
  rw [List.disjoint_left]
  intro end_ hdirect hstart
  have hdirect' : end_ ∈ wireEnds (direct outer) ∨
      end_ ∈ wireEnds (direct inner) := by
    simpa only [wireEnds, List.flatMap_append, List.mem_append] using hdirect
  rcases hdirect' with hold | hnew <;>
    rcases List.mem_append.mp hstart with hstartOld | hstartNew
  · exact (List.disjoint_left.mp (direct_starts_disjoint houter)) hold hstartOld
  · exact hdisjoint end_ (direct_endpoint_real_mem hold) (start_endpoint_real_mem hstartNew)
  · exact hdisjoint end_ (start_endpoint_real_mem hstartOld) (direct_endpoint_real_mem hnew)
  · exact (List.disjoint_left.mp (direct_starts_disjoint hinner)) hnew hstartNew

theorem composed_matching {outer inner : Layer}
    (houter : (layerEnds outer).Nodup)
    (hinner : (layerEnds inner).Nodup)
    (hdisjoint : ∀ end_, Node.real end_ ∈ layerEnds outer →
      Node.real end_ ∈ layerEnds inner → False) (fuel : Nat) :
    (wireEnds (direct outer ++ direct inner ++
      spliceStarts outer inner fuel)).Nodup := by
  have hdirect : (wireEnds (direct outer ++ direct inner)).Nodup := by
    simpa only [wireEnds, List.flatMap_append] using
      List.nodup_append'.2 ⟨direct_ends_nodup houter,
        direct_ends_nodup hinner, directs_disjoint hdisjoint⟩
  have hthrough := (spliceStarts_matching houter hinner hdisjoint fuel).1
  have hdisj : (wireEnds (direct outer ++ direct inner)).Disjoint
      (wireEnds (spliceStarts outer inner fuel)) := by
    rw [List.disjoint_left]
    intro end_ hdir hsplice
    exact (List.disjoint_left.mp
      (directs_exposed_disjoint houter hinner hdisjoint)) hdir
      (spliceStarts_endpoint_exposed houter hinner hdisjoint fuel hsplice)
  simpa only [wireEnds, List.flatMap_append] using
    List.nodup_append'.2 ⟨hdirect, hthrough, hdisj⟩

theorem composed_coverage {outer inner : Layer} (fuel : Nat)
    (hcoverage : ∀ end_, end_ ∈ wireEnds (spliceStarts outer inner fuel) ↔
      end_ ∈ exposedEnds outer inner) (end_ : End) :
    end_ ∈ wireEnds (direct outer ++ direct inner ++ spliceStarts outer inner fuel) ↔
      Node.real end_ ∈ layerEnds outer ∨ Node.real end_ ∈ layerEnds inner := by
  simp only [wireEnds, List.flatMap_append, List.mem_append]
  change (_ ∨ _) ∨ end_ ∈ wireEnds (spliceStarts outer inner fuel) ↔ _
  rw [hcoverage, real_endpoint_partition, real_endpoint_partition]
  simp only [exposedEnds, List.mem_append]
  tauto

end TriageSplice
