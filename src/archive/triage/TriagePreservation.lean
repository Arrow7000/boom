import TriageSplice

/-!
Whole-net preservation for the executable replacement operation.
The old boundary is partitioned from the retained wires, and the boundary
splice is combined with the direct replacement wires.
-/

namespace TriagePreservation
open TriageConcrete TriageBoundary TriagePaths TriageSplicePaths TriageSplice

theorem fromOld_real_eq {left right : Nat} {source end_ : End}
    (h : Node.fromOld left right source = .real end_) :
    source = end_ ∧ belongs left right source = false := by
  cases source <;>
    simp only [Node.fromOld] at h <;>
    (try split_ifs at h) <;> simp_all [belongs]

theorem fromOld_real_of_not_belongs (left right : Nat) (end_ : End)
    (h : belongs left right end_ = false) :
    Node.fromOld left right end_ = .real end_ := by
  cases end_ with
  | free name => rfl
  | agent id slot =>
      have hids : id ≠ left ∧ id ≠ right := by simpa [belongs] using h
      simp [Node.fromOld, hids.1, hids.2]

theorem oldLayer_real_touched {net : Net} {left right : Nat} {end_ : End}
    (hmem : Node.real end_ ∈ layerEnds (oldLayer net left right)) :
    end_ ∈ wireEnds (touched net left right) ∧
      belongs left right end_ = false := by
  rw [oldLayer_ends] at hmem
  rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
  rcases fromOld_real_eq heq with ⟨rfl, hbelongs⟩
  exact ⟨((List.filter_sublist).flatMap _).subset hsource, hbelongs⟩

theorem untouched_endpoint {net : Net} {left right : Nat} {end_ : End}
    (hmem : end_ ∈ wireEnds (untouched net left right)) :
    end_ ∈ net.used ∧ belongs left right end_ = false := by
  have hused := (untouched_ends_sublist net left right).subset hmem
  rcases List.mem_flatMap.mp hmem with ⟨⟨a, b⟩, hedge, hport⟩
  have hpair : belongs left right a = false ∧ belongs left right b = false := by
    simpa using (List.mem_filter.mp hedge).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hport
  rcases hport with rfl | rfl
  · exact ⟨hused, hpair.1⟩
  · exact ⟨hused, hpair.2⟩

theorem oldLayer_direct_nil (net : Net) (left right : Nat) :
    direct (oldLayer net left right) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro edge hmem
  rcases edge with ⟨a, b⟩
  have hedge := direct_mem_iff.mp hmem
  rcases List.mem_map.mp hedge with ⟨⟨x, y⟩, hold, heq⟩
  have hends : Node.fromOld left right x = .real a ∧
      Node.fromOld left right y = .real b := Prod.mk.inj heq
  have hx := (fromOld_real_eq hends.1).2
  have hy := (fromOld_real_eq hends.2).2
  have htouched := (List.mem_filter.mp (List.mem_filter.mp hold).1).2
  simp [hx, hy] at htouched

theorem old_endpoint_partition (net : Net) (left right : Nat) (end_ : End) :
    end_ ∈ wireEnds (untouched net left right) ∨
      Node.real end_ ∈ layerEnds (oldLayer net left right) ↔
    end_ ∈ net.used ∧ belongs left right end_ = false := by
  constructor
  · rintro (hretained | hboundary)
    · exact untouched_endpoint hretained
    · have hused := oldLayer_real_used hboundary
      exact ⟨hused, (oldLayer_real_touched hboundary).2⟩
  · rintro ⟨hused, hbelongs⟩
    rcases List.mem_flatMap.mp hused with ⟨⟨a, b⟩, hedge, hport⟩
    by_cases htouched : (belongs left right a || belongs left right b) = true
    · right
      have hnotActive : sameWire (a, b) (.agent left 0, .agent right 0) = false := by
        by_contra h
        have hsame : sameWire (a, b) (.agent left 0, .agent right 0) = true := by
          cases hh : sameWire (a, b) (.agent left 0, .agent right 0) <;> simp_all
        rcases sameWire_port_is_principal hsame hport with hleft | hright
        · simp [hleft, belongs] at hbelongs
        · simp [hright, belongs] at hbelongs
      rw [oldLayer_ends]
      apply List.mem_map.mpr
      refine ⟨end_, ?_, fromOld_real_of_not_belongs left right end_ hbelongs⟩
      apply List.mem_flatMap.mpr
      refine ⟨(a, b), ?_, hport⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_filter.mpr ⟨hedge, htouched⟩, by simp [hnotActive]⟩
    · left
      exact List.mem_flatMap.mpr
        ⟨(a, b), List.mem_filter.mpr ⟨hedge, by simpa using htouched⟩, hport⟩

theorem wireEnds_cons (edge : Wire) (rest : List Wire) :
    wireEnds (edge :: rest) = edge.1 :: edge.2 :: wireEnds rest := rfl

theorem filtered_endpoints_disjoint (wires : List Wire)
    (hn : (wireEnds wires).Nodup) (predicate : Wire → Bool) :
    (wireEnds (wires.filter predicate)).Disjoint
      (wireEnds (wires.filter fun edge => !predicate edge)) := by
  induction wires with
  | nil => simp [wireEnds]
  | cons edge rest ih =>
      rcases edge with ⟨a, b⟩
      change (a :: b :: wireEnds rest).Nodup at hn
      have hna := List.nodup_cons.mp hn
      have hnb := List.nodup_cons.mp hna.2
      have hrest := ih hnb.2
      have hleft : (wireEnds (rest.filter predicate)).Sublist (wireEnds rest) :=
        List.Sublist.flatMap List.filter_sublist _
      have hright : (wireEnds (rest.filter fun edge => !predicate edge)).Sublist
          (wireEnds rest) := List.Sublist.flatMap List.filter_sublist _
      rw [List.disjoint_left] at hrest ⊢
      intro end_ hold hnew
      cases hp : predicate (a, b) <;>
        simp [hp, wireEnds_cons] at hold hnew
      · rcases hnew with rfl | rfl | htail
        · exact hna.1 (List.mem_cons_of_mem _ (hleft.subset hold))
        · exact hnb.1 (hleft.subset hold)
        · exact hrest hold htail
      · rcases hold with rfl | rfl | htail
        · exact hna.1 (List.mem_cons_of_mem _ (hright.subset hnew))
        · exact hnb.1 (hright.subset hnew)
        · exact hrest htail hnew

theorem untouched_old_real_disjoint {net : Net}
    (hwf : net.wellFormed = true) (left right : Nat) {end_ : End}
    (hretained : end_ ∈ wireEnds (untouched net left right))
    (hboundary : Node.real end_ ∈ layerEnds (oldLayer net left right)) : False := by
  have htouch := (oldLayer_real_touched hboundary).1
  have hd := filtered_endpoints_disjoint net.wires (net.wellFormed_nodup hwf)
    (fun (a, b) => belongs left right a || belongs left right b)
  exact (List.disjoint_left.mp hd) htouch hretained

theorem untouched_rule_real_disjoint {net : Net}
    (hvalid : net.valid = true) (rule : TriageRuleModel.Rule)
    (left right : Nat) {end_ : End}
    (hretained : end_ ∈ wireEnds (untouched net left right))
    (hboundary : Node.real end_ ∈ layerEnds (ruleLayer rule net.nextId)) : False := by
  have hused := (untouched_endpoint hretained).1
  cases end_ with
  | free name => exact ruleLayer_no_free hboundary
  | agent id slot =>
      have hlt := net_used_agent_old hvalid hused
      have hge := ruleLayer_real_fresh hboundary
      omega

theorem valid_wellFormed {net : Net} (h : net.valid = true) :
    net.wellFormed = true := by
  have hv : net.wellFormed = true ∧ net.freshIds = true := by
    simpa [Net.valid] using h
  exact hv.1

theorem replacement_boundary_coverage {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) (end_ : End) :
    end_ ∈ wireEnds (direct (ruleLayer rule net.nextId) ++
      spliceStarts (oldLayer net left right) (ruleLayer rule net.nextId)
        (2 * (rule.left.arity + rule.right.arity) + 2)) ↔
    Node.real end_ ∈ layerEnds (oldLayer net left right) ∨
      Node.real end_ ∈ layerEnds (ruleLayer rule net.nextId) := by
  have hc := (concrete_splice_matching_and_coverage hvalid hrule hactive
    hleftkind hrightkind).2
  have h := composed_coverage _ hc end_
  simpa only [oldLayer_direct_nil, List.nil_append] using h

theorem Net.replace_used_nodup {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) :
    (net.replace rule left right).used.Nodup := by
  have hwf := valid_wellFormed hvalid
  have houter := oldLayer_nodup hwf left right
  have hinner := ruleLayer_nodup hrule net.nextId
  have hreal := old_rule_real_disjoint hvalid rule left right
  have hboundary : (wireEnds (direct (ruleLayer rule net.nextId) ++
      spliceStarts (oldLayer net left right) (ruleLayer rule net.nextId)
        (2 * (rule.left.arity + rule.right.arity) + 2))).Nodup := by
    simpa only [oldLayer_direct_nil, List.nil_append] using
      composed_matching houter hinner hreal
        (2 * (rule.left.arity + rule.right.arity) + 2)
  have hdisjoint : (wireEnds (untouched net left right)).Disjoint
      (wireEnds (direct (ruleLayer rule net.nextId) ++
        spliceStarts (oldLayer net left right) (ruleLayer rule net.nextId)
          (2 * (rule.left.arity + rule.right.arity) + 2))) := by
    rw [List.disjoint_left]
    intro end_ hold hnew
    rcases (replacement_boundary_coverage hvalid hrule hactive
      hleftkind hrightkind end_).mp hnew with hboundary | hboundary
    · exact untouched_old_real_disjoint hwf left right hold hboundary
    · exact untouched_rule_real_disjoint hvalid rule left right hold hboundary
  change (wireEnds (net.replace rule left right).wires).Nodup
  rw [replace_wires, List.append_assoc]
  simpa only [wireEnds, List.flatMap_append] using
    List.nodup_append'.2
      ⟨untouched_ends_nodup hwf left right, hboundary, hdisjoint⟩

theorem Net.replace_used_iff {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) (end_ : End) :
    end_ ∈ (net.replace rule left right).used ↔
      (end_ ∈ net.used ∧ belongs left right end_ = false) ∨
      Node.real end_ ∈ layerEnds (ruleLayer rule net.nextId) := by
  change end_ ∈ wireEnds (net.replace rule left right).wires ↔ _
  rw [replace_wires, List.append_assoc]
  have happend : end_ ∈ wireEnds (untouched net left right ++
      (direct (ruleLayer rule net.nextId) ++
        spliceStarts (oldLayer net left right) (ruleLayer rule net.nextId)
          (2 * (rule.left.arity + rule.right.arity) + 2))) ↔
      end_ ∈ wireEnds (untouched net left right) ∨
      end_ ∈ wireEnds (direct (ruleLayer rule net.nextId) ++
        spliceStarts (oldLayer net left right) (ruleLayer rule net.nextId)
          (2 * (rule.left.arity + rule.right.arity) + 2)) := by
    simp only [wireEnds, List.flatMap_append, List.mem_append]
  rw [happend, replacement_boundary_coverage hvalid hrule hactive
    hleftkind hrightkind]
  have hp := old_endpoint_partition net left right end_
  tauto

def ports (agents : List (Nat × TriageRuleModel.Kind)) : List End :=
  agents.flatMap fun (id, kind) =>
    (List.range (kind.arity + 1)).map (End.agent id)

theorem ports_agent_iff (agents : List (Nat × TriageRuleModel.Kind))
    (id slot : Nat) :
    End.agent id slot ∈ ports agents ↔
      ∃ kind, (id, kind) ∈ agents ∧ slot ≤ kind.arity := by
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨⟨otherId, kind⟩, hentry, hport⟩
    rcases List.mem_map.mp hport with ⟨port, hbound, heq⟩
    have heqs : otherId = id ∧ port = slot := End.agent.inj heq
    rcases heqs with ⟨hid, hslot⟩
    subst otherId
    subst port
    refine ⟨kind, hentry, ?_⟩
    have hlt : slot < kind.arity + 1 := List.mem_range.mp hbound
    omega
  · rintro ⟨kind, hentry, hbound⟩
    have hslot : slot < kind.arity + 1 := by omega
    exact List.mem_flatMap.mpr ⟨(id, kind), hentry,
      List.mem_map.mpr ⟨slot, List.mem_range.mpr hslot, rfl⟩⟩

theorem ports_no_free (agents : List (Nat × TriageRuleModel.Kind)) (name : Nat) :
    End.free name ∉ ports agents := by
  simp [ports, List.mem_flatMap]

theorem rule_expected_agent_iff (rule : TriageRuleModel.Rule) (index slot : Nat) :
    TriageRuleModel.End.agent index slot ∈ rule.expected ↔
      ∃ kind, (kind, index) ∈ rule.agents.zipIdx ∧ slot ≤ kind.arity := by
  simp only [TriageRuleModel.Rule.expected, List.mem_append]
  have hleft : TriageRuleModel.End.agent index slot ∉
      (List.range rule.left.arity).map
        (fun port => TriageRuleModel.End.iface 0 (port + 1)) := by simp
  have hright : TriageRuleModel.End.agent index slot ∉
      (List.range rule.right.arity).map
        (fun port => TriageRuleModel.End.iface 1 (port + 1)) := by simp
  simp only [hleft, hright, false_or]
  constructor
  · intro hmem
    rcases List.mem_flatMap.mp hmem with ⟨⟨kind, otherIndex⟩, hentry, hport⟩
    rcases List.mem_map.mp hport with ⟨port, hbound, heq⟩
    have heqs : otherIndex = index ∧ port = slot := TriageRuleModel.End.agent.inj heq
    rcases heqs with ⟨hindex, hslot⟩
    subst otherIndex
    subst port
    have hlt : slot < kind.arity + 1 := List.mem_range.mp hbound
    exact ⟨kind, hentry, by omega⟩
  · rintro ⟨kind, hentry, hbound⟩
    have hslot : slot < kind.arity + 1 := by omega
    exact List.mem_flatMap.mpr ⟨(kind, index), hentry,
      List.mem_map.mpr ⟨slot, List.mem_range.mpr hslot, rfl⟩⟩

theorem ruleLayer_real_agent_iff {rule : TriageRuleModel.Rule}
    (hrule : rule.wellFormed = true) (fresh id slot : Nat) :
    Node.real (.agent id slot) ∈ layerEnds (ruleLayer rule fresh) ↔
      ∃ index, id = fresh + index ∧
        TriageRuleModel.End.agent index slot ∈ rule.expected := by
  constructor
  · intro hmem
    rw [ruleLayer_ends] at hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, heq⟩
    cases source with
    | iface side port => simp [Node.fromRule] at heq
    | agent index port =>
        have heqs : fresh + index = id ∧ port = slot := by
          simpa [Node.fromRule] using heq
        rcases heqs with ⟨hid, rfl⟩
        exact ⟨index, hid.symm,
          ((TriageRuleModel.Rule.wellFormed_iff rule).mp hrule).2.1 _ hsource⟩
  · rintro ⟨index, rfl, hsource⟩
    exact ruleLayer_covers hrule fresh hsource

theorem retained_ports_iff (agents : List (Nat × TriageRuleModel.Kind))
    (left right : Nat) (end_ : End) :
    end_ ∈ ports (agents.filter fun entry =>
      entry.1 != left && entry.1 != right) ↔
      end_ ∈ ports agents ∧ belongs left right end_ = false := by
  cases end_ with
  | free name => simp [ports_no_free]
  | agent id slot =>
      simp only [ports_agent_iff, List.mem_filter]
      simp [belongs, and_assoc]
      aesop

theorem created_ports_iff {rule : TriageRuleModel.Rule}
    (hrule : rule.wellFormed = true) (fresh : Nat) (end_ : End) :
    end_ ∈ ports (rule.agents.zipIdx.map
      (fun (kind, index) => (fresh + index, kind))) ↔
      Node.real end_ ∈ layerEnds (ruleLayer rule fresh) := by
  cases end_ with
  | free name =>
      constructor
      · exact fun h => False.elim (ports_no_free _ name h)
      · exact fun h => False.elim (ruleLayer_no_free h)
  | agent id slot =>
      rw [ports_agent_iff, ruleLayer_real_agent_iff hrule]
      simp only [rule_expected_agent_iff, List.mem_map]
      constructor
      · rintro ⟨kind, ⟨⟨otherKind, index⟩, hentry, heq⟩, hbound⟩
        have heqs : fresh + index = id ∧ otherKind = kind := Prod.mk.inj heq
        rcases heqs with ⟨hid, rfl⟩
        exact ⟨index, hid.symm, otherKind, hentry, hbound⟩
      · rintro ⟨index, hid, kind, hentry, hbound⟩
        exact ⟨kind, ⟨(kind, index), hentry, by simp [hid]⟩, hbound⟩

theorem ports_append (first second : List (Nat × TriageRuleModel.Kind)) :
    ports (first ++ second) = ports first ++ ports second := by
  simp only [ports, List.flatMap_append]

theorem Net.expected_eq_ports (net : Net) :
    net.expected = ports net.agents ++ [.free 0] := rfl

theorem Net.replace_expected_iff (net : Net)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    (left right : Nat) (end_ : End) :
    end_ ∈ (net.replace rule left right).expected ↔
      (end_ ∈ net.expected ∧ belongs left right end_ = false) ∨
      Node.real end_ ∈ layerEnds (ruleLayer rule net.nextId) := by
  have hfree : end_ ∈ ([End.free 0] : List End) →
      belongs left right end_ = false := by
    intro hmem
    have heq := List.mem_singleton.mp hmem
    subst end_
    rfl
  simp only [Net.expected_eq_ports, Net.replace_agents, ports_append,
    List.mem_append, retained_ports_iff, created_ports_iff hrule]
  tauto

/-- Replacing any applicable active pair preserves every live port exactly
once, uses no illegal ports, and keeps all live agent IDs distinct. -/
theorem Net.replace_wellFormed {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) :
    (net.replace rule left right).wellFormed = true := by
  have hv : net.wellFormed = true ∧ net.freshIds = true := by
    simpa [Net.valid] using hvalid
  have hwf := (Net.wellFormed_iff net).mp hv.1
  have hports : ∀ end_, end_ ∈ (net.replace rule left right).used ↔
      end_ ∈ (net.replace rule left right).expected := by
    intro end_
    rw [Net.replace_used_iff hvalid hrule hactive hleftkind hrightkind,
      Net.replace_expected_iff net hrule left right]
    have hold : end_ ∈ net.used ↔ end_ ∈ net.expected :=
      ⟨hwf.2.2.1 end_, hwf.2.2.2 end_⟩
    rw [hold]
  apply (Net.wellFormed_iff _).mpr
  exact ⟨net.replace_ids_nodup hwf.1 hv.2 rule left right,
    Net.replace_used_nodup hvalid hrule hactive hleftkind hrightkind,
    (fun end_ hmem => (hports end_).mp hmem),
    (fun end_ hmem => (hports end_).mpr hmem)⟩

theorem Net.replace_valid {net : Net}
    (hvalid : net.valid = true)
    {rule : TriageRuleModel.Rule} (hrule : rule.wellFormed = true)
    {left right : Nat} (hactive : net.Active left right)
    (hleftkind : net.kind? left = some rule.left)
    (hrightkind : net.kind? right = some rule.right) :
    (net.replace rule left right).valid = true := by
  have hwf := Net.replace_wellFormed hvalid hrule hactive hleftkind hrightkind
  have hfresh : net.freshIds = true := by
    have hv : net.wellFormed = true ∧ net.freshIds = true := by
      simpa [Net.valid] using hvalid
    exact hv.2
  have hnext := net.replace_freshIds hfresh rule left right
  simp [Net.valid, hwf, hnext]

end TriagePreservation
