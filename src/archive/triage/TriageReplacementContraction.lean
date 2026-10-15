import TriageSpliceContraction
import TriageLocalSemantics

/-! The whole executable replacement, including retained surrounding wires,
is contraction of the old and new wiring through the removed agents' ports. -/

namespace TriageReplacementContraction
open TriageRuleModel (Rule)
open TriageConcrete TriageBoundary TriagePreservation TriageReduction
open TriagePaths TriageSplicePaths TriageSplice TriageLocalSemantics TriageContraction
open TriageSpliceContraction

def outerLayer (net : Net) (left right : Nat) : Layer :=
  net.wires.map fun (a, b) => (Node.fromOld left right a, Node.fromOld left right b)

theorem outerLayer_nodup {net : Net} (h : net.wellFormed = true) (left right : Nat) :
    (layerEnds (outerLayer net left right)).Nodup := by
  rw [outerLayer, layerEnds, layerEnds_map]
  exact (net.wellFormed_nodup h).map (Node.fromOld_injective left right)

theorem outerLayer_real {net : Net} {left right : Nat} {end_ : End} :
    Node.real end_ ∈ layerEnds (outerLayer net left right) ↔
      end_ ∈ net.used ∧ belongs left right end_ = false := by
  rw [outerLayer, layerEnds, layerEnds_map, List.mem_map]
  constructor
  · rintro ⟨source, hsource, heq⟩
    rcases fromOld_real_eq heq with ⟨rfl, hout⟩
    exact ⟨hsource, hout⟩
  · rintro ⟨hused, hout⟩
    exact ⟨end_, hused, fromOld_real_of_not_belongs left right end_ hout⟩

theorem outer_rule_disjoint {net : Net} (hvalid : net.valid = true)
    (rule : Rule) (left right : Nat) :
    ∀ end_, Node.real end_ ∈ layerEnds (outerLayer net left right) →
      Node.real end_ ∈ layerEnds (ruleLayer rule net.nextId) → False := by
  intro end_ hold hnew
  have hu := (outerLayer_real.mp hold).1
  cases end_ with
  | free name => exact ruleLayer_no_free hnew
  | agent id slot =>
      have hlt := net_used_agent_old hvalid hu
      have hge := ruleLayer_real_fresh hnew
      omega

theorem layerNeighbor_mono {first second : Layer}
    (hn : (layerEnds second).Nodup) (hsub : first ⊆ second)
    {a b : Node} (he : layerNeighbor first a = some b) : layerNeighbor second a = some b := by
  rcases layerNeighbor_sound he with hab | hba
  · exact layerNeighbor_of_mem hn (hsub hab)
  · exact layerNeighbor_of_mem_right hn (hsub hba)

theorem oldLayer_subset_outer (net : Net) (left right : Nat) :
    oldLayer net left right ⊆ outerLayer net left right := by
  intro wire hw
  rcases List.mem_map.mp hw with ⟨old, hm, he⟩
  exact List.mem_map.mpr ⟨old, List.filter_sublist.subset (List.filter_sublist.subset hm), he⟩

theorem Walk.enlarge_outer {outer next inner : Layer}
    (he : ∀ a b, layerNeighbor outer a = some b → layerNeighbor next a = some b)
    {n : Nat} {node : Node} {direction : Bool} {target : End}
    (h : Walk outer inner n node direction target) : Walk next inner n node direction target := by
  have hsel : ∀ dir a b, layerNeighbor (selected outer inner dir) a = some b →
      layerNeighbor (selected next inner dir) a = some b := by
    intro dir a b h
    cases dir with
    | false => exact he a b h
    | true => exact h
  induction h with
  | stop h => exact .stop (hsel _ _ _ h)
  | hop h _ ih => exact .hop (hsel _ _ _ h) ih

theorem Route.enlarge_outer {outer next inner : Layer}
    (he : ∀ a b, layerNeighbor outer a = some b → layerNeighbor next a = some b)
    {a b : End} (h : Route outer inner a b) : Route next inner a b := by
  rcases h with ⟨side, slot, direction, n, hs, hw⟩
  refine ⟨side, slot, direction, n, ?_, Walk.enlarge_outer he hw⟩
  cases direction with
  | false => exact hs
  | true => exact he _ _ hs

theorem replace_semantic {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices)
    {a b : End} (hn : (net.replace rule left right).neighbor a = some b) :
    Semantic (outerLayer net left right) (ruleLayer rule net.nextId) a b := by
  have hwf := valid_wellFormed hv
  have ho := outerLayer_nodup hwf left right
  have hr := exported_rule_wellFormed (Net.redexChoice_sound hwf hc).1
  have hi := ruleLayer_nodup hr net.nextId
  have hedge : ∀ a b, (a, b) ∈ (net.replace rule left right).wires →
      Semantic (outerLayer net left right) (ruleLayer rule net.nextId) a b := by
    intro a b hw
    rw [replace_wires] at hw
    rcases List.mem_append.mp hw with hdir | hthrough
    · rcases List.mem_append.mp hdir with hold | hnew
      · have ha := (untouched_endpoint (left_mem_wireEnds hold)).2
        have hb := (untouched_endpoint (right_mem_wireEnds hold)).2
        have hm : (Node.fromOld left right a, Node.fromOld left right b) ∈ outerLayer net left right := List.mem_map.mpr ⟨(a, b), (List.mem_filter.mp hold).1, rfl⟩
        have hm' : (Node.real a, Node.real b) ∈ outerLayer net left right := by
          simpa only [fromOld_real_of_not_belongs left right a ha,
            fromOld_real_of_not_belongs left right b hb] using hm
        exact Or.inl (Or.inl (layerNeighbor_of_mem ho hm'))
      · exact Or.inl (Or.inr (layerNeighbor_of_mem hi (direct_mem_iff.mp hnew)))
    · have hs := (spliceStarts_matching (oldLayer_nodup hwf left right) hi
        (old_rule_real_disjoint hv rule left right) _).2 _ hthrough
      exact Or.inr (Route.enlarge_outer
        (fun _ _ h => layerNeighbor_mono ho (oldLayer_subset_outer net left right) h) hs)
  rcases neighborIn_sound hn with hab | hba
  · exact hedge a b hab
  · exact semantic_symm ho hi (hedge b a hba)

/-- A whole-net rule replacement is exactly graph contraction at its
interface, including wires between removed ports and closed components. -/
theorem replace_iff_contract {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices) (a b : End) :
    (net.replace rule left right).neighbor a = some b ↔
      Contract (Joined (outerLayer net left right) (ruleLayer rule net.nextId)) Hidden (.real a) (.real b) := by
  have hwf := valid_wellFormed hv
  rcases Net.redexChoice_sound hwf hc with ⟨hrule, ha, hl, hr⟩
  have hrwf := exported_rule_wellFormed hrule
  have ho := outerLayer_nodup hwf left right
  have hi := ruleLayer_nodup hrwf net.nextId
  have hd := outer_rule_disjoint hv rule left right
  have hnv := Net.redexChoice_preserves_valid hv hc
  have hn := Net.wellFormed_nodup (valid_wellFormed hnv)
  constructor
  · intro he
    refine ⟨?_, by simp [Hidden], by simp [Hidden], semantic_path ho hi (replace_semantic hv hc he)⟩
    intro heq
    have : a = b := Node.real.inj heq
    subst b
    exact neighborIn_irreflexive hn he
  · rintro ⟨hne, _, _, hp⟩
    have hused : Node.real a ∈ layerEnds (outerLayer net left right) ∨
        Node.real a ∈ layerEnds (ruleLayer rule net.nextId) := by
      cases hp with
      | nil => exact False.elim (hne rfl)
      | single he | cons he _ _ =>
          rcases he with he | he
          · exact Or.inl (layerNeighbor_source_mem he)
          · exact Or.inr (layerNeighbor_source_mem he)
    have hcovered : a ∈ (net.replace rule left right).used := by
      rw [Net.replace_used_iff hv hrwf ha hl hr]
      exact hused.imp outerLayer_real.mp id
    rcases neighborIn_total hn hcovered with ⟨target, htarget⟩
    have heq := semantic_component ho hi hd (replace_semantic hv hc htarget) hp
    rcases heq with heq | heq
    · exact False.elim (hne (congrArg Node.real heq.symm))
    · simpa [heq] using htarget

end TriageReplacementContraction
