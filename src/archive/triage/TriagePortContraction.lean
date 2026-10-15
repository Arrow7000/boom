import TriageReplacementContraction
import TriageAllocation

/-! Express replacement in one common namespace of concrete ports. -/

namespace TriagePortContraction
open TriageRuleModel (Rule)
open TriageConcrete TriageBoundary TriagePreservation TriageReduction TriageResidual
open TriageAllocation TriageLocalSemantics TriageSpliceContraction TriageReplacementContraction
open TriageContraction

def Link (wires : List Wire) (a b : End) : Prop := (a, b) ∈ wires ∨ (b, a) ∈ wires

def mapped {α β : Type} (f : α → β) (wires : List (α × α)) : List (β × β) :=
  wires.map fun (a, b) => (f a, f b)

def port (fresh left right : Nat) : TriageRuleModel.End → End
  | .agent index slot => .agent (fresh + index) slot
  | .iface side slot => .agent (if side = 0 then left else right) slot

def wiring (rule : Rule) (fresh left right : Nat) : List Wire := mapped (port fresh left right) rule.wires

def Removed (left right : Nat) (end_ : End) : Prop := belongs left right end_ = true

theorem link_neighbor {wires : List Wire} (hn : (wireEnds wires).Nodup) (a b : End) :
    Link wires a b ↔ neighborIn wires a = some b := by
  constructor
  · intro h
    exact h.elim (neighborIn_of_mem hn) (neighborIn_of_mem_right hn)
  · exact neighborIn_sound

theorem layer_link {layer : Layer} (hn : (layerEnds layer).Nodup) (a b : Node) :
    layerNeighbor layer a = some b ↔ (a, b) ∈ layer ∨ (b, a) ∈ layer := by
  constructor
  · exact layerNeighbor_sound
  · intro h
    exact h.elim (layerNeighbor_of_mem hn) (layerNeighbor_of_mem_right hn)

theorem mapped_link {α β : Type} (f : α → β) (wires : List (α × α)) (a b : β) :
    ((a, b) ∈ mapped f wires ∨ (b, a) ∈ mapped f wires) ↔
      Image f (fun x y => (x, y) ∈ wires ∨ (y, x) ∈ wires) a b := by
  constructor
  · rintro (hab | hba)
    · rcases List.mem_map.mp hab with ⟨⟨x, y⟩, hm, he⟩
      have heq := Prod.mk.inj he
      exact ⟨x, y, heq.1.symm, heq.2.symm, Or.inl hm⟩
    · rcases List.mem_map.mp hba with ⟨⟨x, y⟩, hm, he⟩
      have heq := Prod.mk.inj he
      exact ⟨y, x, heq.2.symm, heq.1.symm, Or.inr hm⟩
  · rintro ⟨x, y, rfl, rfl, hm | hm⟩
    · exact Or.inl (List.mem_map.mpr ⟨(x, y), hm, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨(y, x), hm, rfl⟩)

theorem image_or {α β : Type} (f : α → β) (first second : α → α → Prop) (a b : β) :
    Image f (fun x y => first x y ∨ second x y) a b ↔
      Image f first a b ∨ Image f second a b := by
  constructor
  · rintro ⟨x, y, hx, hy, he | he⟩
    · exact Or.inl ⟨x, y, hx, hy, he⟩
    · exact Or.inr ⟨x, y, hx, hy, he⟩
  · rintro (⟨x, y, hx, hy, he⟩ | ⟨x, y, hx, hy, he⟩)
    · exact ⟨x, y, hx, hy, Or.inl he⟩
    · exact ⟨x, y, hx, hy, Or.inr he⟩

theorem rule_port_fromOld {rule : Rule} (hr : rule.wellFormed = true)
    {fresh left right : Nat} (hl : left < fresh) (hright : right < fresh) (hne : left ≠ right)
    {end_ : TriageRuleModel.End} (hm : end_ ∈ rule.used) :
    Node.fromOld left right (port fresh left right end_) = Node.fromRule fresh end_ := by
  cases end_ with
  | agent index slot =>
      have h1 : fresh + index ≠ left := by omega
      have h2 : fresh + index ≠ right := by omega
      simp [port, Node.fromOld, Node.fromRule, h1, h2]
  | iface side slot =>
      have hn : Node.iface side slot ∈ layerEnds (ruleLayer rule fresh) := by
        rw [ruleLayer_ends]
        exact List.mem_map.mpr ⟨.iface side slot, hm, rfl⟩
      have ha := ruleIfaces_mem_cases (ruleLayer_iface_mem_ruleIfaces hr fresh side slot hn)
      rcases ha with ⟨_, _, he⟩ | ⟨_, _, he⟩
      · have hs := (Node.iface.inj he).1
        subst side
        simp [port, Node.fromOld, Node.fromRule]
      · have hs := (Node.iface.inj he).1
        subst side
        simp [port, Node.fromOld, Node.fromRule, Ne.symm hne]

theorem mapped_wiring {rule : Rule} (hr : rule.wellFormed = true)
    {fresh left right : Nat} (hl : left < fresh) (hright : right < fresh) (hne : left ≠ right) :
    mapped (Node.fromOld left right) (wiring rule fresh left right) = ruleLayer rule fresh := by
  simp only [mapped, wiring, List.map_map, ruleLayer]
  apply List.map_congr_left
  intro wire hw
  rcases wire with ⟨a, b⟩
  have ha : a ∈ rule.used := List.mem_flatMap.mpr ⟨(a, b), hw, by simp⟩
  have hb : b ∈ rule.used := List.mem_flatMap.mpr ⟨(a, b), hw, by simp⟩
  simp only [Function.comp_apply, rule_port_fromOld hr hl hright hne ha,
    rule_port_fromOld hr hl hright hne hb]

theorem hidden_fromOld (left right : Nat) :
    (fun end_ => Hidden (Node.fromOld left right end_)) = Removed left right := by
  funext end_
  apply propext
  cases end_ with
  | free name => simp [Hidden, Node.fromOld, Removed, belongs]
  | agent id slot =>
      by_cases hl : id = left <;> by_cases hr : id = right <;>
        simp_all [Hidden, Node.fromOld, Removed, belongs]

theorem joined_image {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices) :
    Joined (outerLayer net left right) (ruleLayer rule net.nextId) =
      Image (Node.fromOld left right) (fun a b => Link net.wires a b ∨ Link (wiring rule net.nextId left right) a b) := by
  have hwf := valid_wellFormed hv
  rcases Net.redexChoice_sound hwf hc with ⟨hr, ha, hl, hright⟩
  have hrwf := exported_rule_wellFormed hr
  have hlb := active_id_bound hv hl
  have hrb := active_id_bound hv hright
  have hne := active_ids_ne hwf ha
  funext a b
  apply propext
  simp only [Joined, layer_link (outerLayer_nodup hwf left right),
    layer_link (ruleLayer_nodup hrwf net.nextId)]
  rw [← mapped_wiring hrwf hlb hrb hne]
  rw [show outerLayer net left right = mapped (Node.fromOld left right) net.wires from rfl,
    mapped_link, mapped_link, ← image_or]
  rfl

theorem replace_used_outside {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices)
    {end_ : End} (hm : end_ ∈ (net.replace rule left right).used) : belongs left right end_ = false := by
  rcases Net.redexChoice_sound (valid_wellFormed hv) hc with ⟨hr, ha, hl, hright⟩
  have hlb := active_id_bound hv hl
  have hrb := active_id_bound hv hright
  rcases (Net.replace_used_iff hv (exported_rule_wellFormed hr) ha hl hright end_).mp hm with
    ⟨_, hout⟩ | hnew
  · exact hout
  · cases end_ with
    | free name => rfl
    | agent id slot =>
        have hge := ruleLayer_real_fresh hnew
        have h1 : id ≠ left := by omega
        have h2 : id ≠ right := by omega
        simp [belongs, h1, h2]

/-- Replacement as contraction in the common concrete-port namespace.
This equation can be composed across different active pairs. -/
theorem replace_iff_port_contract {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices) (a b : End) :
    (net.replace rule left right).neighbor a = some b ↔
      Contract (fun x y => Link net.wires x y ∨ Link (wiring rule net.nextId left right) x y)
        (Removed left right) a b := by
  have hused : ∀ x y, (net.replace rule left right).neighbor x = some y →
      belongs left right x = false ∧ belongs left right y = false := by
    intro x y hn
    rcases neighborIn_sound hn with hw | hw
    · exact ⟨replace_used_outside hv hc (left_mem_wireEnds hw), replace_used_outside hv hc (right_mem_wireEnds hw)⟩
    · exact ⟨replace_used_outside hv hc (right_mem_wireEnds hw), replace_used_outside hv hc (left_mem_wireEnds hw)⟩
  by_cases ha : belongs left right a = false
  · by_cases hb : belongs left right b = false
    · rw [replace_iff_contract hv hc, joined_image hv hc]
      rw [← fromOld_real_of_not_belongs left right a ha, ← fromOld_real_of_not_belongs left right b hb,
        contract_image _ (Node.fromOld_injective left right), hidden_fromOld]
    · constructor
      · intro hn; exact False.elim (hb (hused a b hn).2)
      · intro h; exact False.elim (h.2.2.1 (by cases hval : belongs left right b <;> simp_all [Removed]))
  · constructor
    · intro hn; exact False.elim (ha (hused a b hn).1)
    · intro h; exact False.elim (h.2.1 (by cases hval : belongs left right a <;> simp_all [Removed]))

end TriagePortContraction
