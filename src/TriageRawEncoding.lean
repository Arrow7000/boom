import TriageEncoding
import TriageResources

/-! A concrete representation of the four raw constructors used by resource
jobs. Unlike source syntax, this domain distinguishes cached Stem/Fork agents
from application agents with the same syntax readback. -/

namespace TriageResources
open TriageRuleModel (Kind)

def Raw.kind : Raw → Kind
  | .leaf => .leaf
  | .stem _ => .stem
  | .fork _ _ => .fork
  | .app _ _ => .app

def Raw.toSyntax : Raw → TriageMachine.Syntax
  | .leaf => .leaf
  | .stem child => TriageMachine.stem child.toSyntax
  | .fork left right => TriageMachine.fork left.toSyntax right.toSyntax
  | .app fn arg => .app fn.toSyntax arg.toSyntax

theorem Raw.arity (raw : Raw) : raw.kind.arity = raw.children.length := by cases raw <;> rfl

theorem Raw.not_control (raw : Raw) : raw.kind ≠ Kind.dup ∧ raw.kind ≠ Kind.erase := by
  cases raw <;> simp [Raw.kind]

end TriageResources

namespace TriageRawEncoding
open TriageRuleModel (Kind Rule)
open TriageConcrete TriageBoundary TriagePreservation TriageReduction TriageResidual
open TriageEncoding TriageResources

inductive Realizes (net : Net) : End → Raw → Prop where
  | leaf {id : Nat} : net.kind? id = some .leaf → Realizes net (.agent id 0) .leaf
  | stem {id : Nat} {root : End} {child : Raw} :
      net.kind? id = some .stem → Linked net (.agent id 1) root → Realizes net root child →
      Realizes net (.agent id 0) (.stem child)
  | fork {id : Nat} {left right : End} {a b : Raw} :
      net.kind? id = some .fork → Linked net (.agent id 1) left → Linked net (.agent id 2) right →
      Realizes net left a → Realizes net right b → Realizes net (.agent id 0) (.fork a b)
  | app {id : Nat} {left right : End} {a b : Raw} :
      net.kind? id = some .app → Linked net (.agent id 1) left → Linked net (.agent id 2) right →
      Realizes net left a → Realizes net right b → Realizes net (.agent id 0) (.app a b)

theorem Realizes.principal {net : Net} {root : End} {raw : Raw} (h : Realizes net root raw) :
    ∃ id, root = .agent id 0 := by cases h <;> exact ⟨_, rfl⟩

theorem Realizes.kind {net : Net} {id : Nat} {raw : Raw} (h : Realizes net (.agent id 0) raw) :
    net.kind? id = some raw.kind := by cases h <;> assumption

theorem Realizes.children {net : Net} {id : Nat} {raw : Raw} (h : Realizes net (.agent id 0) raw) :
    ∀ index child, raw.children[index]? = some child →
      ∃ root, Linked net (.agent id (index + 1)) root ∧ Realizes net root child := by
  cases h with
  | leaf _ => simp [Raw.children]
  | stem _ hl hr =>
      intro index child hget
      cases index with
      | zero => cases (Option.some.inj hget); exact ⟨_, hl, hr⟩
      | succ i => simp [Raw.children] at hget
  | fork _ hl hr hrl hrr | app _ hl hr hrl hrr =>
      intro index child hget
      cases index with
      | zero => cases (Option.some.inj hget); exact ⟨_, hl, hrl⟩
      | succ i =>
          cases i with
          | zero => cases (Option.some.inj hget); exact ⟨_, hr, hrr⟩
          | succ i => simp [Raw.children] at hget

theorem Realizes.of_children {net : Net} {id : Nat} {raw : Raw}
    (hk : net.kind? id = some raw.kind)
    (hc : ∀ index child, raw.children[index]? = some child →
      ∃ root, Linked net (.agent id (index + 1)) root ∧ Realizes net root child) :
    Realizes net (.agent id 0) raw := by
  cases raw with
  | leaf => exact .leaf hk
  | stem child =>
      rcases hc 0 child rfl with ⟨root, hl, hr⟩
      exact .stem hk hl hr
  | fork a b =>
      rcases hc 0 a rfl with ⟨left, hl, hrl⟩
      rcases hc 1 b rfl with ⟨right, hr, hrr⟩
      exact .fork hk hl hr hrl hrr
  | app a b =>
      rcases hc 0 a rfl with ⟨left, hl, hrl⟩
      rcases hc 1 b rfl with ⟨right, hr, hrr⟩
      exact .app hk hl hr hrl hrr

theorem child_outside {net : Net} (hwf : net.wellFormed = true)
    {left right parent index : Nat} {root : End} {raw : Raw}
    (ha : net.Active left right) (hl : Linked net (.agent parent (index + 1)) root)
    (hr : Realizes net root raw) : belongs left right root = false := by
  rcases hr.principal with ⟨id, rfl⟩
  rcases auxiliary_child_not_active hwf ha (by omega : index + 1 ≠ 0) hl with ⟨h1, h2⟩
  simp [belongs, h1, h2]

/-- Entire raw resource payloads are frozen by rewrites outside their root. -/
theorem Realizes.replace {net : Net} (hv : net.valid = true)
    {rule : Rule} {left right : Nat} (hc : (rule, left, right) ∈ net.redexChoices)
    {root : End} {raw : Raw} (h : Realizes net root raw) (hout : belongs left right root = false) :
    Realizes (net.replace rule left right) root raw := by
  have hwf := valid_wellFormed hv
  have ha := (Net.redexChoice_sound hwf hc).2.1
  have hkind : ∀ id kind, net.kind? id = some kind → belongs left right (.agent id 0) = false →
      (net.replace rule left right).kind? id = some kind := by
    intro id kind hk hb
    have hid : id ≠ left ∧ id ≠ right := by simpa [belongs] using hb
    exact Net.replace_retains_kind hv rule hk hid.1 hid.2
  revert hout
  induction h with
  | leaf hk => intro hb; exact .leaf (hkind _ _ hk hb)
  | @stem id root child hk hl hr ih =>
      intro hb
      have hc := child_outside hwf ha (index := 0) hl hr
      exact .stem (hkind _ _ hk hb) (hl.replace rule left right hb hc) (ih hc)
  | @fork id lroot rroot a b hk hl hr hrl hrr ihl ihr =>
      intro hb
      have hcl := child_outside hwf ha (index := 0) hl hrl
      have hcr := child_outside hwf ha (index := 1) hr hrr
      exact .fork (hkind _ _ hk hb) (hl.replace rule left right hb hcl)
        (hr.replace rule left right hb hcr) (ihl hcl) (ihr hcr)
  | @app id lroot rroot a b hk hl hr hrl hrr ihl ihr =>
      intro hb
      have hcl := child_outside hwf ha (index := 0) hl hrl
      have hcr := child_outside hwf ha (index := 1) hr hrr
      exact .app (hkind _ _ hk hb) (hl.replace rule left right hb hcl)
        (hr.replace rule left right hb hcr) (ihl hcl) (ihr hcr)

theorem Realizes.represents {net : Net} {root : End} {raw : Raw} (h : Realizes net root raw) :
    Represents net root raw.toSyntax := by
  induction h with
  | leaf hk => exact .leaf (Net.kind_mem hk)
  | stem hk hl _ ih => exact .stem (Net.kind_mem hk) hl ih
  | fork hk hl hr _ _ ihl ihr => exact .fork (Net.kind_mem hk) hl hr ihl ihr
  | app hk hl hr _ _ ihl ihr => exact .app (Net.kind_mem hk) hl hr ihl ihr

end TriageRawEncoding
