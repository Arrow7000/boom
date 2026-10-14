import TriageRuleModel

/-!
The graph interface of the netties reducer, abstracting away numeric wire
identifiers and animation bookkeeping. A port has at most one partner, and
each connection is symmetric. Finite support and the rewrite operation will
be added when the source-net encoding is introduced.
-/

namespace TriageGraph
open TriageRuleModel

inductive End where
  | agent : Nat → Nat → End
  | free : Nat → End
  deriving Repr, DecidableEq

structure Net where
  kind : Nat → Option Kind
  isFree : Nat → Bool
  partner : End → Option End
  symmetric : ∀ {a b}, partner a = some b → partner b = some a
  irreflexive : ∀ a, partner a ≠ some a

def Net.legal (net : Net) : End → Prop
  | .agent id slot => ∃ kind, net.kind id = some kind ∧ slot ≤ kind.arity
  | .free id => net.isFree id = true

def Net.Active (net : Net) (left right : Nat) : Prop :=
  (∃ kind, net.kind left = some kind) ∧
  (∃ kind, net.kind right = some kind) ∧
  net.partner (.agent left 0) = some (.agent right 0)

theorem Net.Active.symm {net : Net} {left right : Nat}
    (h : net.Active left right) : net.Active right left :=
  ⟨h.2.1, h.1, net.symmetric h.2.2⟩

theorem Net.Active.ne {net : Net} {left right : Nat}
    (h : net.Active left right) : left ≠ right := by
  intro heq
  subst right
  exact net.irreflexive (.agent left 0) h.2.2

/-- The principal port of an agent belongs to at most one active pair. -/
theorem Net.Active.unique_partner {net : Net} {a b c : Nat}
    (hab : net.Active a b) (hac : net.Active a c) : b = c := by
  have h : (some (End.agent b 0) : Option End) = some (.agent c 0) := by
    rw [← hab.2.2, hac.2.2]
  cases Option.some.inj h
  rfl

/-- Distinct active pairs have disjoint agent IDs. -/
theorem Net.Active.disjoint_or_equal {net : Net} {a b c d : Nat}
    (hab : net.Active a b) (hcd : net.Active c d)
    (hshare : a = c ∨ a = d ∨ b = c ∨ b = d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases hshare with hac | had | hbc | hbd
  · left
    subst c
    exact ⟨rfl, Net.Active.unique_partner hab hcd⟩
  · right
    subst d
    exact ⟨rfl, Net.Active.unique_partner hab hcd.symm⟩
  · right
    subst c
    have h := Net.Active.unique_partner hab.symm hcd
    exact ⟨h, rfl⟩
  · left
    subst d
    have h := Net.Active.unique_partner hab.symm hcd.symm
    exact ⟨h, rfl⟩

end TriageGraph
