/-
Copyright (c) 2026 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import TriageSplice

/-!
Paths with restricted internal vertices, and contraction of those vertices.
This description of wire splicing is independent of edge-list order, the
traversal algorithm, and allocation. Contraction is associative and commutes
for arbitrary sets of hidden vertices, including closed internal components.
-/

namespace TriageContraction

universe u
variable {α : Type u}

inductive Path (edge : α → α → Prop) (hidden : α → Prop) : α → α → Prop where
  | nil (a : α) : Path edge hidden a a
  | single {a b : α} : edge a b → Path edge hidden a b
  | cons {a b c : α} : edge a b → hidden b → Path edge hidden b c → Path edge hidden a c

theorem Path.mono {edge next : α → α → Prop} {hidden more : α → Prop}
    (he : ∀ a b, edge a b → next a b) (hh : ∀ a, hidden a → more a)
    {a b : α} (h : Path edge hidden a b) : Path next more a b := by
  induction h with
  | nil a => exact .nil a
  | single h => exact .single (he _ _ h)
  | cons h hb _ ih => exact .cons (he _ _ h) (hh _ hb) ih

theorem Path.trans {edge : α → α → Prop} {hidden : α → Prop}
    {a b c : α} (first : Path edge hidden a b) (middle : hidden b)
    (second : Path edge hidden b c) : Path edge hidden a c := by
  induction first with
  | nil => exact second
  | single h => exact .cons h middle second
  | cons h hb _ ih => exact .cons h hb (ih middle second)

theorem Path.symm {edge : α → α → Prop} {hidden : α → Prop}
    (hs : ∀ a b, edge a b → edge b a) {a b : α}
    (h : Path edge hidden a b) : Path edge hidden b a := by
  induction h with
  | nil a => exact .nil a
  | single h => exact .single (hs _ _ h)
  | cons h hb _ ih => exact ih.trans hb (.single (hs _ _ h))

def Contract (edge : α → α → Prop) (hidden : α → Prop) (a b : α) : Prop :=
  a ≠ b ∧ ¬hidden a ∧ ¬hidden b ∧ Path edge hidden a b

theorem Contract.symm {edge : α → α → Prop} {hidden : α → Prop}
    (hs : ∀ a b, edge a b → edge b a) {a b : α}
    (h : Contract edge hidden a b) : Contract edge hidden b a :=
  ⟨Ne.symm h.1, h.2.2.1, h.2.1, h.2.2.2.symm hs⟩

theorem Path.ends {edge : α → α → Prop} {hidden good : α → Prop}
    (he : ∀ a b, edge a b → good a ∧ good b) {a b : α}
    (h : Path edge hidden a b) : a = b ∨ (good a ∧ good b) := by
  induction h with
  | nil => exact Or.inl rfl
  | single h => exact Or.inr (he _ _ h)
  | cons h _ _ ih =>
      have hab := he _ _ h
      rcases ih with rfl | hbc
      · exact Or.inr hab
      · exact Or.inr ⟨hab.1, hbc.2⟩

theorem Path.expand {edge : α → α → Prop} {first second : α → Prop}
    {a b : α} (h : Path (Contract edge first) second a b) :
    Path edge (fun x => first x ∨ second x) a b := by
  induction h with
  | nil a => exact .nil a
  | single h => exact h.2.2.2.mono (fun _ _ h => h) (fun _ h => Or.inl h)
  | cons h hb _ ih =>
      exact (h.2.2.2.mono (fun _ _ h => h) (fun _ h => Or.inl h)).trans (Or.inr hb) ih

theorem Path.to_contract {edge : α → α → Prop} {hidden more : α → Prop}
    {a b : α} (h : Path edge hidden a b) (ha : ¬hidden a) (hb : ¬hidden b) :
    Path (Contract edge hidden) more a b := by
  by_cases heq : a = b
  · subst b; exact .nil a
  · exact .single ⟨heq, ha, hb, h⟩

/-- Compress every maximal first-hidden segment of a mixed path. The
accumulator also removes excursions returning to their starting vertex. -/
theorem Path.compress_prefix {edge : α → α → Prop} {first second : α → Prop}
    {current target : α} (h : Path edge (fun x => first x ∨ second x) current target) :
    ∀ {start : α}, ¬first start → ¬first target →
      Path edge first start current → (start = current ∨ first current) →
      Path (Contract edge first) second start target := by
  induction h with
  | nil current =>
      intro start hs ht hp _
      exact hp.to_contract hs ht
  | @single current target hedge =>
      intro start hs ht hp hc
      have hall : Path edge first start target := by
        rcases hc with rfl | hc
        · exact .single hedge
        · exact hp.trans hc (.single hedge)
      exact hall.to_contract hs ht
  | @cons current next target hedge hnext hrest ih =>
      intro start hs ht hp hc
      have accumulated : Path edge first start next := by
        rcases hc with rfl | hc
        · exact .single hedge
        · exact hp.trans hc (.single hedge)
      by_cases hn : first next
      · exact ih hs ht accumulated (Or.inr hn)
      · have hsecond : second next := hnext.resolve_left hn
        have tail := ih hn ht (.nil next) (Or.inl rfl)
        exact (accumulated.to_contract hs hn).trans hsecond tail

theorem Path.compress {edge : α → α → Prop} {first second : α → Prop}
    {a b : α} (h : Path edge (fun x => first x ∨ second x) a b)
    (ha : ¬first a) (hb : ¬first b) : Path (Contract edge first) second a b :=
  h.compress_prefix ha hb (.nil a) (Or.inl rfl)

/-- Eliminating two sets of internal vertices is the same as eliminating
their union. No disjointness or termination assumption is needed. -/
theorem contract_contract (edge : α → α → Prop) (first second : α → Prop) (a b : α) :
    Contract (Contract edge first) second a b ↔
      Contract edge (fun x => first x ∨ second x) a b := by
  constructor
  · rintro ⟨hne, ha, hb, hp⟩
    have he : ∀ x y, Contract edge first x y → ¬first x ∧ ¬first y :=
      fun _ _ h => ⟨h.2.1, h.2.2.1⟩
    rcases hp.ends he with heq | ⟨haf, hbf⟩
    · exact False.elim (hne heq)
    · exact ⟨hne, by tauto, by tauto, hp.expand⟩
  · rintro ⟨hne, ha, hb, hp⟩
    simp only [not_or] at ha hb
    exact ⟨hne, ha.2, hb.2, hp.compress ha.1 hb.1⟩

theorem contract_commute (edge : α → α → Prop) (first second : α → Prop) (a b : α) :
    Contract (Contract edge first) second a b ↔
      Contract (Contract edge second) first a b := by
  rw [contract_contract, contract_contract]
  have heq : (fun x => first x ∨ second x) = (fun x => second x ∨ first x) := by
    funext x
    exact propext (or_comm ..)
  rw [heq]

theorem Path.map {β : Type u} {edge : α → α → Prop} {next : β → β → Prop}
    {hidden : α → Prop} {more : β → Prop} (f : α → β)
    (he : ∀ a b, edge a b → next (f a) (f b)) (hh : ∀ a, hidden a → more (f a))
    {a b : α} (h : Path edge hidden a b) : Path next more (f a) (f b) := by
  induction h with
  | nil a => exact .nil _
  | single h => exact .single (he _ _ h)
  | cons h hb _ ih => exact .cons (he _ _ h) (hh _ hb) ih

def Image {β : Type u} (f : α → β) (edge : α → α → Prop) (a b : β) : Prop :=
  ∃ x y, a = f x ∧ b = f y ∧ edge x y

theorem Path.pullback_image {β : Type u} (f : α → β) (hf : Function.Injective f)
    {edge : α → α → Prop} {hidden : β → Prop} {a b : β}
    (h : Path (Image f edge) hidden a b) :
    ∀ x y, a = f x → b = f y → Path edge (fun x => hidden (f x)) x y := by
  induction h with
  | nil a =>
      intro x y hx hy
      have heq := hf (hx.symm.trans hy)
      subst y
      exact .nil x
  | single he =>
      intro x y hx hy
      rcases he with ⟨first, second, hfirst, hsecond, hedge⟩
      have hx' := hf (hx.symm.trans hfirst)
      have hy' := hf (hy.symm.trans hsecond)
      subst first
      subst second
      exact .single hedge
  | cons he hn _ ih =>
      intro x y hx hy
      rcases he with ⟨first, second, hfirst, hsecond, hedge⟩
      have hx' := hf (hx.symm.trans hfirst)
      subst first
      exact .cons hedge (by simpa only [hsecond] using hn) (ih second y hsecond hy)

theorem contract_image {β : Type u} (f : α → β) (hf : Function.Injective f)
    (edge : α → α → Prop) (hidden : β → Prop) (a b : α) :
    Contract (Image f edge) hidden (f a) (f b) ↔
      Contract edge (fun x => hidden (f x)) a b := by
  constructor
  · rintro ⟨hne, ha, hb, hp⟩
    exact ⟨fun heq => hne (congrArg f heq), ha, hb, hp.pullback_image f hf a b rfl rfl⟩
  · rintro ⟨hne, ha, hb, hp⟩
    exact ⟨fun heq => hne (hf heq), ha, hb,
      hp.map f (fun x y he => ⟨x, y, rfl, rfl, he⟩) (fun _ h => h)⟩

theorem contract_equiv (rename : α ≃ α) (first second : α → α → Prop)
    (hidden more : α → Prop)
    (he : ∀ a b, second (rename a) (rename b) ↔ first a b)
    (hh : ∀ a, more (rename a) ↔ hidden a) (a b : α) :
    Contract second more (rename a) (rename b) ↔ Contract first hidden a b := by
  have hrel : second = Image rename first := by
    funext x y
    apply propext
    constructor
    · intro h
      exact ⟨rename.symm x, rename.symm y, by simp, by simp,
        (he _ _).mp (by simpa using h)⟩
    · rintro ⟨x, y, rfl, rfl, h⟩
      exact (he x y).mpr h
  rw [hrel, contract_image rename rename.injective]
  have hpred : (fun x => more (rename x)) = hidden := funext fun x => propext (hh x)
  rw [hpred]

theorem Path.disjoint_extra {edge extra : α → α → Prop} {hidden : α → Prop}
    (hx : ∀ a b, extra a b → ¬hidden a ∧ ¬hidden b)
    {a b : α} (h : Path (fun x y => edge x y ∨ extra x y) hidden a b) :
    Path edge hidden a b ∨ extra a b := by
  induction h with
  | nil a => exact Or.inl (.nil a)
  | single he => exact he.elim (fun h => Or.inl (.single h)) Or.inr
  | cons he hn _ ih =>
      rcases he with he | he
      · rcases ih with hpath | hextra
        · exact Or.inl (.cons he hn hpath)
        · exact False.elim ((hx _ _ hextra).1 hn)
      · exact False.elim ((hx _ _ he).2 hn)

/-- Adding edges wholly outside an interface commutes with contracting it. -/
theorem contract_add (edge extra : α → α → Prop) (hidden : α → Prop)
    (hx : ∀ a b, extra a b → ¬hidden a ∧ ¬hidden b)
    (hirr : ∀ a, ¬extra a a) (a b : α) :
    Contract (fun x y => edge x y ∨ extra x y) hidden a b ↔
      Contract edge hidden a b ∨ extra a b := by
  constructor
  · rintro ⟨hne, ha, hb, hp⟩
    rcases hp.disjoint_extra hx with hp | he
    · exact Or.inl ⟨hne, ha, hb, hp⟩
    · exact Or.inr he
  · rintro (⟨hne, ha, hb, hp⟩ | he)
    · exact ⟨hne, ha, hb, hp.mono (fun _ _ h => Or.inl h) (fun _ h => h)⟩
    · have hend := hx a b he
      exact ⟨fun heq => hirr b (heq ▸ he), hend.1, hend.2, .single (Or.inr he)⟩

/-- Independent rule wirings may be added and contracted in either order. -/
theorem replacement_commute (edge first second : α → α → Prop) (hideFirst hideSecond : α → Prop)
    (hf : ∀ a b, first a b → ¬hideSecond a ∧ ¬hideSecond b)
    (hs : ∀ a b, second a b → ¬hideFirst a ∧ ¬hideFirst b)
    (hfirr : ∀ a, ¬first a a) (hsirr : ∀ a, ¬second a a) (a b : α) :
    Contract (fun x y => Contract (fun s t => edge s t ∨ first s t) hideFirst x y ∨ second x y) hideSecond a b ↔
      Contract (fun x y => Contract (fun s t => edge s t ∨ second s t) hideSecond x y ∨ first x y) hideFirst a b := by
  have hleft : (fun x y => Contract (fun s t => edge s t ∨ first s t) hideFirst x y ∨ second x y) =
      Contract (fun s t => (edge s t ∨ first s t) ∨ second s t) hideFirst := by
    funext x y
    exact propext (contract_add _ _ _ hs hsirr x y).symm
  have hright : (fun x y => Contract (fun s t => edge s t ∨ second s t) hideSecond x y ∨ first x y) =
      Contract (fun s t => (edge s t ∨ second s t) ∨ first s t) hideSecond := by
    funext x y
    exact propext (contract_add _ _ _ hf hfirr x y).symm
  rw [hleft, hright, contract_contract, contract_contract]
  have he : (fun s t => (edge s t ∨ first s t) ∨ second s t) =
      (fun s t => (edge s t ∨ second s t) ∨ first s t) := by
    funext s t
    exact propext (by tauto)
  have hh : (fun x => hideFirst x ∨ hideSecond x) = (fun x => hideSecond x ∨ hideFirst x) := by
    funext x
    exact propext (or_comm ..)
  rw [he, hh]

end TriageContraction
