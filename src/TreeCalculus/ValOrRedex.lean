/-
Copyright (c) 2025 Aron Adler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aron Adler
-/

import Mathlib.Tactic.Tauto
import Mathlib.Logic.Relation

/-!
# Value/redex presentation of Tree Calculus

This module develops the `Value` / `ValOrRedex` presentation and its proofs.
It coexists with the syntax-only `Term` presentation in `TreeCalculus.Term`;
both are available for comparison and future equivalence results.

The reduction relations need to be distinguished when relating presentations:
`ReductionStep.rewrite` discards `rest`, whereas canonical application
congruence retains trailing arguments. The confluence theorem below is only
about `ValOrRedex`, not about `Term`.
-/

/-- Static values, that cannot be reduced further, not even their subterms -/
@[grind cases]
inductive Value : Type where
  | leaf : Value
  | stem : Value → Value
  | fork : Value → Value → Value




@[grind cases]



inductive ValOrRedex
  | leaf
  | stem (a : ValOrRedex)
  | fork (a b : ValOrRedex)
  | redex (a b c : ValOrRedex) (rest : List ValOrRedex)
  deriving Repr





@[reducible, simp]
def ValOrRedex.toList (v : ValOrRedex) : List ValOrRedex :=
  match v with
  | .leaf => []
  | .stem a => a :: []
  | .fork a b => a :: b :: []
  | .redex a b c items => a :: b :: c :: items



@[reducible, simp]
def ValOrRedex.ofList (list : List ValOrRedex) : ValOrRedex :=
  match list with
  | [] => .leaf
  | a :: [] => .stem a
  | a :: b :: [] => .fork a b
  | a :: b :: c :: rest => .redex a b c rest







@[reducible, simp]
def ValOrRedex.append (fst snd : ValOrRedex) : ValOrRedex :=
  ofList (toList fst ++ toList snd)


/- Computations only apply to `.items` containing at least 3 items and those 3 items must all be values. A reduction takes a ValOrRedex and returns a Value. It does so by either returning `.value`'s contents. Or if `.items`, reduce all the subterms until they're values, and then if you have < 3 values, return them as a Value. Otherwise if ≥ 3, apply a rewrite rule to the first 3 values. Then append the resulting list of 0-2 values to the front of the rest of the items, and rinse and repeat. -/




mutual

@[reducible]
def ValOrRedex.decEq (a b : ValOrRedex) : Bool :=
  match a, b with
  | .leaf, .leaf => true
  | .stem a, .stem a' => a.decEq a'
  | .fork a b, .fork a' b' =>
    match a.decEq a' with
    | true => b.decEq b'
    | false => false
  | .redex a b c rest, .redex a' b' c' rest' =>
    match a.decEq a' with
    | true =>
      match b.decEq b' with
      | true =>
        match c.decEq c' with
        | true => ValOrRedex.listDecEq rest rest'
        | false => false
      | false => false
    | false => false
  | (redex _ _ _ _), (fork _ _)
  | (redex _ _ _ _), (stem _)
  | (redex _ _ _ _), leaf
  | (fork _ _), (redex _ _ _ _)
  | (fork _ _), (stem _)
  | (fork _ _), leaf
  | (stem _), (redex _ _ _ _)
  | (stem _), (fork _ _)
  | (stem _), leaf
  | leaf, (redex _ _ _ _)
  | leaf, (fork _ _)
  | leaf, (stem _) => false


def ValOrRedex.listDecEq (a b : List ValOrRedex) : Bool :=
  match a, b with
  | [], [] => true
  | head :: rest, head' :: rest' =>
    match head.decEq head' with
    | true => listDecEq rest rest'
    | false => false
  | [], _ :: _
  | _ :: _, [] => false

end


@[grind .]
theorem ValOrRedex.decEq_sound : ValOrRedex.decEq a b = true → a = b := by
  intro prem
  induction a using ValOrRedex.rec (motive_2 := λ list₁ ↦ ∀ {list₂}, ValOrRedex.listDecEq list₁ list₂ = true → list₁ = list₂ ) generalizing b with
  | leaf => cases b <;> tauto
  | stem a ih => cases b <;> tauto
  | fork _ _ => cases b <;> grind
  | redex a' b' c' rest' aih bih cih restih =>
    cases b with
    | leaf => simp at prem
    | stem => simp at prem
    | fork => simp at prem
    | redex a'' b'' c'' rest'' =>
      simp at ⊢
      unfold decEq at prem
      split at prem
      · expose_names
        have := aih heq
        rw [this]
        simp
        split at prem
        · expose_names
          have := bih heq_1
          rw [this]
          simp
          split at prem
          · expose_names
            have := cih heq_2
            rw [this]
            simp
            exact restih prem
          · contradiction
        · contradiction
      · contradiction
  | @nil list₂ prem =>
    cases list₂ with
    | nil => rfl
    | cons head tail =>
      unfold listDecEq at prem
      contradiction
  | @cons head tail head_ih tail_ih list₂ prem =>
    cases list₂ with
    | nil =>
      unfold listDecEq at prem
      contradiction
    | cons head' tail' =>
      simp
      unfold listDecEq at prem
      split at prem
      · grind
      · grind




@[grind =]
theorem ValOrRedex.decEq_complete : a = b → ValOrRedex.decEq a b = true := by
  intro prem
  induction a using ValOrRedex.rec (motive_2 := λ list₁ ↦ ∀ {list₂}, list₁ = list₂ → ValOrRedex.listDecEq list₁ list₂ = true) generalizing b with
  | leaf => cases b <;> tauto
  | stem a ih =>
    cases b
    · simp at prem
    · simp at prem
      have := ih prem
      unfold decEq
      exact this
    · simp at prem
    · simp at prem
  | fork _ _ => cases b <;> grind
  | redex a' b' c' rest' aih bih cih restih =>
    cases b with
    | leaf => simp at prem
    | stem => simp at prem
    | fork => simp at prem
    | redex a'' b'' c'' rest'' => grind
  | @nil list₂ prem =>
    cases list₂ with
    | nil => rfl
    | cons head tail => simp at prem
  | @cons head tail head_ih tail_ih list₂ prem =>
    cases list₂ with
    | nil =>
      unfold listDecEq
      contradiction
    | cons head' tail' =>
      unfold listDecEq
      split
      · expose_names
        simp at prem
        obtain ⟨_,heqtail⟩ := prem
        exact tail_ih heqtail
      · grind



def ValOrRedex.decideEq (a b : ValOrRedex) : Decidable (a = b) :=
  decidable_of_bool (ValOrRedex.decEq a b) ⟨decEq_sound, decEq_complete⟩


@[grind]
instance : DecidableEq ValOrRedex := ValOrRedex.decideEq


-- mutual

-- @[reducible]
-- def ValOrRedex.decEq (a b : ValOrRedex) : Decidable (a = b) :=
--   match a, b with
--   | .leaf, .leaf => .isTrue ?_
--   | .stem a, .stem a' =>
--     match a.decEq a' with
--     | .isTrue prf => .isTrue ?_
--     | .isFalse prf => .isFalse ?_

--   | .fork a b, .fork a' b' =>
--     match a.decEq a' with
--     | .isTrue prf =>
--       match b.decEq b' with
--       | .isTrue prf => .isTrue ?_
--       | .isFalse prf => .isFalse ?_

--     | .isFalse prf => .isFalse ?_

--   | .redex a b c rest, .redex a' b' c' rest' =>
--     match a.decEq a' with
--     | .isTrue prf =>
--       match b.decEq b' with
--       | .isTrue prf =>
--         match c.decEq c' with
--         | .isTrue prf =>
--           match ValOrRedex.listDecEq rest rest' with
--           | .isTrue prf => .isTrue ?_
--           | .isFalse prf => .isFalse ?_
--         | .isFalse prf => .isFalse ?_

--       | .isFalse prf => .isFalse ?_

--     | .isFalse prf => .isFalse ?_
--   | (redex _ _ _ _), (fork _ _)
--   | (redex _ _ _ _), (stem _)
--   | (redex _ _ _ _), leaf
--   | (fork _ _), (redex _ _ _ _)
--   | (fork _ _), (stem _)
--   | (fork _ _), leaf
--   | (stem _), (redex _ _ _ _)
--   | (stem _), (fork _ _)
--   | (stem _), leaf
--   | leaf, (redex _ _ _ _)
--   | leaf, (fork _ _)
--   | leaf, (stem _) => .isFalse ?_
--   where finally repeat simp [*]



-- def ValOrRedex.listDecEq (a b : List ValOrRedex) : Decidable (a = b) :=
--   match a, b with
--   | [], [] => .isTrue ?_
--   | head :: rest, head' :: rest' =>
--     match head.decEq head' with
--     | .isTrue prf =>
--       match listDecEq rest rest' with
--       | .isTrue prf => .isTrue ?_
--       | .isFalse prf => .isFalse ?_
--     | .isFalse prf => .isFalse ?_
--   | [], _ :: _
--   | _ :: _, [] => .isFalse ?_
--   where finally repeat simp [*]

-- end


-- @[grind]
-- instance : DecidableEq ValOrRedex := ValOrRedex.decEq






/-- Rewrite rules apply to exactly 3 terms. The first of which always needs to be a value – albeit not fully recursively reduced. We never care what the 2nd contains. The third one we only care about for rules 3a-c, at which point we do need it to be a value, albeit here too not necessarily fully reduced.-/
@[grind cases]
inductive Rewrite : (a b c output : ValOrRedex) → Prop where
  | one :
    Rewrite .leaf y z
      y

  | two :
    Rewrite (.stem x) y z
      (.redex x z (.fork y z) [])

  | threeA :
    Rewrite (.fork w x) y .leaf
      w

  | threeB :
    Rewrite (.fork w x) y (.stem u)
      (.fork x u)

  | threeC :
    Rewrite (.fork w x) y (.fork u v)
      (.redex y u v [])






/-- A relation between two lists where `newList` has an item replaced from `list` -/
@[grind cases]
inductive ReplaceInList {α} : (list : List α) → (oldItem : α) → (index : Nat) → (newItem : α) → (newList : List α) → Prop where
  | here {newItem : α} :
    ReplaceInList (oldItem :: tail) oldItem 0 newItem (newItem :: tail)

  | there :
    ReplaceInList list oldItem i newItem newList →
    ReplaceInList (item :: list) oldItem (i+1) newItem (item :: newList)




/-- The single-step reduction relation on a term, with congruence -/
@[grind cases]
inductive ReductionStep : (term output : ValOrRedex) → Prop where
  | stem :
    ReductionStep a result →
    ReductionStep (.stem a) (.stem result)

  | forkFst :
    ReductionStep a resultA →
    ReductionStep (.fork a b) (.fork resultA b)

  | forkSnd :
    ReductionStep b resultB →
    ReductionStep (.fork a b) (.fork a resultB)

  | rewrite :
    Rewrite a b c output →
    ReductionStep (.redex a b c rest) output


  -- The congruence rules

  | redexFst :
    ReductionStep a resultA →
    ReductionStep (.redex a b c rest) (.redex resultA b c rest)

  | redexSnd :
    ReductionStep b resultB →
    ReductionStep (.redex a b c rest) (.redex a resultB c rest)

  | redexThrd :
    ReductionStep c resultC →
    ReductionStep (.redex a b c rest) (.redex a b resultC rest)

  /-- You can reduce any item in the `.redex` list -/
  | redexItemReplace :
    ReductionStep item reducedItem →
    ReplaceInList items item i reducedItem newItems →
    ReductionStep (.redex a b c items) (.redex a b c newItems)


/-- Rewrite rules are deterministic: same inputs give same outputs -/
theorem Rewrite.deterministic
  (h₁ : Rewrite a b c out₁)
  (h₂ : Rewrite a b c out₂)
  : out₁ = out₂ := by
  cases h₁ <;> cases h₂ <;> rfl


/-! ### One-step semi-diamond (`ReductionStep.diamond`) -/

theorem ReductionStep.reflGen_stem {s t : ValOrRedex}
    (h : Relation.ReflGen ReductionStep s t) :
    Relation.ReflGen ReductionStep (ValOrRedex.stem s) (ValOrRedex.stem t) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (ReductionStep.stem h)

theorem ReductionStep.reflTransGen_stem {s t : ValOrRedex}
    (h : Relation.ReflTransGen ReductionStep s t) :
    Relation.ReflTransGen ReductionStep (ValOrRedex.stem s) (ValOrRedex.stem t) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.stem hbc))

theorem ReductionStep.reflGen_forkFst {s t u : ValOrRedex}
    (h : Relation.ReflGen ReductionStep s t) :
    Relation.ReflGen ReductionStep (ValOrRedex.fork s u) (ValOrRedex.fork t u) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (ReductionStep.forkFst h)

theorem ReductionStep.reflTransGen_forkFst {s t u : ValOrRedex}
    (h : Relation.ReflTransGen ReductionStep s t) :
    Relation.ReflTransGen ReductionStep (ValOrRedex.fork s u) (ValOrRedex.fork t u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.forkFst hbc))

theorem ReductionStep.reflGen_forkSnd {s t u : ValOrRedex}
    (h : Relation.ReflGen ReductionStep t u) :
    Relation.ReflGen ReductionStep (ValOrRedex.fork s t) (ValOrRedex.fork s u) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (ReductionStep.forkSnd h)

theorem ReductionStep.reflTransGen_forkSnd {s t u : ValOrRedex}
    (h : Relation.ReflTransGen ReductionStep t u) :
    Relation.ReflTransGen ReductionStep (ValOrRedex.fork s t) (ValOrRedex.fork s u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.forkSnd hbc))

def ValOrRedex.redex4 (a b c : ValOrRedex) (rest : List ValOrRedex) : ValOrRedex :=
  .redex a b c rest

theorem ReductionStep.reflGen_redexFst {s t b c : ValOrRedex} (rest : List ValOrRedex)
    (h : Relation.ReflGen ReductionStep s t) :
    Relation.ReflGen ReductionStep (ValOrRedex.redex4 s b c rest)
      (ValOrRedex.redex4 t b c rest) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (ReductionStep.redexFst h)

theorem ReductionStep.reflTransGen_redexFst {s t b c : ValOrRedex} (rest : List ValOrRedex)
    (h : Relation.ReflTransGen ReductionStep s t) :
    Relation.ReflTransGen ReductionStep (ValOrRedex.redex4 s b c rest)
      (ValOrRedex.redex4 t b c rest) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.redexFst hbc))

theorem ReductionStep.reflGen_redexSnd {s t a c : ValOrRedex} (rest : List ValOrRedex)
    (h : Relation.ReflGen ReductionStep s t) :
    Relation.ReflGen ReductionStep (ValOrRedex.redex4 a s c rest)
      (ValOrRedex.redex4 a t c rest) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (ReductionStep.redexSnd h)

theorem ReductionStep.reflTransGen_redexSnd {s t a c : ValOrRedex} (rest : List ValOrRedex)
    (h : Relation.ReflTransGen ReductionStep s t) :
    Relation.ReflTransGen ReductionStep (ValOrRedex.redex4 a s c rest)
      (ValOrRedex.redex4 a t c rest) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.redexSnd hbc))

theorem ReductionStep.reflGen_redexThrd {s t a b : ValOrRedex} (rest : List ValOrRedex)
    (h : Relation.ReflGen ReductionStep s t) :
    Relation.ReflGen ReductionStep (ValOrRedex.redex4 a b s rest)
      (ValOrRedex.redex4 a b t rest) := by
  cases h with
  | refl => exact Relation.ReflGen.refl
  | single h => exact Relation.ReflGen.single (ReductionStep.redexThrd h)

theorem ReductionStep.reflTransGen_redexThrd {s t a b : ValOrRedex} (rest : List ValOrRedex)
    (h : Relation.ReflTransGen ReductionStep s t) :
    Relation.ReflTransGen ReductionStep (ValOrRedex.redex4 a b s rest)
      (ValOrRedex.redex4 a b t rest) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.redexThrd hbc))

theorem ReplaceInList.same_index {α} {list : List α} {oldItem i newItem₁ newList₁ newItem₂ newList₂}
    (h₁ : ReplaceInList list oldItem i newItem₁ newList₁)
    (h₂ : ReplaceInList list oldItem i newItem₂ newList₂)
    (heq : newList₁ = newList₂) :
    newItem₁ = newItem₂ := by
  induction h₁ generalizing newItem₂ newList₂ with
  | here =>
    cases h₂
    simp only [List.cons.injEq] at heq
    exact heq.1
  | there h ih =>
    cases h₂
    exact ih ‹_› (by injection heq)

theorem ReplaceInList.at_newItem {α} {list : List α} {item i ri list_i}
    (h : ReplaceInList list item i ri list_i) :
    ReplaceInList list_i ri i ri list_i := by
  induction h with
  | here => exact ReplaceInList.here
  | there h ih => exact ReplaceInList.there ih

theorem ReplaceInList.after {α} {list : List α} {item i ri list_i ri' list'}
    (h₁ : ReplaceInList list item i ri list_i)
    (h₂ : ReplaceInList list_i ri i ri' list') :
    ReplaceInList list item i ri' list' := by
  induction h₁ generalizing ri' list' with
  | here =>
    cases h₂
    exact ReplaceInList.here
  | there h ih =>
    cases h₂
    exact ReplaceInList.there (ih ‹ReplaceInList _ _ _ _ _›)

/-! ### Parallel reduction (confluence via Takahashi / Hindley–Rosen)

`Rewrite.two` duplicates the third argument in the contractum
(`.redex x z (.fork y z) []`). A one-step semi-diamond with `ReflGen` on the
rewrite-first side is therefore **false**: reducing `z` before firing needs
two residual steps after the rewrite. So `Relation.church_rosser` does not
apply directly to `ReductionStep`.

Instead: parallel reduction `ParStep` may fire a root rewrite **and** reduce
both residual copies of `z` in one step. Prove the diamond for `ParStep`, then
`ReductionStep ⊆ ParStep ⊆ MultiStepReduction`. -/

/-- Parallel reduction: congruence in all positions, or fire a triage rule while
parallel-reducing everything that appears in the contractum. -/
inductive ParStep : ValOrRedex → ValOrRedex → Prop where
  | leaf : ParStep .leaf .leaf
  | stem :
    ParStep a a' →
    ParStep (.stem a) (.stem a')
  | fork :
    ParStep a a' →
    ParStep b b' →
    ParStep (.fork a b) (.fork a' b')
  | redex :
    ParStep a a' →
    ParStep b b' →
    ParStep c c' →
    List.Forall₂ ParStep rest rest' →
    ParStep (.redex a b c rest) (.redex a' b' c' rest')
  /-- Rule 1: `△ · y · z → y`, with `y` parallel-reduced. -/
  | rewrite1 :
    ParStep y y' →
    ParStep (.redex .leaf y z rest) y'
  /-- Rule 2: `(△ · x) · y · z → (x · z) · (y · z)`; both copies of `z` reduced together. -/
  | rewrite2 :
    ParStep x x' →
    ParStep y y' →
    ParStep z z' →
    ParStep (.redex (.stem x) y z rest) (.redex x' z' (.fork y' z') [])
  | rewrite3a :
    ParStep w w' →
    ParStep (.redex (.fork w x) y .leaf rest) w'
  | rewrite3b :
    ParStep x x' →
    ParStep u u' →
    ParStep (.redex (.fork w x) y (.stem u) rest) (.fork x' u')
  | rewrite3c :
    ParStep y y' →
    ParStep u u' →
    ParStep v v' →
    ParStep (.redex (.fork w x) y (.fork u v) rest) (.redex y' u' v' [])

def MultiStepReduction := Relation.ReflTransGen ReductionStep

mutual
def ParStep.list_refl (rest : List ValOrRedex) : List.Forall₂ ParStep rest rest :=
  match rest with
  | [] => List.Forall₂.nil
  | x :: xs => List.Forall₂.cons (ParStep.refl x) (ParStep.list_refl xs)

def ParStep.refl (a : ValOrRedex) : ParStep a a :=
  match a with
  | .leaf => ParStep.leaf
  | .stem a => ParStep.stem (ParStep.refl a)
  | .fork a b => ParStep.fork (ParStep.refl a) (ParStep.refl b)
  | .redex a b c rest =>
    ParStep.redex (ParStep.refl a) (ParStep.refl b) (ParStep.refl c) (ParStep.list_refl rest)
end

theorem ParStep.replaceInList {items : List ValOrRedex} {item reducedItem newItems i}
    (hstep : ParStep item reducedItem)
    (hrep : ReplaceInList items item i reducedItem newItems) :
    List.Forall₂ ParStep items newItems := by
  induction hrep with
  | here =>
    exact List.Forall₂.cons hstep (ParStep.list_refl _)
  | there hrep ih =>
    exact List.Forall₂.cons (ParStep.refl _) (ih hstep)

theorem ReductionStep.to_ParStep (h : ReductionStep a b) : ParStep a b := by
  induction h with
  | stem h ih => exact ParStep.stem ih
  | forkFst h ih => exact ParStep.fork ih (ParStep.refl _)
  | forkSnd h ih => exact ParStep.fork (ParStep.refl _) ih
  | rewrite rw =>
    cases rw with
    | one => exact ParStep.rewrite1 (ParStep.refl _)
    | two => exact ParStep.rewrite2 (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
    | threeA => exact ParStep.rewrite3a (ParStep.refl _)
    | threeB => exact ParStep.rewrite3b (ParStep.refl _) (ParStep.refl _)
    | threeC => exact ParStep.rewrite3c (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
  | redexFst h ih =>
    exact ParStep.redex ih (ParStep.refl _) (ParStep.refl _) (ParStep.list_refl _)
  | redexSnd h ih =>
    exact ParStep.redex (ParStep.refl _) ih (ParStep.refl _) (ParStep.list_refl _)
  | redexThrd h ih =>
    exact ParStep.redex (ParStep.refl _) (ParStep.refl _) ih (ParStep.list_refl _)
  | redexItemReplace hitem hrep ih =>
    exact ParStep.redex (ParStep.refl _) (ParStep.refl _) (ParStep.refl _)
      (ParStep.replaceInList ih hrep)

theorem ReplaceInList.offset {α} (pref : List α) {xs : List α} {item i item' ys}
    (h : ReplaceInList xs item i item' ys) :
    ReplaceInList (pref ++ xs) item (pref.length + i) item' (pref ++ ys) := by
  induction pref with
  | nil => simpa using h
  | cons _ _ ih =>
    simpa [Nat.succ_add] using ReplaceInList.there ih

theorem MultiStepReduction.redex_at_offset {a b c : ValOrRedex} (pref : List ValOrRedex)
    {x y : ValOrRedex} {xs : List ValOrRedex}
    (h : MultiStepReduction x y) :
    MultiStepReduction (.redex a b c (pref ++ x :: xs)) (.redex a b c (pref ++ y :: xs)) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.tail ih
      (ReductionStep.redexItemReplace hstep
        (by simpa using ReplaceInList.offset pref (ReplaceInList.here (newItem := _))))

/-- Structural measure for well-founded recursion on `ValOrRedex`. -/
def ValOrRedex.depth : ValOrRedex → Nat
  | .leaf => 1
  | .stem a => depth a + 1
  | .fork a b => depth a + depth b + 1
  | .redex a b c rest => depth a + depth b + depth c + rest.foldl (fun n x => n + depth x) 0 + 1

private theorem ValOrRedex.depth_lt_stem (x : ValOrRedex) :
    ValOrRedex.depth x < ValOrRedex.depth (.stem x) := by simp [depth]

private theorem ValOrRedex.depth_lt_fork_left (x y : ValOrRedex) :
    ValOrRedex.depth x < ValOrRedex.depth (.fork x y) := by simp [depth]; omega

private theorem ValOrRedex.depth_lt_fork_right (x y : ValOrRedex) :
    ValOrRedex.depth y < ValOrRedex.depth (.fork x y) := by simp [depth]; omega

private theorem ValOrRedex.depth_lt_redex_op (a b c : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth a < ValOrRedex.depth (.redex a b c rest) := by simp [depth]; omega

private theorem ValOrRedex.depth_lt_redex_arg1 (a b c : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth b < ValOrRedex.depth (.redex a b c rest) := by simp [depth]; omega

private theorem ValOrRedex.depth_lt_redex_arg2 (a b c : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth c < ValOrRedex.depth (.redex a b c rest) := by simp [depth]; omega

def List.parDepthSum : List ValOrRedex → Nat
  | [] => 0
  | x :: xs => x.depth + parDepthSum xs

private theorem List.foldl_parDepthSum (init : Nat) (xs : List ValOrRedex) :
    xs.foldl (fun n x => n + x.depth) init = init + parDepthSum xs := by
  induction xs generalizing init with
  | nil => simp [parDepthSum]
  | cons x xs ih => simp [parDepthSum, List.foldl_cons, ih, Nat.add_assoc]

private theorem ValOrRedex.depth_lt_redex_rest_head (a b c : ValOrRedex) (r : ValOrRedex)
    (rest : List ValOrRedex) :
    ValOrRedex.depth r < ValOrRedex.depth (.redex a b c (r :: rest)) := by
  simp [ValOrRedex.depth, List.foldl_parDepthSum]
  have ha : 1 ≤ a.depth := by cases a <;> simp [ValOrRedex.depth]
  have hb : 1 ≤ b.depth := by cases b <;> simp [ValOrRedex.depth]
  have hc : 1 ≤ c.depth := by cases c <;> simp [ValOrRedex.depth]
  omega

private theorem List.parDepthSum_head_lt (x : ValOrRedex) (xs : List ValOrRedex) :
    x.depth < parDepthSum (x :: xs) + 1 := by simp [parDepthSum]; omega

private theorem List.parDepthSum_head_lt' {x : ValOrRedex} {xs : List ValOrRedex}
    {l : List ValOrRedex} (h : l = x :: xs) : x.depth < l.parDepthSum + 1 := by
  rw [h, parDepthSum]; omega

private theorem List.parDepthSum_cons_lt (x : ValOrRedex) (xs : List ValOrRedex) :
    parDepthSum xs + 1 < parDepthSum (x :: xs) + 1 := by
  have : 0 < x.depth := by cases x <;> simp [ValOrRedex.depth]
  simp [parDepthSum]; omega

private theorem List.parDepthSum_tail_lt (x : ValOrRedex) (xs : List ValOrRedex) :
    parDepthSum xs < parDepthSum (x :: xs) := by
  have : 0 < x.depth := by cases x <;> simp [ValOrRedex.depth]
  simp [parDepthSum]; omega

private theorem List.parDepthSum_lt_redex (a b c : ValOrRedex) (rest : List ValOrRedex) :
    parDepthSum rest + 1 < ValOrRedex.depth (.redex a b c rest) := by
  have hdepth : ValOrRedex.depth (.redex a b c rest) =
      a.depth + b.depth + c.depth + parDepthSum rest + 1 := by
    simp [ValOrRedex.depth, foldl_parDepthSum]
  rw [hdepth]
  have ha : 1 ≤ a.depth := by cases a <;> simp [ValOrRedex.depth]
  have hb : 1 ≤ b.depth := by cases b <;> simp [ValOrRedex.depth]
  have hc : 1 ≤ c.depth := by cases c <;> simp [ValOrRedex.depth]
  omega

private theorem ValOrRedex.depth_lt_redex_stem_op (x y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth x < ValOrRedex.depth (.redex (.stem x) y z rest) := by
  have h1 := ValOrRedex.depth_lt_stem x
  have h2 := ValOrRedex.depth_lt_redex_op (.stem x) y z rest
  omega

private theorem ValOrRedex.depth_lt_redex_fork_left (w x y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth w < ValOrRedex.depth (.redex (.fork w x) y z rest) := by
  have h1 := ValOrRedex.depth_lt_fork_left w x
  have h2 := ValOrRedex.depth_lt_redex_op (.fork w x) y z rest
  omega

private theorem ValOrRedex.depth_lt_redex_fork_right (w x y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth x < ValOrRedex.depth (.redex (.fork w x) y z rest) := by
  have h1 := ValOrRedex.depth_lt_fork_right w x
  have h2 := ValOrRedex.depth_lt_redex_op (.fork w x) y z rest
  omega

private theorem ValOrRedex.depth_lt_redex_stem_child (a b u : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth u < ValOrRedex.depth (.redex a b (.stem u) rest) := by
  have h1 := ValOrRedex.depth_lt_stem u
  have h2 := ValOrRedex.depth_lt_redex_arg2 a b (.stem u) rest
  omega

private theorem ValOrRedex.depth_lt_redex_fork_arg_left (a b u v : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth u < ValOrRedex.depth (.redex a b (.fork u v) rest) := by
  have h1 := ValOrRedex.depth_lt_fork_left u v
  have h2 := ValOrRedex.depth_lt_redex_arg2 a b (.fork u v) rest
  omega

private theorem ValOrRedex.depth_lt_redex_fork_arg_right (a b u v : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth v < ValOrRedex.depth (.redex a b (.fork u v) rest) := by
  have h1 := ValOrRedex.depth_lt_fork_right u v
  have h2 := ValOrRedex.depth_lt_redex_arg2 a b (.fork u v) rest
  omega

private theorem List.append_singleton_append (pref : List ValOrRedex) (b : ValOrRedex) (xs : List ValOrRedex) :
    pref ++ b :: xs = (pref ++ [b]) ++ xs := by simp [List.append_assoc]

private theorem List.singleton_append_cons (b : ValOrRedex) (ys : List ValOrRedex) :
    [b] ++ ys = b :: ys := rfl

private theorem ValOrRedex.depth_lt_append_parDepthSum (pref : List ValOrRedex) (x : ValOrRedex)
    (xs : List ValOrRedex) :
    x.depth < (pref ++ x :: xs).parDepthSum + 1 := by
  induction pref with
  | nil => simp [List.parDepthSum]; omega
  | cons p ps ih =>
    simp [List.parDepthSum]
    omega

private theorem ValOrRedex.depth_lt_redex_rewrite3a (w x y : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth w < ValOrRedex.depth (.redex (.fork w x) y .leaf rest) := by
  exact ValOrRedex.depth_lt_redex_fork_left w x y .leaf rest

private theorem ValOrRedex.depth_lt_redex_rewrite3b_left (w x y u : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth x < ValOrRedex.depth (.redex (.fork w x) y (.stem u) rest) := by
  have h1 := ValOrRedex.depth_lt_fork_right w x
  have h2 := ValOrRedex.depth_lt_redex_op (.fork w x) y (.stem u) rest
  omega

private theorem ValOrRedex.depth_lt_redex_rewrite3b_right (w x y u : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth u < ValOrRedex.depth (.redex (.fork w x) y (.stem u) rest) := by
  exact ValOrRedex.depth_lt_redex_stem_child (.fork w x) y u rest

private theorem ValOrRedex.depth_lt_redex_rewrite3c_left (w x y u v : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth u < ValOrRedex.depth (.redex (.fork w x) y (.fork u v) rest) := by
  exact ValOrRedex.depth_lt_redex_fork_arg_left (.fork w x) y u v rest

private theorem ValOrRedex.depth_lt_redex_rewrite3c_right (w x y u v : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth v < ValOrRedex.depth (.redex (.fork w x) y (.fork u v) rest) := by
  exact ValOrRedex.depth_lt_redex_fork_arg_right (.fork w x) y u v rest

private theorem ValOrRedex.depth_lt_redex_rewrite1 (y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth y < ValOrRedex.depth (.redex .leaf y z rest) := by
  exact ValOrRedex.depth_lt_redex_arg1 .leaf y z rest

private theorem ValOrRedex.depth_lt_redex_rewrite2_x (x y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth x < ValOrRedex.depth (.redex (.stem x) y z rest) := by
  exact ValOrRedex.depth_lt_redex_stem_op x y z rest

private theorem ValOrRedex.depth_lt_redex_rewrite2_y (x y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth y < ValOrRedex.depth (.redex (.stem x) y z rest) := by
  exact ValOrRedex.depth_lt_redex_arg1 (.stem x) y z rest

private theorem ValOrRedex.depth_lt_redex_rewrite2_z (x y z : ValOrRedex) (rest : List ValOrRedex) :
    ValOrRedex.depth z < ValOrRedex.depth (.redex (.stem x) y z rest) := by
  exact ValOrRedex.depth_lt_redex_arg2 (.stem x) y z rest

private theorem ValOrRedex.depth_wf :
    WellFounded (InvImage (· < ·) ValOrRedex.depth) :=
  InvImage.wf ValOrRedex.depth Nat.lt_wfRel.wf

/-- Well-founded induction on `ValOrRedex.depth`.
Use `induction a using ValOrRedex.depth_wf_ind with | _ a ih => ...`.
Inside `redex` cases, for `Forall₂` goals induct on the list and apply
`ih x (depth_lt_redex_rest_head …)` etc. — no mutual theorem. -/
private theorem ValOrRedex.depth_lt_redex_rest_mem (a b c : ValOrRedex) {rest : List ValOrRedex}
    {x : ValOrRedex} (hx : x ∈ rest) :
    x.depth < ValOrRedex.depth (.redex a b c rest) := by
  induction rest with
  | nil => cases hx
  | cons r rs ih =>
    simp [List.mem_cons] at hx
    cases hx with
    | inl hx =>
      rw [hx]
      exact ValOrRedex.depth_lt_redex_rest_head a b c r rs
    | inr hx =>
      have htail := ih hx
      simp [ValOrRedex.depth, List.foldl_parDepthSum] at htail ⊢
      have hr : 1 ≤ r.depth := by cases r <;> simp [ValOrRedex.depth]
      omega

private theorem ValOrRedex.depth_lt_redex_rest_extend (op arg1 arg2 : ValOrRedex) (a : ValOrRedex)
    (as : List ValOrRedex) :
    ValOrRedex.depth (.redex op arg1 arg2 as) < ValOrRedex.depth (.redex op arg1 arg2 (a :: as)) := by
  simp [ValOrRedex.depth, List.foldl_parDepthSum]
  have ha : 1 ≤ a.depth := by cases a <;> simp [ValOrRedex.depth]
  omega

private theorem ValOrRedex.depth_lt_redex_rest_append_head (op arg1 arg2 : ValOrRedex)
    (before : List ValOrRedex) (a : ValOrRedex) (as : List ValOrRedex) :
    a.depth < ValOrRedex.depth (.redex op arg1 arg2 (before ++ a :: as)) := by
  induction before with
  | nil => exact ValOrRedex.depth_lt_redex_rest_head op arg1 arg2 a as
  | cons b bs ih =>
    have h2 := ValOrRedex.depth_lt_redex_rest_extend op arg1 arg2 b (bs ++ a :: as)
    exact Nat.lt_trans ih h2

private theorem ValOrRedex.depth_lt_redex_rest_sublist_head
    (op arg1 arg2 : ValOrRedex) (a : ValOrRedex) (as rest : List ValOrRedex)
    (h : a :: as = rest) :
    a.depth < ValOrRedex.depth (.redex op arg1 arg2 rest) := by
  rw [← h]
  exact ValOrRedex.depth_lt_redex_rest_head op arg1 arg2 a as

private theorem List.Forall₂_ParStep_join_redex
    (op arg1 arg2 : ValOrRedex) (rest : List ValOrRedex)
    (joinDiamond : ∀ {x y z}, ValOrRedex.depth x < ValOrRedex.depth (.redex op arg1 arg2 rest) →
      ParStep x y → ParStep x z → ∃ d, ParStep y d ∧ ParStep z d) :
    ∀ {l₂ l₃}, List.Forall₂ ParStep rest l₂ → List.Forall₂ ParStep rest l₃ →
      ∃ l₄, List.Forall₂ ParStep l₂ l₄ ∧ List.Forall₂ ParStep l₃ l₄ := by
  induction rest with
  | nil =>
    intro l₂ l₃ h₁₂ h₁₃
    cases h₁₂
    cases h₁₃
    exact ⟨[], List.Forall₂.nil, List.Forall₂.nil⟩
  | cons hd tl tail_ih =>
    intro l₂ l₃ h₁₂ h₁₃
    cases h₁₂ with
    | cons h hxs =>
      cases h₁₃ with
      | cons h' hxs' =>
        obtain ⟨d, hb, hc⟩ :=
          joinDiamond (ValOrRedex.depth_lt_redex_rest_mem op arg1 arg2 (by simp)) h h'
        let tailJoinDiamond : ∀ {x y z},
            ValOrRedex.depth x < ValOrRedex.depth (.redex op arg1 arg2 tl) →
              ParStep x y → ParStep x z → ∃ d, ParStep y d ∧ ParStep z d :=
          fun lt hx hz =>
            joinDiamond (Nat.lt_trans lt (ValOrRedex.depth_lt_redex_rest_extend op arg1 arg2 hd tl)) hx hz
        obtain ⟨l₄, hr_b, hr_c⟩ := tail_ih tailJoinDiamond hxs hxs'
        exact ⟨d :: l₄, List.Forall₂.cons hb hr_b, List.Forall₂.cons hc hr_c⟩

@[elab_as_elim]
theorem ValOrRedex.depth_wf_ind {motive : ValOrRedex → Prop}
    (ih : ∀ a, (∀ b, ValOrRedex.depth b < ValOrRedex.depth a → motive b) → motive a)
    (a : ValOrRedex) : motive a :=
  WellFounded.induction ValOrRedex.depth_wf a ih

private theorem ValOrRedex.depth_lt_redex_rest_forall_head (op arg1 arg2 : ValOrRedex) {rest : List ValOrRedex}
    (hne : rest ≠ []) :
    ValOrRedex.depth (rest.head hne) < ValOrRedex.depth (.redex op arg1 arg2 rest) := by
  cases rest with
  | nil => exact (hne rfl).elim
  | cons a as => simp [List.head_cons]; exact ValOrRedex.depth_lt_redex_rest_head op arg1 arg2 a as

private theorem ValOrRedex.depth_lt_parDepthSum_cons_tail
    (pref : List ValOrRedex) (x : ValOrRedex) (xs : List ValOrRedex)
    {y : ValOrRedex} (_ : ParStep x y) :
    x.depth < (pref ++ x :: xs).parDepthSum + 1 :=
  ValOrRedex.depth_lt_append_parDepthSum pref x xs

private theorem ValOrRedex.depth_lt_parDepthSum_cons (x : ValOrRedex) (xs : List ValOrRedex)
    {y : ValOrRedex} (h : ParStep x y) :
    x.depth < (x :: xs).parDepthSum + 1 :=
  ValOrRedex.depth_lt_parDepthSum_cons_tail [] x xs h

private theorem List.Forall₂_ParStep_redexGo_append
    {op arg1 arg2 : ValOrRedex} {pref : List ValOrRedex}
    {a b : ValOrRedex} {l₁ l₂ : List ValOrRedex}
    (_hx : ParStep a b) (_hrest : List.Forall₂ ParStep l₁ l₂)
    (ih : ∀ pref', MultiStepReduction (.redex op arg1 arg2 (pref' ++ l₁))
      (.redex op arg1 arg2 (pref' ++ l₂))) :
    MultiStepReduction (.redex op arg1 arg2 (pref ++ b :: l₁))
      (.redex op arg1 arg2 (pref ++ b :: l₂)) := by
  rw [List.append_singleton_append pref b l₁, List.append_singleton_append pref b l₂]
  exact ih (pref ++ [b])

mutual
private theorem ParStep.to_MultiStep_redexGo
    {op arg1 arg2 : ValOrRedex} (pref : List ValOrRedex)
    {rest rest' : List ValOrRedex} (h : List.Forall₂ ParStep rest rest') :
    MultiStepReduction (.redex op arg1 arg2 (pref ++ rest)) (.redex op arg1 arg2 (pref ++ rest')) := by
  match rest, rest', h with
  | [], [], .nil => exact Relation.ReflTransGen.refl
  | a :: l₁, b :: l₂, .cons hx hrest =>
    refine Relation.ReflTransGen.trans
      (MultiStepReduction.redex_at_offset pref (ParStep.to_MultiStep hx))
      (List.Forall₂_ParStep_redexGo_append hx hrest fun pref' =>
        ParStep.to_MultiStep_redexGo (op := op) (arg1 := arg1) (arg2 := arg2) pref' hrest)
termination_by rest.parDepthSum + 1
decreasing_by
  all_goals simp_wf
  all_goals try
    first
    | apply ValOrRedex.depth_lt_parDepthSum_cons a l₁ hx
    | apply List.parDepthSum_tail_lt

theorem ParStep.to_MultiStep {a b : ValOrRedex} (h : ParStep a b) : MultiStepReduction a b := by
  cases h with
  | leaf => exact Relation.ReflTransGen.refl
  | stem h =>
    exact ReductionStep.reflTransGen_stem (ParStep.to_MultiStep h)
  | fork h1 h2 =>
    exact Relation.ReflTransGen.trans (ReductionStep.reflTransGen_forkFst (ParStep.to_MultiStep h1))
      (ReductionStep.reflTransGen_forkSnd (ParStep.to_MultiStep h2))
  | redex h1 h2 h3 hrest =>
    refine Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexFst _ (ParStep.to_MultiStep h1)) ?_
    refine Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexSnd _ (ParStep.to_MultiStep h2)) ?_
    refine Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexThrd _ (ParStep.to_MultiStep h3)) ?_
    exact ParStep.to_MultiStep_redexGo [] hrest
  | rewrite1 hy =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (ReductionStep.rewrite Rewrite.one))
      (ParStep.to_MultiStep hy)
  | rewrite2 hx hy hz =>
    refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single (ReductionStep.rewrite Rewrite.two)) ?_
    refine Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexFst _ (ParStep.to_MultiStep hx)) ?_
    refine Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexSnd _ (ParStep.to_MultiStep hz)) ?_
    exact ReductionStep.reflTransGen_redexThrd _ (Relation.ReflTransGen.trans
      (ReductionStep.reflTransGen_forkFst (ParStep.to_MultiStep hy))
      (ReductionStep.reflTransGen_forkSnd (ParStep.to_MultiStep hz)))
  | rewrite3a hw =>
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single (ReductionStep.rewrite Rewrite.threeA))
      (ParStep.to_MultiStep hw)
  | rewrite3b hx hu =>
    refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single (ReductionStep.rewrite Rewrite.threeB)) ?_
    exact Relation.ReflTransGen.trans (ReductionStep.reflTransGen_forkFst (ParStep.to_MultiStep hx))
      (ReductionStep.reflTransGen_forkSnd (ParStep.to_MultiStep hu))
  | rewrite3c hy hu hv =>
    refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single (ReductionStep.rewrite Rewrite.threeC)) ?_
    refine Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexFst _ (ParStep.to_MultiStep hy)) ?_
    exact Relation.ReflTransGen.trans (ReductionStep.reflTransGen_redexSnd _ (ParStep.to_MultiStep hu))
      (ReductionStep.reflTransGen_redexThrd _ (ParStep.to_MultiStep hv))
termination_by ValOrRedex.depth a
decreasing_by
  all_goals try
    first
    | apply ValOrRedex.depth_lt_stem
    | apply ValOrRedex.depth_lt_fork_left
    | apply ValOrRedex.depth_lt_fork_right
    | apply ValOrRedex.depth_lt_redex_op
    | apply ValOrRedex.depth_lt_redex_arg1
    | apply ValOrRedex.depth_lt_redex_arg2
    | apply ValOrRedex.depth_lt_redex_rest_head
    | apply List.parDepthSum_lt_redex
    | apply ValOrRedex.depth_lt_redex_rewrite1
    | apply ValOrRedex.depth_lt_redex_rewrite2_x
    | apply ValOrRedex.depth_lt_redex_rewrite2_y
    | apply ValOrRedex.depth_lt_redex_rewrite2_z
    | apply ValOrRedex.depth_lt_redex_rewrite3a
    | apply ValOrRedex.depth_lt_redex_rewrite3b_left
    | apply ValOrRedex.depth_lt_redex_rewrite3b_right
    | apply ValOrRedex.depth_lt_redex_rewrite3c_left
    | apply ValOrRedex.depth_lt_redex_rewrite3c_right
end

theorem ParStep.to_MultiStep_redexRest {a b c : ValOrRedex} {rest rest' : List ValOrRedex}
    (h : List.Forall₂ ParStep rest rest') :
    MultiStepReduction (.redex a b c rest) (.redex a b c rest') :=
  ParStep.to_MultiStep_redexGo [] h

theorem ParStep.diamond (h₁ : ParStep a b) (h₂ : ParStep a c) :
    ∃ d, ParStep b d ∧ ParStep c d := by
  suffices ∀ a b c, ParStep a b → ParStep a c → ∃ d, ParStep b d ∧ ParStep c d by
    exact this a b c h₁ h₂
  intro a
  induction a using ValOrRedex.depth_wf_ind with
  | _ a ih =>
    intro b c h₁ h₂
    let diamond {x y z : ValOrRedex} (lt : ValOrRedex.depth x < ValOrRedex.depth a)
        (hx : ParStep x y) (hz : ParStep x z) : ∃ d, ParStep y d ∧ ParStep z d :=
      ih x lt y z hx hz
    cases a with
    | leaf =>
      cases h₁
      cases h₂
      exact ⟨ValOrRedex.leaf, ParStep.leaf, ParStep.leaf⟩
    | stem x =>
      cases h₁ with
      | stem hx =>
        cases h₂ with
        | stem hx' =>
          obtain ⟨d, hb, hc⟩ := diamond (ValOrRedex.depth_lt_stem x) hx hx'
          exact ⟨ValOrRedex.stem d, ParStep.stem hb, ParStep.stem hc⟩
    | fork x y =>
      cases h₁ with
      | fork hx hy =>
        cases h₂ with
        | fork hx' hy' =>
          obtain ⟨dx, hxb, hxc⟩ := diamond (ValOrRedex.depth_lt_fork_left x y) hx hx'
          obtain ⟨dy, hyb, hyc⟩ := diamond (ValOrRedex.depth_lt_fork_right x y) hy hy'
          exact ⟨ValOrRedex.fork dx dy, ParStep.fork hxb hyb, ParStep.fork hxc hyc⟩
    | redex op arg1 arg2 rest =>
      let join_rest := @List.Forall₂_ParStep_join_redex op arg1 arg2 rest
        (fun lt hx hz => diamond lt hx hz)
      cases op with
      | leaf =>
        cases h₁ with
        | redex ha hb hc hrest =>
          cases ha with
          | leaf =>
            cases h₂ with
            | redex ha' hb' hc' hrest' =>
              cases ha' with
              | leaf =>
                obtain ⟨y4, hy_b, hy_c⟩ :=
                  diamond (ValOrRedex.depth_lt_redex_arg1 .leaf arg1 arg2 rest) hb hb'
                obtain ⟨z4, hz_b, hz_c⟩ :=
                  diamond (ValOrRedex.depth_lt_redex_arg2 .leaf arg1 arg2 rest) hc hc'
                obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
                exact ⟨ValOrRedex.redex ValOrRedex.leaf y4 z4 rest4,
                  ParStep.redex ParStep.leaf hy_b hz_b hr_b,
                  ParStep.redex ParStep.leaf hy_c hz_c hr_c⟩
            | rewrite1 hyr =>
              obtain ⟨y4, hy_b, hy_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite1 arg1 arg2 rest) hb hyr
              exact ⟨y4, ParStep.rewrite1 hy_b, hy_c⟩
        | rewrite1 hy =>
          cases h₂ with
          | redex ha' hb' _ _ =>
            cases ha' with
            | leaf =>
              obtain ⟨y4, hy_b, hy_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite1 arg1 arg2 rest) hy hb'
              exact ⟨y4, hy_b, ParStep.rewrite1 hy_c⟩
          | rewrite1 hy' =>
            obtain ⟨y4, hy_b, hy_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_rewrite1 arg1 arg2 rest) hy hy'
            exact ⟨y4, hy_b, hy_c⟩
      | stem x =>
        cases h₁ with
        | redex ha hb hc hrest =>
          cases ha with
          | stem hax =>
            cases h₂ with
            | redex ha' hb' hc' hrest' =>
              cases ha' with
              | stem hax' =>
                obtain ⟨x4, hx_b, hx_c⟩ :=
                  diamond (ValOrRedex.depth_lt_redex_stem_op x arg1 arg2 rest) hax hax'
                obtain ⟨y4, hy_b, hy_c⟩ :=
                  diamond (ValOrRedex.depth_lt_redex_arg1 (.stem x) arg1 arg2 rest) hb hb'
                obtain ⟨z4, hz_b, hz_c⟩ :=
                  diamond (ValOrRedex.depth_lt_redex_arg2 (.stem x) arg1 arg2 rest) hc hc'
                obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
                exact ⟨ValOrRedex.redex (ValOrRedex.stem x4) y4 z4 rest4,
                  ParStep.redex (ParStep.stem hx_b) hy_b hz_b hr_b,
                  ParStep.redex (ParStep.stem hx_c) hy_c hz_c hr_c⟩
            | rewrite2 hxr hyr hzr =>
              obtain ⟨x4, hx_b, hx_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite2_x x arg1 arg2 rest) hax hxr
              obtain ⟨y4, hy_b, hy_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite2_y x arg1 arg2 rest) hb hyr
              obtain ⟨z4, hz_b, hz_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite2_z x arg1 arg2 rest) hc hzr
              exact ⟨ValOrRedex.redex x4 z4 (ValOrRedex.fork y4 z4) [], ParStep.rewrite2 hx_b hy_b hz_b,
                ParStep.redex hx_c hz_c (ParStep.fork hy_c hz_c) (ParStep.list_refl [])⟩
        | rewrite2 hx hy hz =>
          cases h₂ with
          | redex ha' hb' hc' hrest' =>
            cases ha' with
            | stem hax =>
              obtain ⟨x4, hx_b, hx_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite2_x x arg1 arg2 rest) hx hax
              obtain ⟨y4, hy_b, hy_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite2_y x arg1 arg2 rest) hy hb'
              obtain ⟨z4, hz_b, hz_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite2_z x arg1 arg2 rest) hz hc'
              exact ⟨ValOrRedex.redex x4 z4 (ValOrRedex.fork y4 z4) [],
                ParStep.redex hx_b hz_b (ParStep.fork hy_b hz_b) (ParStep.list_refl []),
                ParStep.rewrite2 hx_c hy_c hz_c⟩
          | rewrite2 hx' hy' hz' =>
            obtain ⟨x4, hx_b, hx_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_rewrite2_x x arg1 arg2 rest) hx hx'
            obtain ⟨y4, hy_b, hy_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_rewrite2_y x arg1 arg2 rest) hy hy'
            obtain ⟨z4, hz_b, hz_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_rewrite2_z x arg1 arg2 rest) hz hz'
            exact ⟨ValOrRedex.redex x4 z4 (ValOrRedex.fork y4 z4) [],
              ParStep.redex hx_b hz_b (ParStep.fork hy_b hz_b) (ParStep.list_refl []),
              ParStep.redex hx_c hz_c (ParStep.fork hy_c hz_c) (ParStep.list_refl [])⟩
      | fork w x =>
        cases arg2 with
        | leaf =>
          cases h₁ with
          | redex ha hb hc hrest =>
            cases ha with
            | fork hw hx =>
              cases hc with
              | leaf =>
                cases h₂ with
                | redex ha' hb' hc' hrest' =>
                  cases ha' with
                  | fork hw' hx' =>
                    cases hc' with
                    | leaf =>
                      obtain ⟨w4, hw_b, hw_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_left w x arg1 .leaf rest) hw hw'
                      obtain ⟨x4, hx_b, hx_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_right w x arg1 .leaf rest) hx hx'
                      obtain ⟨y4, hy_b, hy_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 .leaf rest) hb hb'
                      obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
                      exact ⟨ValOrRedex.redex (ValOrRedex.fork w4 x4) y4 ValOrRedex.leaf rest4,
                        ParStep.redex (ParStep.fork hw_b hx_b) hy_b ParStep.leaf hr_b,
                        ParStep.redex (ParStep.fork hw_c hx_c) hy_c ParStep.leaf hr_c⟩
                | rewrite3a hwr =>
                  obtain ⟨w4, hw_b, hw_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3a w x arg1 rest) hw hwr
                  exact ⟨w4, ParStep.rewrite3a hw_b, hw_c⟩
          | rewrite3a hw =>
            cases h₂ with
            | redex ha' hb' hc' hrest' =>
              cases ha' with
              | fork hw' hx' =>
                cases hc' with
                | leaf =>
                  obtain ⟨w4, hw_b, hw_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3a w x arg1 rest) hw hw'
                  exact ⟨w4, hw_b, ParStep.rewrite3a hw_c⟩
            | rewrite3a hw' =>
              obtain ⟨w4, hw_b, hw_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite3a w x arg1 rest) hw hw'
              exact ⟨w4, hw_b, hw_c⟩
        | stem u =>
          cases h₁ with
          | redex ha hb hc hrest =>
            cases ha with
            | fork hw hx =>
              cases hc with
              | stem hu =>
                cases h₂ with
                | redex ha' hb' hc' hrest' =>
                  cases ha' with
                  | fork hw' hx' =>
                    cases hc' with
                    | stem hu' =>
                      obtain ⟨w4, hw_b, hw_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_left w x arg1 (.stem u) rest) hw hw'
                      obtain ⟨x4, hx_b, hx_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_right w x arg1 (.stem u) rest) hx hx'
                      obtain ⟨y4, hy_b, hy_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 (.stem u) rest) hb hb'
                      obtain ⟨u4, hu_b, hu_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_stem_child (.fork w x) arg1 u rest) hu hu'
                      obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
                      exact ⟨ValOrRedex.redex (ValOrRedex.fork w4 x4) y4 (ValOrRedex.stem u4) rest4,
                        ParStep.redex (ParStep.fork hw_b hx_b) hy_b (ParStep.stem hu_b) hr_b,
                        ParStep.redex (ParStep.fork hw_c hx_c) hy_c (ParStep.stem hu_c) hr_c⟩
                | rewrite3b hxr hur =>
                  obtain ⟨x4, hx_b, hx_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3b_left w x arg1 u rest) hx hxr
                  obtain ⟨u4, hu_b, hu_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3b_right w x arg1 u rest) hu hur
                  exact ⟨ValOrRedex.fork x4 u4, ParStep.rewrite3b hx_b hu_b, ParStep.fork hx_c hu_c⟩
          | rewrite3b hx hu =>
            cases h₂ with
            | redex ha' hb' hc' hrest' =>
              cases ha' with
              | fork hw' hx' =>
                cases hc' with
                | stem hu' =>
                  obtain ⟨x4, hx_b, hx_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3b_left w x arg1 u rest) hx hx'
                  obtain ⟨u4, hu_b, hu_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3b_right w x arg1 u rest) hu hu'
                  exact ⟨ValOrRedex.fork x4 u4, ParStep.fork hx_b hu_b, ParStep.rewrite3b hx_c hu_c⟩
            | rewrite3b hx' hu' =>
              obtain ⟨x4, hx_b, hx_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite3b_left w x arg1 u rest) hx hx'
              obtain ⟨u4, hu_b, hu_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite3b_right w x arg1 u rest) hu hu'
              exact ⟨ValOrRedex.fork x4 u4, ParStep.fork hx_b hu_b, ParStep.fork hx_c hu_c⟩
        | fork u v =>
          cases h₁ with
          | redex ha hb hc hrest =>
            cases ha with
            | fork hw hx =>
              cases hc with
              | fork hu hv =>
                cases h₂ with
                | redex ha' hb' hc' hrest' =>
                  cases ha' with
                  | fork hw' hx' =>
                    cases hc' with
                    | fork hu' hv' =>
                      obtain ⟨w4, hw_b, hw_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_left w x arg1 (.fork u v) rest) hw hw'
                      obtain ⟨x4, hx_b, hx_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_right w x arg1 (.fork u v) rest) hx hx'
                      obtain ⟨y4, hy_b, hy_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 (.fork u v) rest) hb hb'
                      obtain ⟨u4, hu_b, hu_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_arg_left (.fork w x) arg1 u v rest) hu hu'
                      obtain ⟨v4, hv_b, hv_c⟩ :=
                        diamond (ValOrRedex.depth_lt_redex_fork_arg_right (.fork w x) arg1 u v rest) hv hv'
                      obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
                      exact ⟨ValOrRedex.redex (ValOrRedex.fork w4 x4) y4 (ValOrRedex.fork u4 v4) rest4,
                        ParStep.redex (ParStep.fork hw_b hx_b) hy_b (ParStep.fork hu_b hv_b) hr_b,
                        ParStep.redex (ParStep.fork hw_c hx_c) hy_c (ParStep.fork hu_c hv_c) hr_c⟩
                | rewrite3c hyr hur hvr =>
                  obtain ⟨y4, hy_b, hy_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 (.fork u v) rest) hb hyr
                  obtain ⟨u4, hu_b, hu_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3c_left w x arg1 u v rest) hu hur
                  obtain ⟨v4, hv_b, hv_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3c_right w x arg1 u v rest) hv hvr
                  exact ⟨ValOrRedex.redex y4 u4 v4 [],
                    ParStep.rewrite3c hy_b hu_b hv_b,
                    ParStep.redex hy_c hu_c hv_c (ParStep.list_refl [])⟩
          | rewrite3c hy hu hv =>
            cases h₂ with
            | redex ha' hb' hc' hrest' =>
              cases ha' with
              | fork hw' hx' =>
                cases hc' with
                | fork hu' hv' =>
                  obtain ⟨y4, hy_b, hy_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 (.fork u v) rest) hy hb'
                  obtain ⟨u4, hu_b, hu_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3c_left w x arg1 u v rest) hu hu'
                  obtain ⟨v4, hv_b, hv_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_rewrite3c_right w x arg1 u v rest) hv hv'
                  exact ⟨ValOrRedex.redex y4 u4 v4 [], ParStep.redex hy_b hu_b hv_b (ParStep.list_refl []),
                    ParStep.rewrite3c hy_c hu_c hv_c⟩
            | rewrite3c hy' hu' hv' =>
              obtain ⟨y4, hy_b, hy_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 (.fork u v) rest) hy hy'
              obtain ⟨u4, hu_b, hu_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite3c_left w x arg1 u v rest) hu hu'
              obtain ⟨v4, hv_b, hv_c⟩ :=
                diamond (ValOrRedex.depth_lt_redex_rewrite3c_right w x arg1 u v rest) hv hv'
              exact ⟨ValOrRedex.redex y4 u4 v4 [], ParStep.redex hy_b hu_b hv_b (ParStep.list_refl []),
                ParStep.redex hy_c hu_c hv_c (ParStep.list_refl [])⟩
        | redex oa ob oc orest =>
          cases h₁ with
          | redex ha hb hc hrest =>
            cases h₂ with
            | redex ha' hb' hc' hrest' =>
              cases ha with
              | fork hw hx =>
                cases ha' with
                | fork hw' hx' =>
                  obtain ⟨w4, hw_b, hw_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_fork_left w x arg1 (.redex oa ob oc orest) rest) hw hw'
                  obtain ⟨x4, hx_b, hx_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_fork_right w x arg1 (.redex oa ob oc orest) rest) hx hx'
                  obtain ⟨y4, hy_b, hy_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_arg1 (.fork w x) arg1 (.redex oa ob oc orest) rest) hb hb'
                  obtain ⟨inner4, hc_b, hc_c⟩ :=
                    diamond (ValOrRedex.depth_lt_redex_arg2 (.fork w x) arg1 (.redex oa ob oc orest) rest) hc hc'
                  obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
                  exact ⟨ValOrRedex.redex (ValOrRedex.fork w4 x4) y4 inner4 rest4,
                    ParStep.redex (ParStep.fork hw_b hx_b) hy_b hc_b hr_b,
                    ParStep.redex (ParStep.fork hw_c hx_c) hy_c hc_c hr_c⟩
      | redex oa ob oc orest =>
        cases h₁ with
        | redex ha hb hc hrest =>
          cases h₂ with
          | redex ha' hb' hc' hrest' =>
            obtain ⟨op4, hop_b, hop_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_op (.redex oa ob oc orest) arg1 arg2 rest) ha ha'
            obtain ⟨arg14, h1_b, h1_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_arg1 (.redex oa ob oc orest) arg1 arg2 rest) hb hb'
            obtain ⟨arg24, h2_b, h2_c⟩ :=
              diamond (ValOrRedex.depth_lt_redex_arg2 (.redex oa ob oc orest) arg1 arg2 rest) hc hc'
            obtain ⟨rest4, hr_b, hr_c⟩ := join_rest hrest hrest'
            exact ⟨ValOrRedex.redex op4 arg14 arg24 rest4, ParStep.redex hop_b h1_b h2_b hr_b,
              ParStep.redex hop_c h1_c h2_c hr_c⟩

theorem ParStep.reflTransGen_to_MultiStep
    (h : Relation.ReflTransGen ParStep a b) : MultiStepReduction a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact Relation.ReflTransGen.trans ih (ParStep.to_MultiStep hbc)

theorem MultiStepReduction.to_reflTransGen_ParStep
    (h : MultiStepReduction a b) : Relation.ReflTransGen ParStep a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact Relation.ReflTransGen.trans ih (Relation.ReflTransGen.single (ReductionStep.to_ParStep hbc))

theorem ParStep.semi_diamond {a b c : ValOrRedex}
    (hab : ParStep a b) (hac : ParStep a c) :
    ∃ d, Relation.ReflGen ParStep b d ∧ Relation.ReflTransGen ParStep c d := by
  obtain ⟨d, hb, hc⟩ := ParStep.diamond hab hac
  exact ⟨d, Relation.ReflGen.single hb, Relation.ReflTransGen.single hc⟩

/-- Confluence of multi-step reduction.

Proof strategy: parallel reduction `ParStep` (see above). Do **not** use
Newman’s lemma — the calculus need not terminate. Do **not** use
`Relation.church_rosser` on raw `ReductionStep`: rule 2 duplicates `z`. -/





theorem MultiStepReduction.confluence
  (h₁ : MultiStepReduction a b)
  (h₂ : MultiStepReduction a c)
  : ∃ d, MultiStepReduction b d ∧ MultiStepReduction c d := by
  have h₁' := MultiStepReduction.to_reflTransGen_ParStep h₁
  have h₂' := MultiStepReduction.to_reflTransGen_ParStep h₂
  obtain ⟨d, hb, hc⟩ :=
    Relation.church_rosser (fun _ _ _ hab hac => ParStep.semi_diamond hab hac) h₁' h₂'
  exact ⟨d, ParStep.reflTransGen_to_MultiStep hb, ParStep.reflTransGen_to_MultiStep hc⟩
