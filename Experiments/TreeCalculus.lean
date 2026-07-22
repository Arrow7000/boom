import Mathlib.Tactic.Tauto
import Mathlib.Logic.Relation

/-- Static values, that cannot be reduced further, not even their subterms -/
@[grind cases]
inductive Value : Type where
  | leaf : Value
  | stem : Value → Value
  | fork : Value → Value → Value




@[grind cases]
inductive ValOrRedex : Type where
  | leaf : ValOrRedex
  | stem : ValOrRedex → ValOrRedex
  | fork : ValOrRedex → ValOrRedex → ValOrRedex
  | redex : ValOrRedex → ValOrRedex → ValOrRedex → List ValOrRedex → ValOrRedex
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



-- @[grind cases]
-- inductive MultiStepReduction : (term output : ValOrRedex) → Prop where
--   | refl :
--     MultiStepReduction term term

--   | rel :
--     ReductionStep term output →
--     MultiStepReduction term output

--   | trans :
--     MultiStepReduction term output₁ →
--     MultiStepReduction output₁ output₂ →
--     MultiStepReduction term output₂



def MultiStepReduction := Relation.ReflTransGen ReductionStep


/-- Confluence of multi-step reduction.

The five triage rules are left-linear and non-overlapping: once the operator
(and, for 3a–c, the argument) is a value, exactly one rule matches a given
redex. Rules never pattern-match on a redex, so reducing a subterm cannot flip
*which* rule applies — it can only delay firing. Divergence is only about
*where* you step, and those steps commute.

@TODO Proof strategy (do **not** induct blindly on `ReflTransGen`):
1. Prove a one-step diamond / strip lemma:
   if `a → b` and `a → c`, then `b` and `c` join;
   or: if `a → b` and `a ↠ c`, then `∃ d, b ↠ d ∧ c ↠ d`.
2. Lift that to full confluence.
Newman’s lemma (local confluence + termination) is the wrong tool here:
the calculus is Turing-complete, so reduction need not terminate. Use the
orthogonal-TRS story instead (non-overlap + left-linearity ⇒ confluence). -/
theorem MultiStepReduction.confluence
  (h₁ : MultiStepReduction a b)
  (h₂ : MultiStepReduction a c)
  : ∃ d, MultiStepReduction b d ∧ MultiStepReduction c d := by
  induction h₁ generalizing c with
  | refl =>
    exists c
    simp [*]
    refine .refl
  | tail h r ih =>
    expose_names
    have ⟨d,prf⟩ := ih h₂
    refine ⟨d,?_,prf.right⟩
    have : MultiStepReduction a c_1 := ?_

    exact ih this |>.left

    sorry
  -- | trans a b aih bih =>
  --   expose_names
  --   cases h₂
  --   · exists output₂
  --     constructor
  --     constructor
  --     refine .trans a b

  --   ·
  --     expose_names
  --     have := aih a
  --     have := aih (.rel h)
  --     have := bih b

  --     -- apply bih


  -- | rel reduct =>
  --   induction reduct
  -- sorry










@[grind cases]
inductive Term : Type where
  | term : List Term → Term


@[grind,reducible]
def Term.decEq (a b : Term) : Decidable (a = b) :=
    match a, b with
    | .term [], .term [] =>
      .isTrue ?_
    | .term (a :: as), .term (b :: bs) =>
      match a.decEq b with
      | .isTrue prf =>
        match (Term.term as).decEq (.term bs) with
        | .isTrue prf' => .isTrue ?_
        | .isFalse prf' => .isFalse ?_
      | .isFalse prf => .isFalse ?_
    | .term (_ :: _), .term [] =>
      .isFalse ?_
    | .term [], .term (_ :: _) =>
      .isFalse ?_
  where finally
    · simp
    · subst_eqs
      simp
    · grind
    · grind
    · grind
    · simp


@[grind, simp]
theorem Term.nil_ne_cons : ∀ (a : Term) (as : List Term), Term.term [] ≠ Term.term (a :: as) := by
  intro a as h
  injection h with h'
  exact List.noConfusion h'

-- Mark term constructor as injective for simp
@[simp, grind]
theorem Term.term_injective {xs ys : List Term} : Term.term xs = Term.term ys ↔ xs = ys := by
  constructor
  · intro h; injection h
  · intro h; rw [h]


@[grind]
instance : DecidableEq Term := Term.decEq



/-- Current `⬝`: prepends the left term onto the *right* term's child list.
This is **not** the official multi-child application (see `Term.apply` below). -/
@[reducible,grind]
def Term.cons (term : Term) (terms : Term) :=
  match terms with
  | .term terms => Term.term (term :: terms)

/-- Spec application: attach `arg` as the rightmost child of `fn`'s root.
Application itself is left-associative; “to the right” means where the child
hangs on the tree, i.e. `children ++ [arg]`, not prepending onto `arg`. -/
@[reducible, grind]
def Term.apply (fn arg : Term) : Term :=
  match fn with
  | .term cs => .term (cs ++ [arg])

@[match_pattern]
notation "Δ" => Term.term []

@[inherit_doc, match_pattern] infixl:67 " ⬝ " => Term.cons
@[inherit_doc, match_pattern] infixl:67 " ▷ " => Term.apply

def x := Δ
def y := Δ
def z := Δ
def u := Δ
def v := Δ

/-! ### Does `⬝` match the official spec? (no — `▷` does)

In the multi-child reading, `△ a b c` is a node whose children are `[a, b, c]`
(the leading `△` *is* the node, not a child). So:
- leaf: `△` = `term []`
- stem `a`: `△ a` = `term [a]`
- fork `a b`: `△ a b` = `term [a, b]`
- redex `a b c`: `△ a b c` = `term [a, b, c]`

Rule 1 shape `△ △ y z` = `term [Δ, y, z]`. -/

-- `▷` builds the official shapes
#guard decide (Δ ▷ Δ = Term.term [Δ])
#guard decide (Δ ▷ Δ ▷ y = Term.term [Δ, y])
#guard decide (Δ ▷ Δ ▷ y ▷ z = Term.term [Δ, y, z])
-- Rule 2: △ (△ x) y z
#guard decide (Δ ▷ (Δ ▷ x) ▷ y ▷ z = Term.term [Δ ▷ x, y, z])
-- Rule 3a: △ (△ w x) y △
#guard decide (Δ ▷ (Δ ▷ Δ ▷ Δ) ▷ y ▷ Δ = Term.term [Δ ▷ Δ ▷ Δ, y, Δ])
-- Rule 3b/3c argument shapes
#guard decide (Δ ▷ u = Term.term [u])
#guard decide (Δ ▷ u ▷ v = Term.term [u, v])

-- Current `⬝` nests instead of growing children on the left root.
-- #eval below: `⬝` ⇒ `term [term [term [term []]]]`, `▷` ⇒ `term [Δ, y, z]`
#eval Δ ⬝ Δ ⬝ y ⬝ z
#eval Δ ▷ Δ ▷ y ▷ z
#eval (Δ ▷ Δ ▷ ((Δ ▷ Δ) ▷ x ▷ (y ▷ z)))

@[grind cases]
inductive RewriteRules : (input output : Term) → Prop where
  | one :
    RewriteRules (Δ⬝Δ⬝y⬝z)
      y

  | two :
    RewriteRules (Δ⬝(Δ⬝x)⬝y⬝z)
      (x⬝z⬝(y⬝z))

  | threeA :
    RewriteRules (Δ⬝(Δ⬝w⬝x)⬝y⬝Δ)
      w

  | threeB :
    RewriteRules (Δ⬝(Δ⬝w⬝x)⬝y⬝(Δ⬝u))
      (x⬝u)

  | threeC :
    RewriteRules (Δ⬝(Δ⬝w⬝x)⬝y⬝(Δ⬝u⬝v))
      (y⬝u⬝v)


-- Full reduction relation: includes the 5 rules + congruence
@[grind cases]
inductive Reduces : (input output : Term) → Prop where
  | rule {t t' : Term} :
      RewriteRules t t' →
      Reduces t t'
  | congr_left {t1 t1' t2 : Term} :
      Reduces t1 t1' →
      Reduces (t1⬝t2) (t1'⬝t2)
  | congr_right {t1 t2 t2' : Term} :
      Reduces t2 t2' →
      Reduces (t1⬝t2) (t1⬝t2')









/-- This term is rewritable. I.e. it is not a "value" but a "program" -/
@[simp,grind]
def Term.IsRewritable (term : Term) := ∃ output, RewriteRules term output

/-- Is not rewritable – but can still be *reducible* if its subterms can be reduced! -/
@[simp,grind]
def Term.IsNotRewritable (term : Term) := ∀ output, ¬RewriteRules term output


-- Values (irreducible terms) are exactly: leafs, stems, and forks
@[simp,grind]
def Term.IsLeaf (t : Term) : Prop := t = Δ
@[simp,grind]
def Term.IsStem (t : Term) : Prop := ∃ a, t = (Δ⬝a)
@[simp,grind]
def Term.IsFork (t : Term) : Prop := ∃ a b, t = (Δ⬝a⬝b)




-- Helper lemmas to show Δ doesn't match any rewrite rule patterns
theorem Term.delta_ne_pattern1 : ∀ y z, Δ ≠ Δ ⬝ Δ ⬝ y ⬝ z := by
  intro y z heq
  unfold Term.cons at heq
  cases z; rename_i zs
  apply Term.nil_ne_cons
  exact heq

theorem Term.delta_ne_pattern2 : ∀ x y z, Δ ≠ Δ ⬝ (Δ ⬝ x) ⬝ y ⬝ z := by
  intro x y z heq
  unfold Term.cons at heq
  cases z; rename_i zs
  apply Term.nil_ne_cons
  exact heq

theorem Term.delta_ne_pattern3a : ∀ w x y, Δ ≠ Δ ⬝ (Δ ⬝ w ⬝ x) ⬝ y ⬝ Δ := by
  intro w x y heq
  unfold Term.cons at heq
  apply Term.nil_ne_cons
  exact heq

theorem Term.delta_ne_pattern3b : ∀ w x y u, Δ ≠ Δ ⬝ (Δ ⬝ w ⬝ x) ⬝ y ⬝ (Δ ⬝ u) := by
  intro w x y u heq
  unfold Term.cons at heq
  cases u; rename_i us
  apply Term.nil_ne_cons
  exact heq

theorem Term.delta_ne_pattern3c : ∀ w x y u v, Δ ≠ Δ ⬝ (Δ ⬝ w ⬝ x) ⬝ y ⬝ (Δ ⬝ u ⬝ v) := by
  intro w x y u v heq
  unfold Term.cons at heq
  cases v; rename_i vs
  apply Term.nil_ne_cons
  exact heq

@[grind]
theorem RewriteRules.leaf_irreducible (t : Term) (h : t.IsLeaf) : t.IsNotRewritable := by
  simp [Term.IsLeaf] at h
  subst h
  intro output prem
  -- Use the recursor with a motive that gives us an equality to work with
  refine @RewriteRules.rec (fun input _ _ => input = Δ → False) ?one ?two ?threeA ?threeB ?threeC Δ output prem rfl
  case one => exact fun heq => Term.delta_ne_pattern1 _ _ heq.symm
  case two => exact fun heq => Term.delta_ne_pattern2 _ _ _ heq.symm
  case threeA => exact fun heq => Term.delta_ne_pattern3a _ _ _ heq.symm
  case threeB => exact fun heq => Term.delta_ne_pattern3b _ _ _ _ heq.symm
  case threeC => exact fun heq => Term.delta_ne_pattern3c _ _ _ _ _ heq.symm





-- Helper lemmas to show Δ⬝x doesn't match any rewrite rule patterns
-- Δ⬝x unfolds to Term.term [x], which has a singleton list
theorem Term.stem_ne_pattern1 : ∀ x y z, Δ⬝x ≠ Δ⬝Δ⬝y⬝z := by
  intro x y z heq
  simp only [Term.cons] at heq
  cases z; rename_i zs
  cases x; rename_i xs
  cases y; rename_i ys
  injection heq with h_list
  injection h_list with h_head h_tail
  subst h_tail
  injection h_head with h_inner
  cases xs
  · exact List.noConfusion h_inner
  · exact List.noConfusion h_inner

theorem Term.stem_ne_pattern2 : ∀ x x' y z, Δ⬝x ≠ Δ⬝(Δ⬝x')⬝y⬝z := by
  intro x x' y z heq
  simp only [Term.cons] at heq
  cases z; rename_i zs
  cases x; rename_i xs
  cases y; rename_i ys
  cases x'; rename_i x's
  injection heq with h_list
  injection h_list with h_head h_tail
  subst h_tail
  injection h_head with h_inner
  cases xs
  · exact List.noConfusion h_inner
  · exact List.noConfusion h_inner

theorem Term.stem_ne_pattern3a : ∀ x w x' y, Δ⬝x ≠ Δ⬝(Δ⬝w⬝x')⬝y⬝Δ := by
  intro x w x' y heq
  simp only [Term.cons] at heq
  cases x; rename_i xs
  cases y; rename_i ys
  cases x'; rename_i x's
  cases w; rename_i ws
  injection heq with h_list
  injection h_list with h_head h_tail
  simp at h_head

theorem Term.stem_ne_pattern3b : ∀ x w x' y u, Δ⬝x ≠ Δ⬝(Δ⬝w⬝x')⬝y⬝(Δ⬝u) := by
  intro x w x' y u heq
  simp only [Term.cons] at heq
  cases u; rename_i us
  cases x; rename_i xs
  cases y; rename_i ys
  cases x'; rename_i x's
  cases w; rename_i ws
  injection heq with h_list
  injection h_list with h_head h_tail
  cases us; subst h_tail
  simp at h_head
  injection h_head with h_inner
  exact List.noConfusion h_inner

theorem Term.stem_ne_pattern3c : ∀ x w x' y u v, Δ⬝x ≠ Δ⬝(Δ⬝w⬝x')⬝y⬝(Δ⬝u⬝v) := by
  intro x w x' y u v heq
  simp only [Term.cons] at heq
  cases v; rename_i vs
  cases x; rename_i xs
  cases y; rename_i ys
  cases x'; rename_i x's
  cases w; rename_i ws
  injection heq with h_list
  injection h_list with h_head h_tail
  cases vs; subst h_tail
  simp at h_head
  injection h_head with h_inner
  exact List.noConfusion h_inner

@[grind]
theorem RewriteRules.stem_irreducible (t : Term) (h : t.IsStem) : t.IsNotRewritable := by
  simp [Term.IsStem] at h
  obtain ⟨x, rfl⟩ := h
  intro output prem
  refine @RewriteRules.rec (fun input _ _ => input = Δ⬝x → False) ?one ?two ?threeA ?threeB ?threeC (Δ⬝x) output prem rfl
  case one => exact fun heq => Term.stem_ne_pattern1 _ _ _ heq.symm
  case two => exact fun heq => Term.stem_ne_pattern2 _ _ _ _ heq.symm
  case threeA => exact fun heq => Term.stem_ne_pattern3a _ _ _ _ heq.symm
  case threeB => exact fun heq => Term.stem_ne_pattern3b _ _ _ _ _ heq.symm
  case threeC => exact fun heq => Term.stem_ne_pattern3c _ _ _ _ _ _ heq.symm

-- Helper lemmas to show Δ⬝x⬝y doesn't match any rewrite rule patterns
-- Δ⬝x⬝y unfolds to Term.term [x, y], which has a two-element list
theorem Term.fork_ne_pattern1 : ∀ x y y' z, Δ⬝x⬝y ≠ Δ⬝Δ⬝y'⬝z := by
  intro x y y' z heq
  simp only [Term.cons] at heq
  cases z; rename_i zs
  cases y; rename_i ys
  cases x; rename_i xs
  cases y'; rename_i y's
  injection heq with h_list
  simp at h_list

theorem Term.fork_ne_pattern2 : ∀ x y x' y' z, Δ⬝x⬝y ≠ Δ⬝(Δ⬝x')⬝y'⬝z := by
  intro x y x' y' z heq
  simp only [Term.cons] at heq
  cases z; rename_i zs
  cases y; rename_i ys
  cases x; rename_i xs
  cases y'; rename_i y's
  cases x'; rename_i x's
  injection heq with h_list
  simp at h_list

theorem Term.fork_ne_pattern3a : ∀ x y w x' y', Δ⬝x⬝y ≠ Δ⬝(Δ⬝w⬝x')⬝y'⬝Δ := by
  intro x y w x' y' heq
  simp only [Term.cons] at heq
  cases y; rename_i ys
  cases x; rename_i xs
  cases y'; rename_i y's
  cases x'; rename_i x's
  cases w; rename_i ws
  injection heq with h_list
  simp at h_list

theorem Term.fork_ne_pattern3b : ∀ x y w x' y' u, Δ⬝x⬝y ≠ Δ⬝(Δ⬝w⬝x')⬝y'⬝(Δ⬝u) := by
  intro x y w x' y' u heq
  simp only [Term.cons] at heq
  cases u; rename_i us
  cases y; rename_i ys
  cases x; rename_i xs
  cases y'; rename_i y's
  cases x'; rename_i x's
  cases w; rename_i ws
  injection heq with h_list
  simp at h_list

theorem Term.fork_ne_pattern3c : ∀ x y w x' y' u v, Δ⬝x⬝y ≠ Δ⬝(Δ⬝w⬝x')⬝y'⬝(Δ⬝u⬝v) := by
  intro x y w x' y' u v heq
  simp only [Term.cons] at heq
  cases v; rename_i vs
  cases y; rename_i ys
  cases x; rename_i xs
  cases y'; rename_i y's
  cases x'; rename_i x's
  cases w; rename_i ws
  injection heq with h_list
  simp at h_list

@[grind]
theorem RewriteRules.fork_irreducible (t : Term) (h : t.IsFork) : t.IsNotRewritable := by
  simp [Term.IsFork] at h
  obtain ⟨x, y, rfl⟩ := h
  intro output prem
  refine @RewriteRules.rec (fun input _ _ => input = Δ⬝x⬝y → False) ?one ?two ?threeA ?threeB ?threeC (Δ⬝x⬝y) output prem rfl
  case one => exact fun heq => Term.fork_ne_pattern1 _ _ _ _ heq.symm
  case two => exact fun heq => Term.fork_ne_pattern2 _ _ _ _ _ heq.symm
  case threeA => exact fun heq => Term.fork_ne_pattern3a _ _ _ _ _ heq.symm
  case threeB => exact fun heq => Term.fork_ne_pattern3b _ _ _ _ _ _ heq.symm
  case threeC => exact fun heq => Term.fork_ne_pattern3c _ _ _ _ _ _ _ heq.symm











-- Helper: try to apply a rewrite rule to exactly 4 terms
@[reducible,simp]
def tryRewrite (t1 t2 t3 t4 : Term) : Option Term :=
  match t1, t2, t3, t4 with
  -- Rule one: Δ⬝Δ⬝y⬝z → y
  | Δ, Δ, y, _z => some y

  -- Rule two: Δ⬝(Δ⬝x)⬝y⬝z → x⬝z⬝(y⬝z)
  | Δ, .term [x], _y, z => some (Term.term [x, z, Term.term [_y, z]])

  -- Rule threeA: Δ⬝(Δ⬝w⬝x)⬝y⬝Δ → w
  | Δ, .term [w, _x], _y, Δ => some w

  -- Rule threeB: Δ⬝(Δ⬝w⬝x)⬝y⬝(Δ⬝u) → x⬝u
  | Δ, .term [_w, x], _y, .term [u] => some (Term.term [x, u])

  -- Rule threeC: Δ⬝(Δ⬝w⬝x)⬝y⬝(Δ⬝u⬝v) → y⬝u⬝v
  | Δ, .term [_w, _x], y, .term [u, v] => some (Term.term [y, u, v])

  | .term (.cons _ _), _, _, _ => none
  -- | _ => none
  | (Term.term []), (Term.term (List.cons _ (List.cons _ (List.cons _ _)))), _, _ => none
  | (Term.term []), (Term.term (List.cons _ (List.cons _ []))), _, (Term.term (List.cons _ (List.cons _ (List.cons _ _)))) => none




theorem tryRewrite.some_iff_rewritable : tryRewrite t1 t2 t3 t4 = none ↔ ∀ output, ¬RewriteRules (.term [t1,t2,t3,t4]) output := by
  constructor
  · intro prem output
    -- set term := Term.term [t1,t2,t3,t4] with h
    fun_cases tryRewrite t1 t2 t3 t4
    · simp only [tryRewrite, reduceCtorEq] at prem
    · simp at prem
    · simp at prem
    · simp at prem
    · simp at prem
    · intro contra
    · simp at prem
    · simp at prem
  sorry


-- Mutual recursion: reduce and reduceList
-- TODO: Add termination proof showing that rewriting always produces a smaller term
mutual
  -- Helper: reduce a list of terms element-wise
  def reduceList (terms : List Term) : List Term :=
    terms.map Term.reduce

  -- Full reduction step
  def Term.reduce (term : Term) : Term :=
    match term with
    | Δ =>
      -- Leaf: return as-is (irreducible)
      Δ

    | .term terms =>
      match terms with
      | [] => Δ  -- Should be unreachable, but for completeness
      | [t] => Term.term [t.reduce]
      | [t1, t2] => Term.term [t1.reduce, t2.reduce]
      | [t1, t2, t3] => Term.term [t1.reduce, t2.reduce, t3.reduce]
      | t1 :: t2 :: t3 :: t4 :: rest =>
        -- List has ≥4 items
        -- Step 1: Recursively reduce the first 4 items
        let r1 := t1.reduce
        let r2 := t2.reduce
        let r3 := t3.reduce
        let r4 := t4.reduce

        -- Step 2: Try to apply a rewrite rule to the 4 reduced items
        match tryRewrite r1 r2 r3 r4 with
        | some result =>
          -- Step 3: Extract the list from the result and prepend to rest
          match result with
          | Term.term resultList =>
            let newList := resultList ++ rest
            -- Step 4: If new list has ≥4 items, recurse; otherwise reduce each item
            if newList.length < 4 then
              Term.term (reduceList newList)
            else
              (Term.term newList).reduce
        | none =>
          -- No rule matched - this shouldn't happen if all 4 are properly reduced
          -- For now, just return the reduced items plus recursively reduced rest
          Term.term (r1 :: r2 :: r3 :: r4 :: reduceList rest)
end



-- Note: Not ALL terms of the form Δ⬝x⬝y⬝z are reducible - it depends on x's structure
-- This is just an example showing that SOME such terms reduce
theorem RewriteRules.redex_one_reducible : Term.IsRewritable (Δ⬝Δ⬝y⬝z) := by
  simp [Term.IsRewritable]
  exact ⟨y, RewriteRules.one⟩




-- Reflexive transitive closure of the rewrite relation
inductive RewriteRules.ReflTransClosure : Term → Term → Prop where
  | refl {t : Term} :
      RewriteRules.ReflTransClosure t t
  | step {t t' t'' : Term} :
      RewriteRules t t' →
      RewriteRules.ReflTransClosure t' t'' →
      RewriteRules.ReflTransClosure t t''

-- Notation: t ⟶* t' means "t reduces to t' in zero or more steps"
infixl:50 " ⟶* " => RewriteRules.ReflTransClosure

-- Confluence (Church-Rosser property):
-- If t reduces to both t1 and t2, then there exists t3 that both can reduce to
theorem confluence :
    ∀ {t t1 t2 : Term},
      t ⟶* t1 →
      t ⟶* t2 →
      ∃ t3, t1 ⟶* t3 ∧ t2 ⟶* t3 := by
  sorry


-- Intensionality: The calculus can distinguish between different kinds of values

-- Every irreducible term is exactly one of these three kinds
theorem value_classification :
    ∀ (t : Term), t.IsNotRewritable ↔ (t.IsLeaf ∨ t.IsStem ∨ t.IsFork) := by
  sorry

-- The "case" combinator: Δ (Δ w x) y can distinguish between the three kinds
-- of values and compute different results for each
def case_combinator (w x y : Term) : Term := Δ⬝(Δ⬝w⬝x)⬝y

theorem case_on_leaf :
    ∀ w x y, case_combinator w x y ⬝ Δ ⟶* w := by
  sorry

theorem case_on_stem :
    ∀ w x y u, (case_combinator w x y ⬝ (Δ⬝u)) ⟶* (x⬝u) := by
  sorry

theorem case_on_fork :
    ∀ w x y u v, (case_combinator w x y ⬝ (Δ⬝u⬝v)) ⟶* (y⬝u⬝v) := by
  sorry

-- This demonstrates intensionality: we can write a program (case_combinator)
-- that inspects the structure of a value and computes different things
-- based on whether it's a leaf, stem, or fork
