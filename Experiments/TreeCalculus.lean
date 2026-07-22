import Mathlib.Tactic.Tauto
import Mathlib.Logic.Relation

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
  -- induction h₁ generalizing c with
  -- | refl =>
  --   exists c
  --   simp [*]
  --   refine .refl
  -- | tail h r ih =>
  --   expose_names
  --   have ⟨d,prf⟩ := ih h₂
  --   refine ⟨d,?_,prf.right⟩
  --   have : MultiStepReduction a c_1 := ?_

  --   exact ih this |>.left

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


@[grind]
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



/-- Spec application: attach `arg` as the rightmost child of `fn`'s root.
Application itself is left-associative; “to the right” means where the child
hangs on the tree, i.e. `children ++ [arg]`. -/
@[reducible, grind]
def Term.apply (fn arg : Term) : Term :=
  match fn with
  | .term cs => .term (cs ++ [arg])

@[match_pattern]
notation "△" => Term.term []

@[inherit_doc, match_pattern] infixl:67 " ⬝ " => Term.apply

def x := △
def y := △
def z := △
def u := △
def v := △

/-! ### Spec multi-child shapes via `⬝`

In the multi-child reading, `△ a b c` is a node whose children are `[a, b, c]`
(the leading `△` *is* the node, not a child). So:
- leaf: `△` = `term []`
- stem `a`: `△ a` = `term [a]`
- fork `a b`: `△ a b` = `term [a, b]`
- redex `a b c`: `△ a b c` = `term [a, b, c]`

Rule 1 shape `△ △ y z` = `term [△, y, z]`. -/

#guard decide (△ ⬝ △ = Term.term [△])
#guard decide (△ ⬝ △ ⬝ y = Term.term [△, y])
#guard decide (△ ⬝ △ ⬝ y ⬝ z = Term.term [△, y, z])
-- Rule 2: △ (△ x) y z
#guard decide (△ ⬝ (△ ⬝ x) ⬝ y ⬝ z = Term.term [△ ⬝ x, y, z])
-- Rule 3a: △ (△ w x) y △
#guard decide (△ ⬝ (△ ⬝ △ ⬝ △) ⬝ y ⬝ △ = Term.term [△ ⬝ △ ⬝ △, y, △])
-- Rule 3b/3c argument shapes
#guard decide (△ ⬝ u = Term.term [u])
#guard decide (△ ⬝ u ⬝ v = Term.term [u, v])

#eval △ ⬝ △ ⬝ y ⬝ z
#eval (△ ⬝ △ ⬝ ((△ ⬝ △) ⬝ x ⬝ (y ⬝ z)))

@[grind cases]
inductive RewriteRules : (input output : Term) → Prop where
  | one {y z : Term} :
    RewriteRules (△⬝△⬝y⬝z)
      y

  | two {x y z : Term} :
    RewriteRules (△⬝(△⬝x)⬝y⬝z)
      (x⬝z⬝(y⬝z))

  | threeA {w x y : Term} :
    RewriteRules (△⬝(△⬝w⬝x)⬝y⬝△)
      w

  | threeB {w x y u : Term} :
    RewriteRules (△⬝(△⬝w⬝x)⬝y⬝(△⬝u))
      (x⬝u)

  | threeC {w x y u v : Term} :
    RewriteRules (△⬝(△⬝w⬝x)⬝y⬝(△⬝u⬝v))
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

/-- `t` diverges if every multi-step reduct is still one-step reducible.
I.e. there is an infinite reduction sequence from `t`. -/
def Term.Diverges (t : Term) : Prop :=
  ∀ u, Relation.ReflTransGen Reduces t u → ∃ v, Reduces u v

/-! Not strongly normalizing: some terms diverge.

Intended witness (combinatory Ω):
  `I = △ ⬝ (△ ⬝ (△ ⬝ △)) ⬝ (△ ⬝ △)` (≈ S K K)
  `ω = △ ⬝ (△ ⬝ I) ⬝ I` (≈ S I I)
  `Ω = ω ⬝ ω`
Rule 2 (S-like duplication) keeps feeding fresh redexes, so reduction never
reaches a normal form. -/

/-- Combinator `I` ≈ `S K K`. -/
def combI : Term := △ ⬝ (△ ⬝ (△ ⬝ △)) ⬝ (△ ⬝ △)

/-- Combinator `ω` ≈ `S I I`. -/
def combω : Term := △ ⬝ (△ ⬝ combI) ⬝ combI

/-- Combinator `Ω` ≈ `ω ω`. -/
def combΩ : Term := combω ⬝ combω

/-- A term is in normal form when it is a leaf, stem, or fork built from normal subterms. -/
inductive Term.NormalForm : Term → Prop where
  | leaf : Term.NormalForm △
  | stem (a : Term) : Term.NormalForm a → Term.NormalForm (△ ⬝ a)
  | fork (a b : Term) : Term.NormalForm a → Term.NormalForm b → Term.NormalForm (△ ⬝ a ⬝ b)









/-- This term is rewritable. I.e. it is not a "value" but a "program" -/
@[simp,grind]
def Term.IsRewritable (term : Term) := ∃ output, RewriteRules term output

/-- Is not rewritable – but can still be *reducible* if its subterms can be reduced! -/
@[simp,grind]
def Term.IsNotRewritable (term : Term) := ∀ output, ¬RewriteRules term output


-- Values (irreducible terms) are exactly: leafs, stems, and forks
@[simp,grind]
def Term.IsLeaf (t : Term) : Prop := t = △
@[simp,grind]
def Term.IsStem (t : Term) : Prop := ∃ a, t = (△⬝a)
@[simp,grind]
def Term.IsFork (t : Term) : Prop := ∃ a b, t = (△⬝a⬝b)




-- Leaf/stem/fork are not rewrite-rule redexes (arity mismatch; `cases` on RewriteRules).

@[grind]
theorem RewriteRules.leaf_irreducible (t : Term) (h : t.IsLeaf) : t.IsNotRewritable := by
  simp [Term.IsLeaf] at h
  subst h
  intro output prem
  cases prem

@[grind]
theorem RewriteRules.stem_irreducible (t : Term) (h : t.IsStem) : t.IsNotRewritable := by
  simp [Term.IsStem] at h
  obtain ⟨x, rfl⟩ := h
  intro output prem
  cases prem

@[grind]
theorem RewriteRules.fork_irreducible (t : Term) (h : t.IsFork) : t.IsNotRewritable := by
  simp [Term.IsFork] at h
  obtain ⟨x, y, rfl⟩ := h
  intro output prem
  cases prem

/-! ### Divergence of `combΩ`

@TODO Proof strategy (restart — avoid general ΩArg/ΩReduct algebras):
1. Keep/use the small helpers below (`numChildren*`, apply-eq, `combI`/`combω` NF, …).
2. Progress: `∀ t, ¬ NormalForm t → ∃ v, Reduces t v` (arity / sizeOf; fire rewrite or congr).
3. Invariant on *top-level shapes only* reachable from `combΩ`
   (e.g. finite grammar: `ω ⬝ t` with `t` from a small arg set, plus length-≥4 apps;
   or weaker: length ≥ 3 and never a top-level K-redex). Prove closed under `Reduces`
   by case-bash on that grammar — do **not** invent a general “good subterm” predicate.
4. Conclude every reduct is non-NF, hence `Diverges combΩ`.

Do **not** rename the demo globals `x,y,z,u,v` — if binders clash, rename
locals in the theorem or use `@RewriteRules.two _ _ _`. -/

theorem Term.NormalForm.not_three_children {a b c : Term} :
    ¬ Term.NormalForm (△ ⬝ a ⬝ b ⬝ c) := by
  intro h
  cases h

theorem Term.combΩ_not_normalForm : ¬ Term.NormalForm combΩ := by
  intro h
  change Term.NormalForm (△ ⬝ (△ ⬝ combI) ⬝ combI ⬝ combω) at h
  exact Term.NormalForm.not_three_children h

theorem Reduces.combΩ_step :
    Reduces combΩ (combI ⬝ combω ⬝ (combI ⬝ combω)) := by
  unfold combΩ combω
  exact Reduces.rule (@RewriteRules.two combI combI combω)

/-! #### Helpers kept from prior attempt -/

def Term.numChildren : Term → Nat
  | .term cs => cs.length

@[simp] theorem Term.numChildren_apply (t1 t2 : Term) :
    (t1 ⬝ t2).numChildren = t1.numChildren + 1 := by
  cases t1; simp [Term.numChildren]

theorem Term.foldl_apply (t : Term) (cs : List Term) :
    cs.foldl (· ⬝ ·) t = match t with | .term ts => .term (ts ++ cs) := by
  induction cs generalizing t with
  | nil => cases t; simp
  | cons a as ih =>
    cases t with | term ts
    simp only [List.foldl, Term.apply]
    rw [ih]
    simp [List.append_assoc]

theorem Term.term_eq_foldl (cs : List Term) :
    Term.term cs = cs.foldl (· ⬝ ·) △ := by
  rw [Term.foldl_apply]; simp

theorem Reduces.congr_foldl {t t' : Term} (args : List Term) (h : Reduces t t') :
    Reduces (args.foldl (· ⬝ ·) t) (args.foldl (· ⬝ ·) t') := by
  induction args generalizing t t' with
  | nil => exact h
  | cons a as ih => exact ih (Reduces.congr_left h)

theorem Term.NormalForm.numChildren_le_two {t : Term} (h : t.NormalForm) :
    t.numChildren ≤ 2 := by
  cases h with
  | leaf => simp [Term.numChildren]
  | stem => simp [Term.numChildren]
  | fork => simp [Term.numChildren]

theorem Term.not_normalForm_of_numChildren_ge_three {t : Term}
    (h : t.numChildren ≥ 3) : ¬ t.NormalForm := by
  intro hnf
  have := hnf.numChildren_le_two
  omega

theorem Term.apply_ne_delta (fn arg : Term) : fn ⬝ arg ≠ △ := by
  cases fn with | term cs
  simp [Term.apply]

theorem Term.eq_stem_of_apply {t1 t2 a : Term} (h : t1 ⬝ t2 = △ ⬝ a) :
    t1 = △ ∧ t2 = a := by
  cases t1 with | term cs
  simp [Term.apply] at h
  match cs with
  | [] =>
    simp at h
    exact ⟨rfl, h⟩
  | head :: tail =>
    have hlen := congrArg List.length h
    simp at hlen

theorem Term.eq_fork_of_apply {t1 t2 a b : Term} (h : t1 ⬝ t2 = △ ⬝ a ⬝ b) :
    t1 = △ ⬝ a ∧ t2 = b := by
  cases t1 with | term cs
  simp [Term.apply] at h
  match cs with
  | [] => simp at h
  | [x] =>
    simp at h
    refine ⟨?_, h.2⟩
    simp [Term.apply, h.1]
  | x :: y :: zs =>
    have hlen := congrArg List.length h
    simp at hlen

/-- Combinator `I` is a normal form. -/
theorem combI_normalForm : Term.NormalForm combI := by
  unfold combI
  refine Term.NormalForm.fork _ _ ?_ ?_
  · exact Term.NormalForm.stem _ (Term.NormalForm.stem _ Term.NormalForm.leaf)
  · exact Term.NormalForm.stem _ Term.NormalForm.leaf

/-- Combinator `ω` is a normal form. -/
theorem combω_normalForm : Term.NormalForm combω := by
  unfold combω
  exact Term.NormalForm.fork _ _ (Term.NormalForm.stem _ combI_normalForm) combI_normalForm

/-! #### Progress: non-NF terms have a one-step reduct -/

/-- Explicit weight: nested `sizeOf` on `Term`/`List` is awkward for `omega`. -/
def Term.weight : Term → Nat
  | .term cs => 1 + (cs.map weight).sum

theorem Term.weight_lt_of_mem {a : Term} {cs : List Term} (h : a ∈ cs) :
    a.weight < (Term.term cs).weight := by
  induction cs with
  | nil => cases h
  | cons b bs ih =>
    simp [Term.weight] at *
    cases h with
    | inl heq => subst heq; omega
    | inr hmem =>
      have := ih hmem
      simp at this ⊢
      omega

/-- Avoid dependent elim on `NormalForm (t1 ⬝ t2)` by expanding to equalities. -/
theorem Term.NormalForm.as_cases {t : Term} (h : t.NormalForm) :
    t = △ ∨
    (∃ a, t = △ ⬝ a ∧ a.NormalForm) ∨
    (∃ a b, t = △ ⬝ a ⬝ b ∧ a.NormalForm ∧ b.NormalForm) := by
  cases h with
  | leaf => exact Or.inl rfl
  | stem a ha => exact Or.inr (Or.inl ⟨a, rfl, ha⟩)
  | fork a b ha hb => exact Or.inr (Or.inr ⟨a, b, rfl, ha, hb⟩)

theorem RewriteRules.numChildren_eq_three {t t' : Term}
    (h : RewriteRules t t') : t.numChildren = 3 := by
  cases h <;> simp [Term.numChildren, Term.apply]

theorem Term.reduces_not_of_normalForm {t t' : Term}
    (hr : Reduces t t') (hnf : t.NormalForm) : False := by
  induction hr with
  | rule r =>
    have hlen := RewriteRules.numChildren_eq_three r
    exact Term.not_normalForm_of_numChildren_ge_three (by omega) hnf
  | congr_left hr ih =>
    expose_names
    obtain h | h | h := Term.NormalForm.as_cases hnf
    · exact (Term.apply_ne_delta t1 t2).elim h
    · obtain ⟨a, heq, ha⟩ := h
      obtain ⟨rfl, rfl⟩ := Term.eq_stem_of_apply heq
      exact ih Term.NormalForm.leaf
    · obtain ⟨a, b, heq, ha, hb⟩ := h
      obtain ⟨rfl, rfl⟩ := Term.eq_fork_of_apply heq
      exact ih (Term.NormalForm.stem a ha)
  | congr_right hr ih =>
    expose_names
    obtain h | h | h := Term.NormalForm.as_cases hnf
    · exact (Term.apply_ne_delta t1 t2).elim h
    · obtain ⟨a, heq, ha⟩ := h
      obtain ⟨rfl, rfl⟩ := Term.eq_stem_of_apply heq
      exact ih ha
    · obtain ⟨a, b, heq, ha, hb⟩ := h
      obtain ⟨rfl, rfl⟩ := Term.eq_fork_of_apply heq
      exact ih hb

theorem Term.NormalForm.irreducible {t : Term} (h : t.NormalForm) :
    ∀ t', ¬ Reduces t t' := fun _ hr => Term.reduces_not_of_normalForm hr h

/-- Fire the matching rewrite on a length-3 term whose first child is a value. -/
theorem Term.exists_reduces_of_three {a b c : Term}
    (ha : a.numChildren ≤ 2)
    (hc : c.numChildren ≤ 2 ∨ a.numChildren ≤ 1) :
    ∃ t', Reduces (△ ⬝ a ⬝ b ⬝ c) t' := by
  -- Case-split on the shape of `a` (leaf / stem / fork).
  cases a with | term as
  match as with
  | [] =>
    exact ⟨b, Reduces.rule (@RewriteRules.one b c)⟩
  | [x] =>
    exact ⟨x ⬝ c ⬝ (b ⬝ c), Reduces.rule (@RewriteRules.two x b c)⟩
  | [w, x] =>
    -- Need `c` to be leaf/stem/fork for rules 3a–c.
    have hc' : c.numChildren ≤ 2 := by
      cases hc with
      | inl h => exact h
      | inr h => simp [Term.numChildren] at h
    cases c with | term cs
    match cs with
    | [] =>
      exact ⟨w, Reduces.rule (@RewriteRules.threeA w x b)⟩
    | [u] =>
      exact ⟨x ⬝ u, Reduces.rule (@RewriteRules.threeB w x b u)⟩
    | [u, v] =>
      exact ⟨b ⬝ u ⬝ v, Reduces.rule (@RewriteRules.threeC w x b u v)⟩
    | _ :: _ :: _ :: _ =>
      simp [Term.numChildren] at hc'
  | _ :: _ :: _ :: _ =>
    simp [Term.numChildren] at ha

/-- Progress: every non-normal form has a one-step reduct. -/
theorem Term.progress {t : Term} (h : ¬ t.NormalForm) : ∃ t', Reduces t t' := by
  have helper : ∀ n, ∀ t, t.weight = n → ¬ t.NormalForm → ∃ t', Reduces t t' := by
    intro n
    refine Nat.strongRecOn n fun n ih t hsz hnf => ?_
    cases t with | term cs
    match cs with
    | [] => exact (hnf Term.NormalForm.leaf).elim
    | [a] =>
      have ha : ¬ a.NormalForm := fun ha => hnf (Term.NormalForm.stem a ha)
      have hwt : a.weight < n := by
        subst hsz
        exact Term.weight_lt_of_mem (by simp)
      obtain ⟨a', hr⟩ := ih a.weight hwt a rfl ha
      refine ⟨△ ⬝ a', ?_⟩
      simpa [Term.apply] using Reduces.congr_right (t1 := △) hr
    | [a, b] =>
      by_cases ha : a.NormalForm
      · by_cases hb : b.NormalForm
        · exact (hnf (Term.NormalForm.fork a b ha hb)).elim
        · have hwt : b.weight < n := by
            subst hsz
            exact Term.weight_lt_of_mem (by simp)
          obtain ⟨b', hr⟩ := ih b.weight hwt b rfl hb
          refine ⟨△ ⬝ a ⬝ b', ?_⟩
          simpa [Term.apply] using
            Reduces.congr_right (t1 := △ ⬝ a) hr
      · have hwt : a.weight < n := by
          subst hsz
          exact Term.weight_lt_of_mem (by simp)
        obtain ⟨a', hr⟩ := ih a.weight hwt a rfl ha
        refine ⟨△ ⬝ a' ⬝ b, ?_⟩
        have hr' : Reduces (△ ⬝ a) (△ ⬝ a') := Reduces.congr_right (t1 := △) hr
        simpa [Term.apply] using Reduces.congr_left (t2 := b) hr'
    | a :: b :: c :: rest =>
      let t3 : Term := △ ⬝ a ⬝ b ⬝ c
      have ht : Term.term (a :: b :: c :: rest) =
          rest.foldl (· ⬝ ·) t3 := by
        simp [t3, Term.foldl_apply, Term.apply]
      by_cases ha : a.NormalForm
      · by_cases hc : c.NormalForm
        · have ha_len := ha.numChildren_le_two
          have hc_len := hc.numChildren_le_two
          obtain ⟨t3', hr3⟩ := Term.exists_reduces_of_three (a := a) (b := b) (c := c)
            ha_len (Or.inl hc_len)
          refine ⟨rest.foldl (· ⬝ ·) t3', ?_⟩
          rw [ht]
          exact Reduces.congr_foldl rest hr3
        · have hwt : c.weight < n := by
            subst hsz
            exact Term.weight_lt_of_mem (by simp)
          obtain ⟨c', hr⟩ := ih c.weight hwt c rfl hc
          have hr3 : Reduces (△ ⬝ a ⬝ b ⬝ c) (△ ⬝ a ⬝ b ⬝ c') := by
            simpa [Term.apply] using
              Reduces.congr_right (t1 := △ ⬝ a ⬝ b) hr
          refine ⟨rest.foldl (· ⬝ ·) (△ ⬝ a ⬝ b ⬝ c'), ?_⟩
          rw [ht]
          exact Reduces.congr_foldl rest hr3
      · have hwt : a.weight < n := by
          subst hsz
          exact Term.weight_lt_of_mem (by simp)
        obtain ⟨a', hr⟩ := ih a.weight hwt a rfl ha
        have hr3 : Reduces (△ ⬝ a ⬝ b ⬝ c) (△ ⬝ a' ⬝ b ⬝ c) := by
          have h1 : Reduces (△ ⬝ a) (△ ⬝ a') := Reduces.congr_right (t1 := △) hr
          have h2 : Reduces (△ ⬝ a ⬝ b) (△ ⬝ a' ⬝ b) :=
            Reduces.congr_left (t2 := b) h1
          simpa [Term.apply] using Reduces.congr_left (t2 := c) h2
        refine ⟨rest.foldl (· ⬝ ·) (△ ⬝ a' ⬝ b ⬝ c), ?_⟩
        rw [ht]
        exact Reduces.congr_foldl rest hr3
  exact helper t.weight t rfl h

/-! #### Top-level shape invariant for `combΩ` reducts

Spine grammar (not a general “good child” algebra):
* `ΩArg`: `combω`, or `combI ⬝ a`, or a (possibly mismatched) K-redex body
* `ΩForm`: `combω ⬝ a`, `combI ⬝ a ⬝ b`, or K-prefix applied to one more arg -/

mutual
inductive Term.ΩArg : Term → Prop where
  | ω : Term.ΩArg combω
  | I {a : Term} : Term.ΩArg a → Term.ΩArg (combI ⬝ a)
  | K {a b : Term} : Term.ΩArg a → Term.ΩArg b →
      Term.ΩArg ((△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b))

inductive Term.ΩForm : Term → Prop where
  | ωapp {a : Term} : Term.ΩArg a → Term.ΩForm (combω ⬝ a)
  | Iapp {a b : Term} : Term.ΩArg a → Term.ΩArg b → Term.ΩForm (combI ⬝ a ⬝ b)
  | Kapp {a b c : Term} : Term.ΩArg a → Term.ΩArg b → Term.ΩArg c →
      Term.ΩForm ((△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b) ⬝ c)
end

theorem Term.ΩForm.combΩ : Term.ΩForm combΩ :=
  .ωapp .ω

theorem Term.ΩArg.numChildren_ge_two {t : Term} (h : t.ΩArg) :
    t.numChildren ≥ 2 := by
  cases h with
  | ω => simp [combω, Term.numChildren, Term.apply]
  | I => simp [combI, Term.numChildren, Term.apply]
  | K => simp [Term.numChildren, Term.apply]

theorem Term.ΩForm.numChildren_ge_three {t : Term} (h : t.ΩForm) :
    t.numChildren ≥ 3 := by
  cases h with
  | ωapp => simp [combω, Term.numChildren, Term.apply]
  | Iapp => simp [combI, Term.numChildren, Term.apply]
  | Kapp => simp [Term.numChildren, Term.apply]

theorem Term.ΩForm.not_normalForm {t : Term} (h : t.ΩForm) : ¬ t.NormalForm :=
  Term.not_normalForm_of_numChildren_ge_three h.numChildren_ge_three

/-- Applying an `ΩArg` to an `ΩArg` yields an `ΩForm`. -/
theorem Term.ΩArg.apply_ΩArg {a c : Term} (ha : a.ΩArg) (hc : c.ΩArg) :
    (a ⬝ c).ΩForm := by
  cases ha with
  | ω => exact .ωapp hc
  | I ha => exact .Iapp ha hc
  | K ha hb => exact .Kapp ha hb hc

theorem Term.apply_inj {fn1 arg1 fn2 arg2 : Term}
    (h : fn1 ⬝ arg1 = fn2 ⬝ arg2) : fn1 = fn2 ∧ arg1 = arg2 := by
  cases fn1 with | term cs1
  cases fn2 with | term cs2
  simp [Term.apply] at h
  exact ⟨congrArg Term.term h.1, h.2⟩

/-- One-step reducts of `combI ⬝ a`. -/
theorem Term.reduces_combI_app {a t' : Term} (hr : Reduces (combI ⬝ a) t') :
    t' = (△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ a) ∨
    (∃ a', Reduces a a' ∧ t' = combI ⬝ a') := by
  change Reduces (△ ⬝ (△ ⬝ (△ ⬝ △)) ⬝ (△ ⬝ △) ⬝ a) t' at hr
  generalize ht : (△ ⬝ (△ ⬝ (△ ⬝ △)) ⬝ (△ ⬝ △) ⬝ a : Term) = t at hr
  induction hr generalizing a with
  | rule r =>
    cases r with
    | two =>
      -- Unify via ht
      injection ht with ht'
      simp [Term.apply] at ht'
      obtain ⟨h1, h2, h3⟩ := ht'
      -- h1 : △ ⬝ △ = xx (as lists), h2 : △ ⬝ △ = yy, h3 : a = zz
      subst h1; subst h2; subst h3
      exact Or.inl rfl
    | one =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeA =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeB =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeC =>
      injection ht with ht'
      simp [Term.apply] at ht'
  | congr_left hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    -- Left is △ ⬝ (△ ⬝ (△ ⬝ △)) ⬝ (△ ⬝ △) = combI, NF
    exact (combI_normalForm.irreducible _ hr).elim
  | congr_right hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    exact Or.inr ⟨t2', hr, by simp [combI, Term.apply]⟩

/-- One-step reducts of `(△ ⬝ △) ⬝ a` (always via reducing `a`). -/
theorem Term.reduces_delta_delta_app {a t' : Term}
    (hr : Reduces ((△ ⬝ △) ⬝ a) t') :
    ∃ a', Reduces a a' ∧ t' = (△ ⬝ △) ⬝ a' := by
  change Reduces (△ ⬝ △ ⬝ a) t' at hr
  generalize ht : (△ ⬝ △ ⬝ a : Term) = t at hr
  induction hr generalizing a with
  | rule r =>
    cases r with
    | one =>
      injection ht with ht'
      simp at ht'
    | two =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeA =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeB =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeC =>
      injection ht with ht'
      simp [Term.apply] at ht'
  | congr_left hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    have hnf : Term.NormalForm (△ ⬝ △) :=
      Term.NormalForm.stem _ Term.NormalForm.leaf
    exact (hnf.irreducible _ hr).elim
  | congr_right hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    exact ⟨t2', hr, rfl⟩

/-- One-step reducts of a K-body `(△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b)`. -/
theorem Term.reduces_K_body {a b t' : Term}
    (hr : Reduces ((△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b)) t') :
    t' = a ∨
    (∃ a', Reduces a a' ∧ t' = (△ ⬝ △) ⬝ a' ⬝ ((△ ⬝ △) ⬝ b)) ∨
    (∃ b', Reduces b b' ∧ t' = (△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b')) := by
  change Reduces (△ ⬝ △ ⬝ a ⬝ ((△ ⬝ △) ⬝ b)) t' at hr
  generalize ht : (△ ⬝ △ ⬝ a ⬝ ((△ ⬝ △) ⬝ b) : Term) = t at hr
  induction hr generalizing a b with
  | rule r =>
    cases r with
    | one =>
      injection ht with ht'
      simp [Term.apply] at ht'
      obtain ⟨h1, h2⟩ := ht'
      subst h1; subst h2
      exact Or.inl rfl
    | two =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeA =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeB =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeC =>
      injection ht with ht'
      simp [Term.apply] at ht'
  | congr_left hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    obtain ⟨a', hr', rfl⟩ := Term.reduces_delta_delta_app hr
    exact Or.inr (Or.inl ⟨a', hr', rfl⟩)
  | congr_right hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    obtain ⟨b', hr', rfl⟩ := Term.reduces_delta_delta_app hr
    exact Or.inr (Or.inr ⟨b', hr', rfl⟩)

theorem Term.ΩArg_preserves {t t' : Term} (h : t.ΩArg) (hr : Reduces t t') :
    t'.ΩArg := by
  cases h with
  | ω =>
    exact (combω_normalForm.irreducible _ hr).elim
  | I ha =>
    obtain h | ⟨a', hr', rfl⟩ := Term.reduces_combI_app hr
    · subst h
      exact .K ha ha
    · exact .I (Term.ΩArg_preserves ha hr')
  | K ha hb =>
    obtain h | h | h := Term.reduces_K_body hr
    · subst h; exact ha
    · obtain ⟨a', hr', rfl⟩ := h
      exact .K (Term.ΩArg_preserves ha hr') hb
    · obtain ⟨b', hr', rfl⟩ := h
      exact .K ha (Term.ΩArg_preserves hb hr')

/-- One-step reducts of `combω ⬝ a`. -/
theorem Term.reduces_combω_app {a t' : Term} (hr : Reduces (combω ⬝ a) t') :
    t' = combI ⬝ a ⬝ (combI ⬝ a) ∨
    (∃ a', Reduces a a' ∧ t' = combω ⬝ a') := by
  change Reduces (△ ⬝ (△ ⬝ combI) ⬝ combI ⬝ a) t' at hr
  generalize ht : (△ ⬝ (△ ⬝ combI) ⬝ combI ⬝ a : Term) = t at hr
  induction hr generalizing a with
  | rule r =>
    cases r with
    | two =>
      injection ht with ht'
      simp [Term.apply] at ht'
      obtain ⟨h1, h2, h3⟩ := ht'
      subst h1; subst h2; subst h3
      exact Or.inl (by simp [combI, Term.apply])
    | one =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeA =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeB =>
      injection ht with ht'
      simp [Term.apply] at ht'
    | threeC =>
      injection ht with ht'
      simp [Term.apply] at ht'
  | congr_left hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    exact (combω_normalForm.irreducible _ hr).elim
  | congr_right hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    exact Or.inr ⟨t2', hr, by simp [combω, Term.apply]⟩

/-- One-step reducts of `combI ⬝ a ⬝ b`. -/
theorem Term.reduces_combI_app2 {a b t' : Term} (hr : Reduces (combI ⬝ a ⬝ b) t') :
    t' = (△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ a) ⬝ b ∨
    (∃ a', Reduces a a' ∧ t' = combI ⬝ a' ⬝ b) ∨
    (∃ b', Reduces b b' ∧ t' = combI ⬝ a ⬝ b') := by
  generalize ht : (combI ⬝ a ⬝ b : Term) = t at hr
  induction hr generalizing a b with
  | rule r =>
    subst ht
    have hlen := RewriteRules.numChildren_eq_three r
    have : (combI ⬝ a ⬝ b).numChildren = 4 := by
      simp [combI, Term.numChildren, Term.apply]
    omega
  | congr_left hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    obtain h | ⟨a', hr', rfl⟩ := Term.reduces_combI_app hr
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl ⟨a', hr', rfl⟩)
  | congr_right hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    exact Or.inr (Or.inr ⟨t2', hr, rfl⟩)

/-- One-step reducts of a K-app. -/
theorem Term.reduces_K_app {a b c t' : Term}
    (hr : Reduces ((△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b) ⬝ c) t') :
    t' = a ⬝ c ∨
    (∃ a', Reduces a a' ∧ t' = (△ ⬝ △) ⬝ a' ⬝ ((△ ⬝ △) ⬝ b) ⬝ c) ∨
    (∃ b', Reduces b b' ∧ t' = (△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b') ⬝ c) ∨
    (∃ c', Reduces c c' ∧ t' = (△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b) ⬝ c') := by
  generalize ht : ((△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b) ⬝ c : Term) = t at hr
  induction hr generalizing a b c with
  | rule r =>
    subst ht
    have hlen := RewriteRules.numChildren_eq_three r
    have : ((△ ⬝ △) ⬝ a ⬝ ((△ ⬝ △) ⬝ b) ⬝ c).numChildren = 4 := by
      simp [Term.numChildren, Term.apply]
    omega
  | congr_left hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    obtain h | h | h := Term.reduces_K_body hr
    · exact Or.inl (by rw [h])
    · obtain ⟨a', hr', rfl⟩ := h
      exact Or.inr (Or.inl ⟨a', hr', rfl⟩)
    · obtain ⟨b', hr', rfl⟩ := h
      exact Or.inr (Or.inr (Or.inl ⟨b', hr', rfl⟩))
  | congr_right hr ih =>
    expose_names
    obtain ⟨rfl, rfl⟩ := Term.apply_inj ht
    exact Or.inr (Or.inr (Or.inr ⟨t2', hr, rfl⟩))

theorem Term.ΩForm_preserves {t t' : Term} (h : t.ΩForm) (hr : Reduces t t') :
    t'.ΩForm := by
  cases h with
  | ωapp ha =>
    obtain h | ⟨a', hr', rfl⟩ := Term.reduces_combω_app hr
    · subst h
      exact .Iapp ha (.I ha)
    · exact .ωapp (Term.ΩArg_preserves ha hr')
  | Iapp ha hb =>
    obtain h | h | h := Term.reduces_combI_app2 hr
    · subst h
      exact .Kapp ha ha hb
    · obtain ⟨a', hr', rfl⟩ := h
      exact .Iapp (Term.ΩArg_preserves ha hr') hb
    · obtain ⟨b', hr', rfl⟩ := h
      exact .Iapp ha (Term.ΩArg_preserves hb hr')
  | Kapp ha hb hc =>
    obtain h | h | h | h := Term.reduces_K_app hr
    · subst h
      exact Term.ΩArg.apply_ΩArg ha hc
    · obtain ⟨a', hr', rfl⟩ := h
      exact .Kapp (Term.ΩArg_preserves ha hr') hb hc
    · obtain ⟨b', hr', rfl⟩ := h
      exact .Kapp ha (Term.ΩArg_preserves hb hr') hc
    · obtain ⟨c', hr', rfl⟩ := h
      exact .Kapp ha hb (Term.ΩArg_preserves hc hr')

theorem Term.ΩForm_of_reducts {u : Term}
    (h : Relation.ReflTransGen Reduces combΩ u) : u.ΩForm := by
  induction h with
  | refl => exact Term.ΩForm.combΩ
  | tail _ hr ih => exact Term.ΩForm_preserves ih hr

theorem combΩ_diverges : combΩ.Diverges := by
  intro u hu
  have hform := Term.ΩForm_of_reducts hu
  exact Term.progress hform.not_normalForm

theorem exists_diverging_term : ∃ t : Term, t.Diverges :=
  ⟨combΩ, combΩ_diverges⟩


/-! ### Future work (not needed for divergence)
Executable `Term.reduce`, confluence of `Reduces`, and value-classification /
triage examples can return here later. -/
