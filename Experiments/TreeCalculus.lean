import Mathlib

@[grind cases]
inductive Term where
  | delta
  | app : Term → Term → Term
  deriving DecidableEq

-- Custom Repr instance to display terms with our notation
partial def Term.repr : Term → Nat → String
  | .delta, _ => "Δ"
  | .app t1 t2, prec =>
    -- Left associative, precedence 70
    let s1 := t1.repr 70
    let s2 := t2.repr 71
    let result := s1 ++ " ⬝ " ++ s2
    if prec > 70 then "(" ++ result ++ ")" else result

instance : Repr Term where
  reprPrec t prec := t.repr prec



-- Notation for Term construction
-- Δ symbol for delta (works in patterns too!)
syntax (name := termDelta) "Δ" : term

-- Left-associative application notation using ⬝ (white diamond, U+2B1D)
-- (name := ...) makes it work in patterns!
syntax:70 (name := termApp) term:70 " ⬝ " term:71 : term

macro_rules
  | `(Δ) => `(Term.delta)
  | `($t1 ⬝ $t2) => `(Term.app $t1 $t2)

-- Make Lean display terms using our notation
@[app_unexpander Term.delta]
def unexpandDelta : Lean.PrettyPrinter.Unexpander := fun _ => `(Δ)

@[app_unexpander Term.app]
def unexpandApp : Lean.PrettyPrinter.Unexpander := fun
  | `($_ $t1 $t2) => `($t1 ⬝ $t2)
  | _ => throw ()




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










@[simp,grind]
def IsReducible (term : Term) := ∃ output, RewriteRules term output

@[simp,grind]
def Term.IsIrreducible (term : Term) := ∀ output, ¬RewriteRules term output



-- Helper: count the number of nested applications (depth of left spine)
@[grind]
def Term.appDepth : Term → Nat
  | .delta => 0
  | .app t t' => 1 + t.appDepth + t'.appDepth

@[grind]
theorem RewriteRules.leaf_irreducible : Term.IsIrreducible Δ := by grind

@[grind]
theorem RewriteRules.stem_irreducible : Term.IsIrreducible (Δ⬝x) := by grind

@[grind]
theorem RewriteRules.fork_irreducible : Term.IsIrreducible (Δ⬝x⬝y) := by grind



-- @[grind]
-- theorem Term.Irreducible_iff_both {t1 t2 : Term}
--   (h1 : t1.IsIrreducible)
--   (h2 : t2.IsIrreducible)
--   : (t1 ⬝ t2).IsIrreducible := by
--   simp
--   intro output prem
--   cases prem
--   · simp at h1 h2
--     sorry




-- All rewrite rules require at least 3 applications
-- Expressions with < 3 applications from delta are values (irreducible)
@[grind]
theorem small_depth_irreducible (t : Term) (h : t.appDepth < 3) : Term.IsIrreducible t := by
  sorry


@[grind]
theorem large_depth_reducible (t : Term) (h : t.appDepth ≥ 3) : IsReducible t := by
  sorry




-- Full reduction step: applies Reduces (with congruence) anywhere in the term
def Term.reduce
  (term : Term)
  : { term' // Reduces term term' ∨ (IsIrreducible term ∧ term' = term) } :=

  match hterm : term with
  -- Try to apply a rewrite rule at the root first
  | .app (.app (.app .delta .delta) y) z =>
    ⟨y, Or.inl (Reduces.rule RewriteRules.one)⟩

  | .app (.app (.app .delta (.app .delta x)) y) z =>
    ⟨Term.app (Term.app x z) (Term.app y z), Or.inl (Reduces.rule RewriteRules.two)⟩

  | .app (.app (.app .delta (.app (.app .delta w) x)) y) .delta =>
    ⟨w, Or.inl (Reduces.rule RewriteRules.threeA)⟩

  | .app (.app (.app .delta (.app (.app .delta w) x)) y) (.app .delta u) =>
    ⟨Term.app x u, Or.inl (Reduces.rule RewriteRules.threeB)⟩

  | .app (.app (.app .delta (.app (.app .delta w) x)) y) (.app (.app .delta u) v) =>
    ⟨Term.app (Term.app y u) v, Or.inl (Reduces.rule RewriteRules.threeC)⟩

  -- Values (irreducible)
  | .delta =>
    ⟨.delta, Or.inr ⟨RewriteRules.leaf_irreducible, rfl⟩⟩

  | .app .delta x =>
    ⟨.app .delta x, Or.inr ⟨RewriteRules.stem_irreducible, rfl⟩⟩

  | .app (.app .delta x) y =>
    ⟨.app (.app .delta x) y, Or.inr ⟨RewriteRules.fork_irreducible, rfl⟩⟩
  | (app (app (app (app _ _) _) _) _) => by
    sorry
  | (app (app (app Δ (app (app (app _ _) _) _)) _) _) => by sorry
  | (app (app (app Δ (app (app Δ _) _)) _) (app (app (app _ _) _) _)) => by sorry
  -- No rule matches at root: try reducing left subterm (congruence)
  -- | .app t1 t2 =>
  --   have : t1.appDepth < (Term.app t1 t2).appDepth := by
  --     simp [Term.appDepth]
  --     omega

  --   let ⟨t1', h1⟩ := t1.reduce
  --   if ht1 : t1' = t1 then
  --     have : t2.appDepth < (Term.app t1 t2).appDepth := by simp [Term.appDepth]
  --     let ⟨t2', h2⟩ := t2.reduce
  --     ⟨.app t1 t2', ?_⟩
  --   else
  --     ⟨Term.app t1' t2, ?_⟩
  termination_by term.appDepth
  where finally
    · subst_eqs
      cases h2 with
      | inl h2 => refine .inl (.congr_right h2)
      | inr h2 =>
        cases h1 with
        | inl h1 =>
          obtain ⟨_,_⟩ := h2
          subst_eqs
          left
          refine .congr_left h1
        | inr h1 =>
          obtain ⟨_,_⟩ := h1
          obtain ⟨_,_⟩ := h2
          subst_eqs
          simp only [and_true]
          right
          expose_names
          exact t1.Irreducible_iff_both left left_1
    · cases h1 with
      | inl h =>
        left
        subst_eqs
        refine .congr_left h
      | inr h =>
        absurd h.right
        exact ht1



-- Note: Not ALL terms of the form Δ⬝x⬝y⬝z are reducible - it depends on x's structure
-- This is just an example showing that SOME such terms reduce
theorem RewriteRules.redex_one_reducible : IsReducible (Δ⬝Δ⬝y⬝z) := by
  simp [IsReducible]
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
-- Values (irreducible terms) are exactly: leafs, stems, and forks

def IsLeaf (t : Term) : Prop := t = Δ
def IsStem (t : Term) : Prop := ∃ a, t = (Δ⬝a)
def IsFork (t : Term) : Prop := ∃ a b, t = (Δ⬝a⬝b)

-- Every irreducible term is exactly one of these three kinds
theorem value_classification :
    ∀ t, IsIrreducible t ↔ (IsLeaf t ∨ IsStem t ∨ IsFork t) := by
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
