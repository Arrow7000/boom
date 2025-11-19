
@[grind cases]
inductive Term where
  | delta
  | app : Term → Term → Term



-- Notation for Term construction
-- Δ symbol for delta
syntax "Δ" : term

-- Left-associative application notation using bullet operator ∙ (U+2219)
-- Lower precedence than function application to avoid conflicts
syntax:50 term:50 "∙" term:51 : term

macro_rules
  | `(Δ) => `(Term.delta)
  | `($t1 ∙ $t2) => `(Term.app $t1 $t2)




@[grind cases]
inductive RewriteRules : (input output : Term) → Prop where
  | one :
    RewriteRules (Δ∙Δ∙y∙z)
      y

  | two :
    RewriteRules (Δ∙(Δ∙x)∙y∙z)
      (x∙z∙(y∙z))

  | threeA :
    RewriteRules (Δ∙(Δ∙w∙x)∙y∙Δ)
      w

  | threeB :
    RewriteRules (Δ∙(Δ∙w∙x)∙y∙(Δ∙u))
      (x∙u)

  | threeC :
    RewriteRules (Δ∙(Δ∙w∙x)∙y∙(Δ∙u∙v))
      (y∙u∙v)






-- def RewriteRules.decide (term : Term) : Decidable



@[simp,grind]
def IsReducible (term : Term) := ∃ output, RewriteRules term output

@[simp,grind]
def IsIrreducible (term : Term) := ∀ output, ¬RewriteRules term output



@[grind]
theorem RewriteRules.leaf_irreducible : IsIrreducible Δ := by grind

@[grind]
theorem RewriteRules.stem_irreducible : IsIrreducible (Δ∙x) := by grind

@[grind]
theorem RewriteRules.fork_irreducible : IsIrreducible (Δ∙x∙y) := by grind


def Term.step (term : Term) : { term' // RewriteRules term term' ∨ (IsIrreducible term ∧ term' = term) } :=
  match hterm : term with
  -- Rule one: Δ∙Δ∙y∙z ⟶ y
  | .app (.app (.app .delta .delta) y) z =>
    ⟨y, Or.inl RewriteRules.one⟩

  -- Rule two: Δ∙(Δ∙x)∙y∙z ⟶ x∙z∙(y∙z)
  | .app (.app (.app .delta (.app .delta x)) y) z =>
    ⟨Term.app (Term.app x z) (Term.app y z), Or.inl RewriteRules.two⟩

  -- Rule threeA: Δ∙(Δ∙w∙x)∙y∙Δ ⟶ w
  | .app (.app (.app .delta (.app (.app .delta w) x)) y) .delta =>
    ⟨w, Or.inl RewriteRules.threeA⟩

  -- Rule threeB: Δ∙(Δ∙w∙x)∙y∙(Δ∙u) ⟶ x∙u
  | .app (.app (.app .delta (.app (.app .delta w) x)) y) (.app .delta u) =>
    ⟨Term.app x u, Or.inl RewriteRules.threeB⟩

  -- Rule threeC: Δ∙(Δ∙w∙x)∙y∙(Δ∙u∙v) ⟶ y∙u∙v
  | .app (.app (.app .delta (.app (.app .delta w) x)) y) (.app (.app .delta u) v) =>
    ⟨Term.app (Term.app y u) v, Or.inl RewriteRules.threeC⟩

  -- Base case: Δ is irreducible (leaf)
  | .delta =>
    ⟨.delta, Or.inr ⟨RewriteRules.leaf_irreducible, rfl⟩⟩

  -- Base case: Δ∙x is irreducible (stem)
  | .app .delta x =>
    ⟨.app .delta x, Or.inr ⟨RewriteRules.stem_irreducible, rfl⟩⟩

  -- Base case: Δ∙x∙y is irreducible (fork)
  | .app (.app .delta x) y =>
    ⟨.app (.app .delta x) y, Or.inr ⟨RewriteRules.fork_irreducible, rfl⟩⟩

  -- All other cases: proving irreducibility is complex, so we leave it as sorry
  | .delta => by
    refine ⟨.delta, Or.inr ⟨?_, rfl⟩⟩
    simp
    intro output prem
    grind


-- Note: Not ALL terms of the form Δ∙x∙y∙z are reducible - it depends on x's structure
-- This is just an example showing that SOME such terms reduce
theorem RewriteRules.redex_one_reducible : IsReducible (Δ∙Δ∙y∙z) := by
  simp [IsReducible]
  exact ⟨y, RewriteRules.one⟩


-- Inductive predicate: a term normalizes if it's either irreducible
-- or it can reduce to something that normalizes
inductive Normalizes : Term → Prop where
  | irreducible {t : Term} :
      IsIrreducible t →
      Normalizes t
  | step {t t' : Term} :
      RewriteRules t t' →
      Normalizes t' →
      Normalizes t

-- The main theorem we want to prove: every term normalizes
-- NOTE: This is NOT provable! Tree Calculus is Turing-complete,
-- so some terms will reduce forever.
theorem every_term_normalizes : ∀ t : Term, Normalizes t := by
  sorry


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
def IsStem (t : Term) : Prop := ∃ a, t = (Δ∙a)
def IsFork (t : Term) : Prop := ∃ a b, t = (Δ∙a∙b)

-- Every irreducible term is exactly one of these three kinds
theorem value_classification :
    ∀ t, IsIrreducible t ↔ (IsLeaf t ∨ IsStem t ∨ IsFork t) := by
  sorry

-- The "case" combinator: Δ (Δ w x) y can distinguish between the three kinds
-- of values and compute different results for each
def case_combinator (w x y : Term) : Term := Δ∙(Δ∙w∙x)∙y

theorem case_on_leaf :
    ∀ w x y, case_combinator w x y ∙ Δ ⟶* w := by
  sorry

theorem case_on_stem :
    ∀ w x y u, (case_combinator w x y ∙ (Δ∙u)) ⟶* (x∙u) := by
  sorry

theorem case_on_fork :
    ∀ w x y u v, (case_combinator w x y ∙ (Δ∙u∙v)) ⟶* (y∙u∙v) := by
  sorry

-- This demonstrates intensionality: we can write a program (case_combinator)
-- that inspects the structure of a value and computes different things
-- based on whether it's a leaf, stem, or fork
