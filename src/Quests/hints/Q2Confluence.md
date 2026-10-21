# Quest 2 hints

Open in Markdown preview. Hints get bigger as you go down; open only the one you need.

## Part A: `Confluent`

<details><summary>A1: the definition</summary>

Use `Relation.ReflTransGen r` for "zero or more steps". Mathlib also has
`Relation.Join`, which may or may not read better to you.

</details>

<details><summary>A2: the Fin 3 check</summary>

`1` and `2` have no outgoing steps, so anything reachable from `1` is `1`.
Prove that as a small lemma by induction on `ReflTransGen` (or
`Relation.ReflTransGen.cases_head`). Then `1 = d = 2`.

</details>

## Part B: one-step diamond fails

<details><summary>B1: where to look</summary>

Take a rule-2 redex `△ (△ x) y z` where `z` itself can step. Firing rule 2
first makes two copies of `z`; reducing `z` first makes one.

</details>

<details><summary>B2: a concrete term</summary>

`x = △`, `y = △`, `z = △ ⬝ △ ⬝ △ ⬝ △` (that's `K △ △`, which steps to `△`).
After firing rule 2, the result needs *two* more steps to reach where the
other branch gets in one.

</details>

<details><summary>B3: proving there is no common reduct</summary>

`Reduces` has no `Decidable` instance, so `decide` won't enumerate the
reducts for you. Prove a small inversion lemma per term instead: "if this
term steps to `d`, then `d` is one of these". The `reduces_combI_app`-style
lemmas in section `Divergence` of `TreeCalculus.lean` show the technique
(`generalize`, induction on `Reduces`, `Term.apply_inj`).

</details>

## Part C: the theorem

<details><summary>C1: the shape of the argument</summary>

Part B shows that one-step `Reduces` doesn't have the diamond property,
because steps can copy redexes. Look for a relation `P` in between:
`Reduces ⊆ P ⊆ ReflTransGen Reduces`, where `P` *does* have the diamond
property. Then `ReflTransGen P` and `ReflTransGen Reduces` are the same
relation, and the diamond property for `P` gives confluence (Mathlib:
`Relation.church_rosser`).

</details>

<details><summary>C2: the technique's name</summary>

Parallel reduction (Tait and Martin-Löf): `P` fires any set of the redexes
present in a term at once. In particular it is reflexive (fire none), and it
can work on every child at the same time.

</details>

<details><summary>C3: shaping P for `Term`</summary>

Children are a list, so "every child steps in parallel" is
`List.Forall₂ P cs cs'`. You want one constructor for that, and one per
rewrite rule. In a rule constructor, the parts also take a `P` step, and any
arguments after the first three get reattached (`List.foldl (· ⬝ ·)`), also
after a `P` step.

The facts to prove are: `P` is reflexive, `Reduces ⊆ P`,
`P ⊆ ReflTransGen Reduces`, and the diamond.

</details>

<details><summary>C4: proving the diamond (Takahashi)</summary>

Proving the diamond directly means a large case analysis on both `P` steps.
The shorter route is Takahashi's: define `Term.develop`, which fires every
redex present in a term at once, and prove `P t u → P u t.develop`. The
diamond then follows immediately.

Watch out for rule 3: it fires depending on the *shape* of its third argument
before anything is reduced. Check that a `P` step can't change the shape of a
node with at most two children. `Term.weight` is there if termination of
`develop` gives you trouble.

</details>

<details><summary>C5: worked reference</summary>

`ValOrRedex.lean` proves confluence for the other presentation via a direct
parallel-reduction diamond (`ParStep`, `ParStep.diamond`,
`MultiStepReduction.confluence`). It's a different syntax, but the overall
plan carries over.

</details>

## Part D: consequences

<details><summary>D1: uniqueness of normal forms</summary>

Confluence gives a common `d`. Then a small lemma: a normal form only reduces
to itself (`n.NormalForm → ReflTransGen Reduces n d → d = n`).

</details>

<details><summary>D2: `Convertible`</summary>

Mathlib has `Relation.EqvGen`. Prove `joinable` by induction on it; the
transitivity case is where confluence is used.

</details>

<details><summary>D3: consistency</summary>

`joinable` gives a common `d`. Both `△` and `△ ⬝ △` are normal forms, so by
D1's lemma `d` equals both.

</details>
