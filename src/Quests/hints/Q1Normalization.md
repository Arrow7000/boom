# Quest 1 hints

Open in Markdown preview. Hints get bigger as you go down; open only the one you need.

## Part A: `Irreducible`

<details><summary>A1: the definition</summary>

It's one line. `Term.IsNotRewritable` in `TreeCalculus.lean` has the right
shape, but with `RewriteRules` where you want `Reduces`.

</details>

<details><summary>A2: the iff</summary>

You don't need any new ideas: both directions are already lemmas in section
`NormalForms`. One direction holds as stated; the other only holds as its
contrapositive (`by_contra`, `not_not`).

</details>

<details><summary>A3: the acceptance checks</summary>

Prove the iff first; then `combI.Irreducible` and `△.Irreducible` follow from
`NormalForm` facts that already exist. For the stem, write down the step
explicitly: `Reduces.congr_right` around `Reduces.rule RewriteRules.one`.
`Term.Irreducible`'s negation wants a witness.

</details>

## Part B: `HasNormalForm`

<details><summary>B1: the definition</summary>

An `∃` over `Relation.ReflTransGen Reduces`, the same closure `Diverges` uses.

</details>

<details><summary>B2: the iff</summary>

(→) If `t` reached a normal form `n`, `Diverges` says `n` can still step.
Which lemma says it can't?
(←) Take any reduct `u`. Either `u.NormalForm` (contradiction) or not, in
which case `Term.progress`.

</details>

<details><summary>B3: the acceptance checks</summary>

`K △ Ω`: one `RewriteRules.one` step, wrapped in `Relation.ReflTransGen.single`.
`combΩ`: the iff, plus `combΩ_diverges`.

</details>

## Part C: infinite reductions

<details><summary>C1: the definition</summary>

Three reasonable designs:
- a function `f : ℕ → Term` with `f 0 = t`, where every `f n` steps to `f (n+1)`;
- a `coinductive` predicate (works on this project's toolchain) with a single constructor:
  "`t` steps to some `u` that again has an infinite reduction";
- "some set of terms contains `t`, and every term in the set steps to another
  term in the set". This is what the coinductive version unfolds to: look at
  the `.coinduct` principle Lean generates for it.

They make different parts of part C easy or hard, so it's worth seeing which
is which.

</details>

<details><summary>C2: why the obvious construction fails</summary>

You can't just keep applying `progress`: a step can land on a term that has a
normal form (think `K △ Ω`). You need every term in the sequence to still
diverge. So first prove that `Diverges` survives a step: if `t` diverges, it
steps to some `u` that also diverges.

</details>

<details><summary>C3: building the sequence</summary>

Work in the subtype `{u : Term // u.Diverges}`. Use `Classical.choose` to
define `next : {u // u.Diverges} → {u // u.Diverges}`, then set
`f n := (next^[n] ⟨t, h⟩).1`. `Function.iterate_succ_apply'` turns
`next^[n+1] x` into `next (next^[n] x)`, which is the form you want.

</details>

<details><summary>C4: the counterexample</summary>

`K △ Ω = △ ⬝ △ ⬝ △ ⬝ combΩ`. Part B gives it a normal form. For the
infinite reduction, take `combΩ`'s sequence `f` and use
`fun n => △ ⬝ △ ⬝ △ ⬝ f n`, with each step given by `Reduces.congr_right`.

For `¬ △.HasInfiniteReduction`: the first step would start at `△`.

</details>
