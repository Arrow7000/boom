# boom 💥

Dutch for _tree_. Also: 💥.

A Lean 4 formalisation of [tree calculus](https://treecalcul.us/) — specifically the **triage** (five-rule) variant suggested by Johannes Bader and used on that site / in Barry Jay’s later work. Programs and values are unlabeled binary trees (leaf / stem / fork); the sole operator is △.

You can also explore terms visually: the `#tree t` command renders an interactive tree right in the Lean infoview. Orange nodes are redexes: click one to rewrite it, or use the controls to step, play, and run through a reduction. Under the hood, every step is computed by a rewrite function formally proved sound against the reduction relation.

![boom demo](assets/boom-demo.gif)

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`, managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

## Representations

This project explores two different ways to formalise tree calculus:

- **`TreeCalculus.Term`**: The canonical syntax. Terms are nodes with an ordered list of arguments. Reduction and normal forms are in `TreeCalculus.lean`.
- **`TreeCalculus.ValOrRedex`**: An alternative presentation split into `Value` and `ValOrRedex` types.

Both are kept around to compare them. Note that their reduction relations are currently slightly different: `ValOrRedex` drops trailing arguments, meaning its confluence theorem doesn't immediately carry over to `Term`.

## References

- Barry Jay. _Reflective Programs in Tree Calculus._ (book)
- [treecalcul.us](https://treecalcul.us/) — demos and specification (Johannes Bader)
- Barry Jay. [Calculus, calculi](https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md) — original three-rule tree calculus vs triage calculus
