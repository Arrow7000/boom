# boom 💥

Dutch for *tree*. Also: 💥.

A Lean 4 formalisation of [tree calculus](https://treecalcul.us/) — specifically the **triage** (five-rule) variant suggested by Johannes Bader and used on that site / in Barry Jay’s later work. Programs and values are unlabeled binary trees (leaf / stem / fork); the sole operator is △.

Extracted from a personal experiments monorepo with history intact.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.26.0`, managed by `elan`). On a fresh clone:

```bash
lake exe cache get   # download prebuilt Mathlib oleans (don't recompile Mathlib!)
lake build
```

## Interaction-net candidate

`TriageMachine.lean` models the evaluator used by the adjacent `netties`
playground. Its step and whole-run soundness theorems relate the abstract
machine to `Term.Reduces`; its example checks that fork inspection precedes
evaluation of a selected child.

`TriageRules.lean` is generated from `netties/src/core/triageMachine.ts`.
`TriageRuleModel.lean` checks the exported port wiring, rule uniqueness,
copy/erase layouts, and the evaluator barriers before `Call`, `Case`, and
`Triage`. From `../netties`, run `npm run formal:export` after changing the
system and `npm run formal:check` to check freshness and build the Lean proofs.

The remaining proof obligation is a simulation between concrete net rewrites
and `TriageMachine.Step`, including the administrative copy and erase steps.
The current theorems do not establish semantic correctness of arbitrary nets.

## References

- Barry Jay. *Reflective Programs in Tree Calculus.* (book)
- [treecalcul.us](https://treecalcul.us/) — demos and specification (Johannes Bader)
- Barry Jay. [Calculus, calculi](https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md) — original three-rule tree calculus vs triage calculus
