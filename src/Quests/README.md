# Quests

Each quest is a Lean file of `sorry`s for you to fill in, plus a hints file.

- **Props you are given** look like `def Term.Foo (t : Term) : Prop := sorry`.
  The docstring says what the prop should *mean*. The body is yours: fill it in,
  or replace the `def` with an `inductive` or `structure`. You can change the
  signature too, but then you'll have to adjust the statements that use it.
- **Acceptance checks** are the `example`s right after each prop. They're there
  to catch a definition that's vacuous or has its quantifiers the wrong way
  round. If one turns out to be unprovable, suspect the definition first.
- **Theorems** are the headline statements. Any helper lemmas or auxiliary
  props you need along the way are yours to invent. Inventing them is the
  point, and they aren't signposted on purpose.
- **Hints** are in `hints/`, one file per quest, from smallest to biggest.
  Each hint is inside a collapsed `<details>` block, so open the file in
  Markdown preview to avoid reading ahead.

Build all quests with `lake build Quests`. Each remaining `sorry` shows up as a
"declaration uses 'sorry'" warning.

| Quest | Topic | Size |
|---|---|---|
| `Q1Normalization` | normal forms, normalizing, infinite reductions | small to medium |
| `Q2Confluence` | Church–Rosser and its corollaries | large |
