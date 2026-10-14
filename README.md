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

`TriageGraph.lean` starts the port-graph model. It treats wiring as a symmetric,
irreflexive partner function and proves that distinct active pairs cannot
share an agent. Rule replacement and its preservation properties remain to
be defined.

`TriageRuleReadback.lean` follows the exported RHS wires of each `Triage`
rule. It proves the expressions passed to `Eval` are respectively `w`, `x u`,
and `y u v`, that the unused inputs go to `Erase`, and that the result is
wired to the original continuation. These are local template theorems;
the whole-net simulation still needs the rewrite semantics.

`TriageResources.lean` proves that finite copy/erase task trees terminate
under any order of administrative steps. It abstracts from the copied output
nets and will need to be connected to the concrete `Dup`/`Erase` rewrites.

`TriageInspection.lean` defines the finite static tree domain and proves its
encoding is injective. For every such tree, the abstract machine reaches the
appropriate triage branch and passes its exact children without reducing them.
The resulting TC reduction is proved for any machine continuation. It also
constructs one closed program that classifies the three root shapes for every
static tree, regardless of the contents of its children.

`TriageRuleProperties.lean` proves unique rule selection for each unordered
active pair and checks that any active pair wired entirely within a rule's
replacement has an applicable exported rule. Connections through the
surrounding net remain part of the whole-net simulation obligation.

`TriageConcrete.lean` is an executable model of whole-net replacement using
the exported rules. It follows alternating old and new wires through each
rule boundary, checks a total one-wire-per-port graph invariant, and reads
the output tree. A finite Lean check covers all 65 closed source terms with
up to six leaves: each abstract run finishes, each concrete trace stays well
formed, and its final tree matches the abstract result with no active pairs.
This finite check is evidence for the model, not the universal simulation
theorem.
For any concrete net satisfying its wellformedness check, the edge lookup is
proved total on live ports, symmetric, and irreflexive. Such a net maps into
`TriageGraph.Net`, so its distinct active pairs are formally disjoint.
The stronger executable `valid` check also tracks fresh ID allocation, and a
general theorem proves that every rule replacement preserves that ID bound
and cannot duplicate a live agent ID. The remaining generic preservation
lemma is for the alternating wire splice across the rule boundary.

The remaining proof obligation is a simulation between concrete net rewrites
and `TriageMachine.Step`, including the administrative copy and erase steps.
The current theorems do not establish semantic correctness of arbitrary nets.

## References

- Barry Jay. *Reflective Programs in Tree Calculus.* (book)
- [treecalcul.us](https://treecalcul.us/) — demos and specification (Johannes Bader)
- Barry Jay. [Calculus, calculi](https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md) — original three-rule tree calculus vs triage calculus
