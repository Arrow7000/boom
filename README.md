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

## Tree Calculus representations

`Term` in `TreeCalculus.Term` is the canonical syntax representation: a node
with an ordered list of arguments, with reduction and normal forms defined
separately in `TreeCalculus.lean`. The `Value` / `ValOrRedex` presentation and
its proofs live in `TreeCalculus.ValOrRedex` (check with
`lake build TreeCalculus.ValOrRedex`). Both presentations remain available for
future comparisons and equivalence results. Their current reduction relations
differ: the `ValOrRedex` relation discards trailing arguments, so its confluence
theorem does not establish confluence for `Term`.

## Current research: native reflection for interaction nets

Find a small interaction-net system combining native structural reflection
with universality for other interaction-net systems. We may design its agents
and rules from scratch; preserving Lafont's existing rules or adding exactly
one agent is not a requirement.

The target is:

- Executable programs can inspect and manipulate their own native structure,
  including the programs implementing reflection. Callers do not first supply
  a separately encoded AST, and execution and metaprogramming share a
  representation.
- Structure includes actual graph connectivity: shared subnets must be
  distinguishable from separate structurally identical copies, and cycles
  must remain visible where present in the native value domain. Compare
  structure up to agent renaming, preserving kinds, ordered ports, and the
  external interface; editor coordinates and incidental allocation IDs are
  not the intended observables.
- Other finite interaction-net systems, including ordinary interaction
  combinators, admit a compositional translation that preserves interfaces
  and simulates source interactions. Turing completeness alone is
  insufficient for this requirement.
- Observation and execution preserve confluence. We must specify what
  constitutes an inspectable value and how it becomes stable for inspection;
  a snapshot that races against active rewrites is not yet a defined feature.
- Seek a small basis after finding a viable design. "Zero cost reflection"
  means no mandatory conversion to a separate syntax representation; it does
  not promise that traversal, reconstruction, or copying takes zero steps.

The inspectable domain explicitly includes deadlocked nets with no active
pairs. The feasibility investigation below establishes an obstruction under
ordinary local interaction rules. Copying a chosen tree domain remains a
different claim from copying arbitrary graphs; the original duplication
results and their assumptions are recorded in the report.

### Feasibility result with deadlocked nets included

The user confirmed that reflection must cover deadlocked principal-port
cycles too. Under that requirement, ordinary one-principal-port interaction
nets cannot provide the requested native graph reflection: a sealed region
whose principals all point to internal auxiliary ports cannot participate in
a first interaction, so its contents cannot be distinguished from outside.
Compositional principal-net translation preserves counterexamples in any
universal target signature.

The [feasibility report and reproducible experiments](../netties/research/native-reflection/README.md)
state the assumptions, give the contextual proof, audit the primary sources,
and distinguish partial quoting mechanisms from the full requirement. This
is a mathematical obstruction with executable witnesses, not a new Lean
formalization. Meeting the unchanged reflection requirement needs a change to
the interaction model; adding ordinary agents alone cannot remove it.

## Archived TC implementation

The earlier TC-oriented interaction-net formalization is preserved in
[src/archive/triage](src/archive/triage/README.md), with its detailed proof
inventory and limitations. Its optional library is `TriageArchive`; it is not
part of `lake build` / the default `Boom` target, whose root is `TreeCalculus`.
The archived implementation and its unfinished proof roadmap are background
reference, not the current research objective.

## References

- Barry Jay. *Reflective Programs in Tree Calculus.* (book)
- [treecalcul.us](https://treecalcul.us/) — demos and specification (Johannes Bader)
- Barry Jay. [Calculus, calculi](https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md) — original three-rule tree calculus vs triage calculus
