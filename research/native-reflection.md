# Native reflection for interaction nets

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

## Feasibility result with deadlocked nets included

The user confirmed that reflection must cover deadlocked principal-port
cycles too. Under that requirement, ordinary one-principal-port interaction
nets cannot provide the requested native graph reflection: a sealed region
whose principals all point to internal auxiliary ports cannot participate in
a first interaction, so its contents cannot be distinguished from outside.
Compositional principal-net translation preserves counterexamples in any
universal target signature.

The [feasibility report and reproducible experiments](../../netties/research/native-reflection/README.md)
state the assumptions, give the contextual proof, audit the primary sources,
and distinguish partial quoting mechanisms from the full requirement. This
is a mathematical obstruction with executable witnesses, not a new Lean
formalization. Meeting the unchanged reflection requirement needs a change to
the interaction model; adding ordinary agents alone cannot remove it.
