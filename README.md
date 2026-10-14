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
share an agent. `TriageConcrete.lean` defines executable rule replacement.

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
and cannot duplicate a live agent ID.
`TriageBoundary.lean` proves the local conditions for that splice: each old
and replacement layer is a matching, the active principal wire is absent
from the old layer, and every applicable rule auxiliary port occurs in both
layers. It also proves that retained old wires and direct replacement wires
have disjoint endpoints.
`TriagePaths.lean` defines a declarative alternating walk and proves that
`follow` returns an endpoint exactly when such a walk fits within its fuel.
The endpoint and length of a terminating walk from a fixed starting state
are unique. Its interface states never repeat. For an applicable concrete
rule, every terminating boundary walk fits within the fuel used by
`Net.replace`. A finite injective transition argument also proves that every
walk starting at an exposed real endpoint terminates at another real endpoint
within that fuel. Separate closed interface loops can vanish. A generic
reverse-chain lemma gives uniqueness of predecessor-free starts reaching one
terminal interface state. The old and replacement boundary layers are also
proved disjoint on real ports, using the fresh ID bound.

`TriageSplicePaths.lean` connects walks to their real endpoints. Under the two
matching invariants and disjointness of real ports, its path relation is
symmetric, gives each source a unique target, and cannot connect a port to
itself.

`TriageSplice.lean` now proves that transfer. The duplicate filter preserves
endpoint coverage and produces a matching for a symmetric relation with
unique, distinct partners. Applied to `spliceStarts`, the result proves that
every exposed boundary port is used exactly once for every applicable rule
on a valid net.

`TriagePreservation.lean` combines that boundary matching with retained old
wires and direct replacement wires. Its universal `Net.replace_valid` theorem
proves that replacing an applicable active pair by any well formed rule
preserves the complete graph invariant: every live port is used exactly once,
all used ports belong to surviving or created agents or the external result,
live agent IDs stay distinct, and new allocation remains fresh.

`TriageReduction.lean` proves that every executable `redexChoices` entry is
an applicable exported rule on an active pair. Hence every finite schedule
from a valid net stays valid. The first-redex `run` and every state in its
`trace` inherit this universal invariant.

`TriageInitial.lean` proves that the source builder produces a valid initial
net for every finite source syntax. Its construction invariant records
unconnected ports until the evaluator and external result port are attached.
Together with reduction preservation, this proves graph validity at every
state of every finite schedule from any source term, without a size bound.
The correspondence of final output syntax with tree calculus remains a
separate simulation obligation.
A separate bounded check explores every redex choice in one copying net; each
schedule terminates within 40 interactions at the same tree and keeps the
stronger validity invariant throughout.

`TriageEquivalence.lean` defines graph isomorphism by a bijection on agent IDs,
fixing free ports and port slots. It is an equivalence relation and preserves
active pairs and the executable syntax readback at every fuel bound.

`TriageResidual.lean` proves that executable choices either coincide exactly
or have disjoint agents. A replacement preserves the other disjoint choice,
even when auxiliary wires connect the two pairs. Both orders are therefore
valid executable schedules, with the same final allocation counter. Equality
of their resulting wire graphs remains to be proved.

`TriageAllocation.lean` constructs the explicit bijection swapping the two
fresh allocation blocks. Under that bijection, the complete agent lists of
two independent replacements are permutations of one another and all kind
lookups agree. The outstanding local diamond concerns wire connectivity.

`TriageEncoding.lean` relates raw source trees to concrete agents and wires.
For every finite syntax, the source builder establishes this relation, and
reading the source side of the initial evaluator reconstructs the original
syntax exactly with sufficient fuel. Representation is unique and preserved
by graph isomorphism. A represented source whose root is outside a contracted
active pair is preserved exactly by the rewrite: its descendants have their
principal ports attached to auxiliary ports and cannot be active pairs. This
proves stability of raw source payloads, including syntactically reducible
payloads. Evaluator and continuation simulation still need separate proofs.

`TriageLocalSemantics.lean` connects declarative boundary routes to actual
post-rewrite neighbor lookups. Universal local semantic proofs cover
`Eval/Leaf`, `Call/Leaf`, and `Call/Stem` in arbitrary valid surrounding nets:
the latter two expose a stem or fork retaining the exact raw source arguments.
These local interactions are the first pieces of the concrete machine
simulation; they do not yet compose into a complete simulation theorem.

`TriageDispatch.lean` proves the concrete structural inspection step for all
three head shapes in arbitrary valid surrounding nets. Given raw inputs
`w`, `x`, and `y`, the actual exported replacement starts evaluation of
`w`, `x u`, or `y u v`, retaining the exact raw child syntax. Its combined
`dispatch_from_inputs` theorem also establishes the corresponding abstract
machine transition; `dispatch_tc_sound` connects that transition to the
original TC term reduction relation under any abstract continuation. The
continuation lies outside the replaced pair as a
consequence of the input representations and matching invariant; no extra
separation assumption is needed. This is a universal local simulation of
inspection, with no requirement that children be normalized. It does not
yet prove reachability of every such represented state, simulate the full
continuation stack, or discharge the resulting erasure tasks.

The remaining semantic obligations are confluence of concrete rewrites up to
renaming allocated agents and reordering wire lists, and a simulation between
concrete net rewrites and `TriageMachine.Step`, including the administrative
copy and erase steps. That simulation must transfer the abstract structural
inspection theorems to concrete execution. Universal graph validity does not
yet establish agreement of outputs under arbitrary reduction schedules.

## References

- Barry Jay. *Reflective Programs in Tree Calculus.* (book)
- [treecalcul.us](https://treecalcul.us/) — demos and specification (Johannes Bader)
- Barry Jay. [Calculus, calculi](https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md) — original three-rule tree calculus vs triage calculus
