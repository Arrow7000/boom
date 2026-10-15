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
nets; the concrete resource modules described below establish the corresponding
executable `Dup`/`Erase` results.

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
of their resulting wire graphs is established below, up to the allocation
block permutation.

`TriageAllocation.lean` constructs the explicit bijection swapping the two
fresh allocation blocks. Under that bijection, the complete agent lists of
two independent replacements are permutations of one another and all kind
lookups agree. Wire connectivity is addressed below.

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
inspection, with no requirement that children be normalized. This module does not
prove reachability of every such represented state. The continuation and
erasure obligations for these local transitions are discharged by
`TriageDispatchResources.lean` below.

`TriageContraction.lean` proves that contracting two sets of internal graph
vertices is equivalent to contracting their union, so the order commutes.
The theorem handles arbitrary directed edge relations and internal cycles.
`TriageSpliceContraction.lean` proves that a complete alternating splice
implements exactly this contraction of its interface vertices.
`TriageReplacementContraction.lean` extends this characterization to the
complete executable replacement, including retained surrounding wires.
Its universal `replace_iff_contract` theorem characterizes the actual
post-rewrite neighbor relation by paths through the removed pair.
`TriagePortContraction.lean` translates this equation into a shared concrete
port namespace. `TriageWireCommutation.lean` applies contraction commutation
and the allocation block swap to prove `double_iso`: both orders of any two
distinct executable choices produce isomorphic complete nets, including when
auxiliary wires connect the pairs. This closes the executable local diamond.

`TriageEquivariance.lean` proves that executable steps respect isomorphisms
with equal allocation counters that fix unused future IDs. The local diamond
produces exactly these isomorphisms, so they can be moved past later steps.
`TriageConfluence.lean` uses the local diamond and the Church-Rosser theorem
to prove **confluence of all finite executable schedules from any valid net,
up to graph isomorphism**. Its joining schedules consist of actual executable
steps; renaming steps used inside the argument are postponed to the end.
Consequently, every two stopped schedules from the same source have
isomorphic results and identical syntax readbacks at every fuel bound. This
applies to all finite source terms through `initial_confluence` and
`initial_finished_readback`. It does not assert termination of every term.

`TriageRawEncoding.lean` gives concrete representations of the four raw
resource constructors and relates them to syntax readback.
`TriageResourceRules.lean` connects abstract jobs to the eight exported
copy/erase rules, including the child-controller and copy-output wiring.
`TriageResourceJobs.lean` proves that each active represented job creates
exactly its child jobs with intact raw payloads; all other represented jobs
survive. `TriageResourceExecution.lean` proves that any finite forest of such
jobs can be drained by actual executable steps, in exactly the sum of the
raw-tree sizes. Every recorded administrative step reduces this measure by
one, so arbitrary administrative job selection is well founded. These
theorems concern the represented job forest.
`TriagePendingSources.lean` describes sources containing pending copies and
proves that administrative execution preserves their exact raw structure.
Draining a forest materializes all sources observed at free, evaluator, and
continuation ports simultaneously. Its `copy_correct` theorem produces two
distinct concrete roots with the original raw tree; `erase_correct` preserves
all such observed raw sources while draining the erasure job.
`TriageContinuations.lean` represents the complete `Call`/`Case`/`Triage`
continuation stack and its argument sources. Resource execution preserves
the stack, including pending argument copies, and an ordinary interaction
preserves every untouched materialized continuation stack.
`TriageCaseCopy.lean` proves a complete concrete macro transition for
`Case/Stem`: the case interaction starts a represented copy job, its finite
execution materializes `(x arg) (y arg)`, and the resulting evaluator retains
the complete original continuation stack. The argument may contain arbitrary
raw applications; no normalization or size bound is assumed.
`TriageCaseErase.lean` proves the corresponding `Case/Leaf` transition,
including complete erasure of the unused argument. `TriageCaseFork.lean`
constructs the successor `Triage` frame with its exact raw branches.
`TriageCaseSimulation.lean` combines all three cases into a universal concrete
implementation of each abstract inspection transition, preserving the full
successor continuation, and derives soundness for TC reduction.
`TriageDispatchResources.lean` strengthens structural dispatch for all three
head shapes: it creates the two actual erasure jobs for precisely the unused
branches, drains them in their total raw-tree size, and preserves the selected
source and full continuation. Its `dispatch_simulation` theorem supplies both
the complete concrete execution and corresponding abstract machine step.
The inspected raw children need not be normalized.

The remaining semantic obligation is to assemble a complete simulation for
all source terms: finish the evaluator/call control transitions, relate
initial nets to represented machine states, and connect finished states to
output readback. All `Case` and `Triage` transitions now have universal local
implementations with complete resource execution and represented continuation
stacks. Confluence already establishes that reduction order cannot change
stopped results. Agreement of those results with TC execution for every
source term still needs the assembled simulation; bounded examples do not
supply it.

## References

- Barry Jay. *Reflective Programs in Tree Calculus.* (book)
- [treecalcul.us](https://treecalcul.us/) — demos and specification (Johannes Bader)
- Barry Jay. [Calculus, calculi](https://github.com/barry-jay-personal/blog/blob/main/2024-12-12-calculus-calculi.md) — original three-rule tree calculus vs triage calculus
