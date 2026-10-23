# Maximal root-blob replacement: complete source-to-source proof proposal

Author: dot (OpenAI), 23 October 2026.
Status: UNELABORATED Lean source proposal. No compiler, runtime, kernel,
installation, solver or CI execution was performed. File inspection is not
a verification certificate. Earlier accepted hand arguments remain intact.

## 1. Exact endpoint

`RootBlobMaximalEndpoint.maximal_root_blob_full` proposes the full theorem
for a finite, single-root, binary, simple, leaf-observed DAG whose root is
its last stable ancestor, with a nontrivial maximal internally bridgeless
root-containing region having exactly two boundary **edge occurrences**.

The state space is finite with at least two states. Every original edge
matrix varies freely and independently over ALL strictly positive
H-equivariant stochastic matrices. The root varies over H-invariant
probability distributions. The entire original inheritance assignment is
fixed, strictly positive and normalized at every nonroot vertex.

The conclusion contains, separately:

1. Admissibility of the replacement as a finite ranked single-root DAG with
   exactly the original labelled leaves.
2. Binary indegrees/outdegrees.
3. Absence of parallel edges.
4. The root-last-stable-ancestor condition.
5. Admission of the original inheritance weights restricted to surviving
   original edge occurrences.
6. Exact equality of the two complete observed-law parameter images.

Thus the rank-free equality of state sums is not being used to infer graph
admission. Both model-image directions are included, not only inclusion,
closure equality or a generic claim.

## 2. Literal target, not a surrogate two-port graph

Let R be the original region. The final replacement has a fresh root and
exactly the original vertices outside R. Its edge type consists of the
original edges whose targets are outside R. Each such edge keeps its target
and its individual inheritance weight. Its source is the fresh root if its
original source was inside R; otherwise its original outside source is
retained. The original labelled observations are retained.

The explicit rank is zero at the fresh root and original rank plus two at
each outside vertex. This gives an admissible rank, rather than accepting
an arbitrary rank field in the final theorem.

The intermediate root-to-port-to-outside fork is NOT binary: its two ports
have indegree/outdegree (1,1). The identification module proves that this
intermediate is a vertex/edge relabeling of two subdivisions of the actual
replacement. Exact two-directional subdivision equality then suppresses
both ports. Their intermediate ranks, transported from those subdivisions,
are two and one; this intermediate also receives explicit graph and weight
admission proofs. No identity matrix is inserted into a strictly positive
class, and no limiting argument is used.

## 3. What the source adapter now proves

The original maximal-blob record contains a vertex set, actual root
membership, nontriviality, connectedness after deleting any one internal
edge, maximality, and boundary cardinality two. It does not contain
ancestry, two internal sinks, a probability identity or a model-image
equality. Deleting a global edge outside the induced region does nothing,
so the no-cut-edge field is equivalently indexed over all original edges.

Internal degree at least two is derived by taking an initial edge of a
nonconstant internal undirected walk, then taking an initial edge of a
walk after that first edge is deleted. Binary leaf degree one then proves
that the original region is hidden. The two boundary occurrences are
enumerated from their finite cardinality, using classical choice rather
than eliminating a propositional existence statement directly into data.

Ancestry is derived from actual-root membership, hiddenness and the exact
two-edge boundary. If one edge entered, there would be only one possible
exit. A root-to-outside-source path and an inside-target-to-leaf path must
both use it, forcing a strict rank cycle. Root reachability and the
existence of a reachable observed sink are themselves proved from finite
ranked DAG admission. Maximality is not needed for this stronger ancestry
lemma; no semidirected root-lifting implication is thereby asserted.

Subdivision creates two fresh hidden ports. Original hidden vertices still
have an outgoing edge inside the enlarged region, including original
boundary attachment vertices that had internal children. Each new port's
only outgoing edge goes outside. This constructs the exact old
`RootComponent` contract, rather than adding it as a source assumption.

Maximality is used where necessary for the target's simple-graph class.
Two distinct exits cannot have the same outside target: adjoining that
target and the two edges preserves connectedness after any single edge
deletion. This would strictly enlarge the original bridgeless region.
Exact boundary cardinality alone would not justify that conclusion.

The root-LSA condition is preserved by mapping each original root-to-leaf
path avoiding a specified outside vertex into the replacement. All inside
vertices map to the new root; internal steps become stutters and outside
steps remain actual original edge occurrences. Ancestry rules out an
outside-to-inside step. The target LSA property is therefore derived from
the original LSA property, not assumed anew.

## 4. Both parameter-image directions

For each free original cut-edge matrix M, choose the uniform invariant row
mu, put nu = mu M, and choose an attained t in (0,1) sufficiently near one.
The matrices

    K = t I + (1-t) 1 mu,
    A = (M - (1-t) 1 nu) / t

are strictly positive, stochastic and equivariant, and K A = M exactly.
The two factorizations are independent. Conversely, the product of any
two admitted factors is admitted. Original inheritance is unchanged; each
new indegree-one edge receives weight one.

The actual assignment sum is preserved even when the original child has
other parents. The inserted coordinate y appears through

    sum_y K(x,y) [w A(y,z) + other-parent terms],

which is exactly the original child factor with M = K A. The other-parent
terms are retained by the row-sum-one identity, not discarded by a false
independence assumption. This is lifted to the full observed state sum.

Forward: factor the original two cut edges; replace the enlarged true
two-sink component using the earlier complete open-equivariant endpoint;
identify the resulting fork with two subdivisions of the final replacement;
collapse those two edges exactly.

Reverse: factor any final replacement parameter point into that fork;
relabel to the two-sink exterior; realize it on the original enlarged
component with the original inheritance fixed; collapse its two new ports
back to admitted original matrices.

Cut-edge matrices are free parameters and may change. This is NOT a theorem
preserving protected/fixed cut-edge matrices, shared matrices, an invariant
root fixed in advance, shared generators, embeddability, or continuous-time
rate constraints. Other exterior matrices can be retained by the underlying
hand construction, but the final source endpoint quantifies over the full
free independent matrix model.

## 5. Whole-theorem dependency graph

The previous two interfaces and ten unelaborated proof modules are retained:

    ClaimInterfaces -> EdgeIndexedInterfaces
    OpenProof -> DAGNormalization -> Switching -> TreeMarginals
    -> ContextGlue -> CutFactorization -> Relabeling -> SourceCut
    -> ComponentConstructor -> FullModel.

The new seven modules extend that chain, with actual proposed proof bodies:

1. `RootBlobEdgeSubdivision`: open factorization/product closure; one-state
   assignment elimination; original observed-law equality; both complete
   image directions; graph/weight admission; two successive subdivisions.
2. `RootBlobBoundaryGraph`: root and sink reachability; boundary enumeration;
   directed-excursion ancestry from the actual two-edge contract.
3. `RootBlobBoundaryAdapter`: explicit augmented incidences and ports;
   constructed two-sink component; composition with the earlier endpoint.
4. `RootBlobMaximalSource`: original binary and maximal bridgeless records;
   hiddenness; distinct nonroot exit sources; distinct outside exit targets.
5. `RootBlobBinaryReplacement`: actual port-suppressed target; explicit rank;
   graph/weight/binary/simple/LSA admission.
6. `RootBlobForkIdentification`: actual outside-vertex and outer-edge
   equivalences; full incidence and weight identification; intermediate
   admission; image transport; exact final port collapse.
7. `RootBlobMaximalEndpoint`: the complete original-class conjunction.

The selected exact image theorem is the last declaration, not a finite
algebra lemma or a conditional certificate whose graph construction remains
assumed. A source inspection found no `sorry`, `admit` or `axiom` declaration
in these seven new files. That inspection is not an elaboration result.

## 6. Primary-source relation and unchanged blocker

[Sullivant, Section 5](https://arxiv.org/html/2507.23056v2#S5) defines the
maximal edge-connected blob and asks for an exact root-blob converse after
proving inclusion and a limiting converse. His fork retains the two ports;
the present open-class subdivision equality identifies that fork with its
degree-two-suppressed replacement. His explicitly two-sink formulation is
kept separate from the additional maximal-blob adapter proved here.

[Brits et al., Definition 2.1 and Section 2.1](https://arxiv.org/html/2607.12919v3#S2.SS1)
provides the binary, simple, root-LSA class and counts boundary edges for a
maximal m-blob. The source endpoint now preserves all those listed rooted
graph properties. It does not import the broader Section 5.1 printed
two-boundary-vertex sub-blob class into the two-edge contract.

The literal arbitrary root-trapping 2-sub-blob problem remains blocked at
the definition/operation and semidirected-rooting adapter identified in
[SUBBLOB-DEFINITION-RECONCILIATION.md](SUBBLOB-DEFINITION-RECONCILIATION.md).
The three-boundary-edge witness is not a counterexample to a well-defined
model-image equality. No universal larger-root-blob/parallel-collapse lift
has been established. This checkpoint does not claim that full broader
published question has been solved.

The earlier bounded prior-work comparison, separate nucleotide/Fourier and
continuous-time domain results, and unresolved historical novelty remain
unchanged. No new G1/G2/G5 transfer or G3/G4 acceptance is claimed.

## 7. Review and remaining trust dependencies

The earlier maximal-root-blob hand adapter and exact two-edge excursion
lemma have scoped coordinating-assistant hand review recorded separately.
The coordinating assistant has also read the new final theorem boundary,
the maximal-region/NoParallel/RootLSA definitions and exposed target
admission chain. That was a static **statement/scope** review, not a
transitive review of every proof body, API syntax or elaboration.

All seventeen proof-source modules, both interfaces and their entire
dependency/import chain remain unelaborated. The principal remaining formal
obligation is an actual authorized Lean/kernel pass, including dependent
subtype equality, classical-choice definitions, finite-sum reindexing,
universe inference, tactic/API names and import resolution. Source inspection
uses Lean v4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`; no installed capability is inferred
from those source files.

Primary-paper graph terminology is represented explicitly by finite edge
incidences, induced-region connectedness after edge deletion, degrees and
avoiding paths. The finite DAG's natural-number rank is an auxiliary
topological representation, not a biological parameter. The representation
correspondence and mathematical proof still require external correctness
review; they are not mechanically parsed from the publications. Novelty
and all broader-model coverage remain separate from correctness.

All earlier artifacts are preserved. This packet adds attributed scientific
source and status only; it contains no private handoff or personal data.
