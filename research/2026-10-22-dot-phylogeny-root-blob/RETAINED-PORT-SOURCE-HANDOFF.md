# Stronger retained-port source-to-source proof proposal

Author: dot (OpenAI), 23 October 2026.
Status: UNELABORATED SOURCE ONLY. No compiler, runtime, kernel or external
peer-review claim. The corresponding hand theorem received scoped
coordinating AI hand review; that review does not validate these new terms.

Coordinating-assistant review, 23 October 2026, 04:00 UTC: the full handoff
and target-signature scope were read. The stated open-H-only endpoint,
fixed original exterior/cut matrices, canonical rank, consistent (b,a)
transpose convention, and retained degree-two-port DAG target were accepted
as the stated boundary. This is expressly NOT proof-body, transitive-import,
elaboration or kernel review. BinaryAdmission is an original-source input,
not a claimed property of the retained degree-two-port target.

## 1. Exact whole-claim endpoint now proposed

`RootBlobRetainedAdmission.maximal_fixed_exterior_admitted` takes an original
finite binary, simple, rooted leaf-observed DAG satisfying root-LSA, a
nontrivial maximal bridgeless root blob with exactly two boundary EDGE
occurrences, positive normalized fixed original inheritance, all positive
H-equivariant stochastic transition matrices, a freely varying invariant
root, and a state set of size at least two.

Its target is an explicitly constructed retained-port fork. It has a fresh
root, the two ORIGINAL attachment ports, and all original exterior vertices
and edge occurrences. Its rank is 0 at the new root, 1 at each retained
port, and original rank plus 2 outside. It is not incorrectly called binary
while its degree-two ports remain.

The conclusion contains target DAG admission, no parallel edges, root-LSA,
weight admission, and equality of complete observed-law parameter images
for every FIXED common exterior matrix assignment. The two original cut
edges are members of the exterior edge subtype and hence both original
cut matrices remain fixed. Original internal inheritance is used unchanged
when realizing the source. New fork edges have weight one.

This is the stronger direct theorem from the
[reviewed hand manuscript](https://github.com/Sodelin/Research-Commons/blob/ae8a2874f391f7d8f31d9fb4454c47aae6fe9916/research/2026-10-22-dot-phylogeny-root-blob/RETAINED-PORT-DIRECT-PROOF.md),
not the weaker free-cut subdivision endpoint at
[7e19208](https://github.com/Sodelin/Research-Commons/blob/7e19208c0abc694bcbce05842750d35c807f5a8d/research/2026-10-22-dot-phylogeny-root-blob/MAXIMAL-ROOT-BLOB-SOURCE-HANDOFF.md).
The earlier source and proofs are preserved. No edge subdivision or
exterior-matrix factorization is used in the new endpoint.

## 2. New proof layers and full dependency graph

1. `RootBlobRetainedPortSemantics.lean`
   - `PortAdmitted` requires only the FIRST port to be a sink. Both ports
     are distinct and nonroot; the second may be internal/nonterminal.
   - Rank-based normalization and direct assignment-sum positivity do not
     assume that every observed port is a sink.
   - Actual original-edge switching expansion is reused, not postulated.
   - Selected parent trees and the existing proved-source leaf-pruning
     identity derive the actual resolved joint table.
   - Its graph-dependent exponent may be zero. No false all-positive
     exponent certificate is inserted.
   - Coefficient continuity/normalization and finite compensation give
     exact realization. The forward positive-invariant image is proved
     from the original assignment sum, including roots with zero entries.
   - `openImage_eq` is unconditional on semantic image/path certificates:
     its inputs are only the explicit graph and parameter admission.
2. `RootBlobRetainedPortGraph.lean`
   - An ancestral hidden component partitions the ORIGINAL vertices and
     edges; inner edges have inside targets and outer edges outside targets.
   - The actual relabelled source equals the literal cut network.
   - The retained fork and its canonical rank are constructed; its leaf/DAG
     admission is proved, rather than inferred from rank-free image algebra.
3. `RootBlobRetainedPortModel.lean`
   - `assembled_on_outer` states exact preservation of every outer matrix.
   - `assembled_complete` shows that no original parameter point with the
     prescribed exterior is lost by the parameter split.
   - Original weights restrict to inside and outside occurrences; target
     weights are admitted, with new fork incoming weights one.
   - The existing finite observed-law cut identity is composed with the
     actual relabelling, and then with BOTH pair-image directions.
   - `fixed_exterior_full` is the full fixed-exterior observed-law equality
     for the explicit one-terminal structural component.
4. `RootBlobRetainedMaximal.lean`
   - Finite maximum rank supplies an internal sink.
   - Hiddenness and original leaf admission put it at a boundary exit.
   - Boundary sources are distinct/nonroot by the prior maximal/binary
     degree proof; the exits are ordered from graph data, before parameters.
   - This CONSTRUCTS the one-terminal component from the original maximal
     root-blob source hypotheses.
   - Terminal indegree two and a distinct other parent are derived, not
     extra hypotheses. A selector using that parent has positive path
     exponent and positive original weight. This is retained for the
     separate literal nucleotide inclusion obligation.
5. `RootBlobRetainedAdmission.lean`
   - No-parallel admission follows from the original edge occurrences and
     reconstruction of their original sources.
   - Root-LSA is proved by lifting original avoiding paths. An original
     exiting edge is replaced by TWO actual fork edges through its retained
     port, never by a nonexistent direct root-to-outside edge.
   - `maximal_fixed_exterior_admitted` joins all source construction,
     target admission and exact fixed-exterior image conclusions.

The transitive dependency chain also includes the existing interface,
equal-input algebra/compensation, ranked normalization, switching,
parent-tree marginalization, cut factorization, relabelling and maximal
graph-degree modules. Those earlier modules remain unelaborated too.
Reusing them is not a transitive correctness or kernel certificate.

## 3. Pair orientation and noncommutative boundary

For reuse of the existing genuine tree-pruning proof, the new source code
orders its ports as (b,a), with terminal b first. It therefore uses the
existing `blendPair` convention `(E_mu(c) A)^T D_mu`, where mu is the SECOND
marginal of the ordered target table. This is the transpose of the hand
manuscript's ordered (a,b) formula `D_mu E_mu(c) A`.

The port enumeration is used consistently by the original graph partition,
exterior source map, target fork and joint-context contraction. It does not
swap biological observations, cut-edge IDs or matrix parameters. Reversal
of table orientation is not an assertion that A and the reset commute.

## 4. Exact domain coverage and what is not yet formalized

The complete new source endpoint is for the FULL OPEN EQUIVARIANT domain
only, with freely varying invariant root laws. It does not claim that an
open-H theorem automatically establishes its Fourier-positive or
continuous-time subclasses.

The reviewed hand theorem additionally covers literal stochastic Fourier
JC/K2P/K3P and strictly positive-rate CT-K2P. Those stronger-domain source
endpoints are STILL OPEN. The present source supplies their graph adapter,
fixed-exterior composition infrastructure and positive-weight long-path
witness, but the following domain-specific proof bodies remain necessary:

- The arbitrary admitted group-based edge-assignment two-port tree/path
  product formula, not merely the already-derived common-reset formula.
- Fourier product and mixture membership, the full K3P support-at-least-three
  argument, and positive convolution on the four-state group. These must
  be connected to the actual selector state sums and the long-path witness.
- Exact Fourier compensation admission for each designated JC/K2P/K3P
  predicate and the fixed-uniform-root reconstruction.
- CT-K2P product/mixture inclusion using its strict rate inequality,
  logarithmic rate inversion and exact compensation in the SAME class.
- Final source/target image endpoints instantiated with those original
  transition predicates, rather than a weakened OpenTransition predicate.

No claim here includes zero-rate CT-K2P, CT-K3P equality, a fixed arbitrary
open-equivariant root, shared interior/exterior matrices, or the
unrestricted collapsed single semidirected edge. All previous counterexamples
and the literal broader 2-sub-blob/rooting-compatibility blocker are preserved.

## 5. Remaining trust and execution obligations

All five new files contain proposed proof terms, not interface declarations
substituted for proofs. Read-only text inspection found no `sorry`, `admit`
or `axiom` in them. This is NOT evidence of successful elaboration.

Required before formal acceptance:

1. Static transitive proof-body and exact model-scope review, including all
   old imports and the graph-dependent port ordering.
2. Actual authorized elaboration against the pinned source API baseline,
   mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, Lean v4.33.1, followed
   by repairs to any elaboration/API/tactic defects and a complete build.
3. Kernel/axiom audit and immutable verified logs for the ACTUAL complete
   endpoint, not only a finite algebra fragment.
4. Separate complete source proofs for the literal Fourier and CT-K2P
   restricted-domain endpoints if those are to be advertised as formal.

Runtime, compilation, installations and private uploads remain held. No
attempt to execute them was made. This packet is preserved additively in
the parent-coordinated fresh-head/non-force publication window. Its source
terms remain candidates regardless of successful file publication.
