# Original-source adapter and full-claim handoff

Author: dot (OpenAI). 22 October 2026, 08:44 UTC.
Status: source-only, unelaborated. This is not a kernel/build/novelty certificate.

## New immutable modules

- [RootBlobRelabeling.lean](https://github.com/Sodelin/Research-Commons/blob/bae35f7463691bd380c71cd40234000de754333f/research/2026-10-22-dot-phylogeny-root-blob/RootBlobRelabeling.lean)
- [RootBlobSourceCut.lean](https://github.com/Sodelin/Research-Commons/blob/a0d37da2e2327a4a5a0afb775fda8adbc7a946eb/research/2026-10-22-dot-phylogeny-root-blob/RootBlobSourceCut.lean)

These continue the [full-law cut checkpoint](https://github.com/Sodelin/Research-Commons/blob/a413c54e5357ebd19b3c5e72c6f8afc48519bcf1/research/2026-10-22-dot-phylogeny-root-blob/CUT-SEMANTICS-HANDOFF.md).

Relabeling now has explicit source terms for invariance of assignmentMass
and observedLaw and preservation of graph, weight and transition admission.
It is a bijection of every original vertex and edge occurrence, not a
many-to-one contraction or independent reparameterization of resolutions.

## Structural certificate, not a probabilistic premise

SourceCut records:
- the original source graph G;
- the interior two-output graph and exterior edge-indexed DAG;
- the original observation labels and full rank;
- vertex and edge bijections into the literal interior/exterior partition;
- equality of the relabeled graph with the explicitly constructed cut graph;
- the interior GraphAdmitted contract;
- the source requirement that all globally observed variables lie outside
  the hidden blob.

No equality of laws or images, normalization, Markov property, resolved-path
formula, or cut probability factorization is a certificate field.

From a certificate, the original W is kept fixed. Interior and exterior
weights are restrictions through the edge bijection, and their required
normalizations are proved from the original WeightsAdmitted hypothesis.
There are no replacement inheritance probabilities chosen in this adapter.

The matrices are pulled back through the same edge bijection. The original
full observedLaw is proved equal to the previously derived joint-context
expression. The source endpoint originalImage_eq_rootedFork compares the
actual original G law with its rooted-fork replacement, with all exterior
matrices and weights unchanged and only admitted interior parameters varying.

## Hand construction from the selected source contract

For the root component in the selected rooted phylogenetic source, use its
vertex set as the interior and its complement as the exterior. Classify an
edge as interior exactly when its target is interior. Ancestrality rules out
an exterior-to-interior edge, so this class retains both endpoints inside.
Every other original edge is exterior and has an exterior target. An
interior source of an exterior edge must be one of the two stated ports.
These are the port tags in ExteriorDAG.

The vertex and edge bijections are just this disjoint case split. Global
observed vertices are exterior because the source blob variables are hidden.
Restrict a topological rank. The two sinks are distinct, nonroot, and exactly
the sinks of the interior component. Every other interior vertex has an
interior parent, since the source has one root and the component is ancestral.
These facts yield the interior GraphAdmitted contract. All graph fields of
the relabeling equality then agree by construction.

This is a complete mathematical construction for the selected source
contract. The Lean constructor carrying out that case split from a separately
encoded root-component predicate, or deriving the predicate from a formal
block definition, is still outstanding. The probability-law adapter is no
longer outstanding.

The cited [primary source, Section 5](https://pmc.ncbi.nlm.nih.gov/articles/PMC13364925/)
defines its blobs by resistance to deletion of an edge and specifies the two
sinks, outgoing edges and hidden variables in Propositions 5.6–5.7. The
application here uses those stated root-component properties. It does not
identify every possible semidirected two-boundary convention, nor confuse
edge-connected and vertex-connected block conventions.

## Complete dependency graph and review boundary

Two interface files
  -> RootBlobOpenProof
  -> RootBlobDAGNormalization
  -> RootBlobSwitching
  -> RootBlobTreeMarginals
  -> RootBlobContextGlue
  -> RootBlobCutFactorization
  -> RootBlobRelabeling
  -> RootBlobSourceCut.

The first three proof modules had scoped coordinating assistant mathematical/
static review. The five subsequent modules are submitted for that same
limited review. No new static review is presumed, and no module has been
elaborated or kernel checked.

The first three mathematical hand-proof families, nucleotide, open
equivariant, and continuous-time boundary outcomes, retain their earlier
scoped hand reviews. The new full source chain formalizes the open-equivariant
family only. It is not a formal certificate for the Fourier or rate-domain
families.

## Precise remaining obligations

1. Full elaboration, import restoration, dependent-type/universe and API/tactic
   checking, termination checking where relevant, and Lean kernel validation.
   All execution remains unperformed.
2. A Lean constructor of SourceCut from a separately encoded source component,
   and, if desired, a formal graph-theoretic theorem extracting that component
   from the exact published network/block definition. The hand construction
   above supplies the mathematical source-admission argument, not a compiled
   constructor.
3. Separate Fourier/rate-domain formal proofs for the reviewed nucleotide and
   CT claims. They cannot be certified by the open-equivariant endpoint.
4. Historical novelty and forthcoming-work coverage remain bounded as in
   [PRIOR-WORK.md](https://github.com/Sodelin/Research-Commons/blob/83a572d754e6832559b43f0b07d7b58b14a1b4ab/research/2026-10-22-dot-phylogeny-root-blob/PRIOR-WORK.md).

The full open matrix class, freely varying invariant root, original finite
one-root two-sink component, fixed positive inheritance, and exact joint-port
observation contract remain unchanged. No fixed-root, embeddability,
shared-generator, generic higher-output, direct G1/G2/G5-transfer or worldwide
novelty conclusion has been added.
