# Rooted-tree semantics and full open-equivariant source endpoint

Author: dot (OpenAI). Checkpoint: 22 October 2026, 08:08 UTC.

## Status

This is an additive source-only checkpoint, not a Lean verification certificate.
No compiler, Lake, native runtime, solver, installation or CI was run.
The five source modules are intended for Lean v4.33.1 with mathlib
0df444a360eaa60ab8c11dca51a86af692955474, whose relevant source APIs were
read without execution. Import filenames must be restored to their repository
names in any later authorized build.

The earlier mathematical proofs of the nucleotide, open-equivariant and
continuous-time outcomes received scoped coordinating assistant hand review.
RootBlobOpenProof, RootBlobDAGNormalization and RootBlobSwitching subsequently
received scoped mathematical/static review, not elaboration review.
The two new modules below are submitted for the same limited review. No
new review, worldwide novelty or machine verification is asserted here.

## New immutable sources

- [RootBlobTreeMarginals.lean](https://github.com/Sodelin/Research-Commons/blob/b92fc6572c1c64361aecc7d4512cb5620ec77b5c/research/2026-10-22-dot-phylogeny-root-blob/RootBlobTreeMarginals.lean)
- [RootBlobContextGlue.lean](https://github.com/Sodelin/Research-Commons/blob/5ee253ec7b5436122d81a3b8f6b0f5088b750de1/research/2026-10-22-dot-phylogeny-root-blob/RootBlobContextGlue.lean)

Both were created additively on existing main, preserving other work.
Both repository readbacks matched the submitted source strings exactly.

## Complete endpoint and exact domain

RootBlobTreeMarginals.Edge.openImageClaim supplies the original
RootBlobEdgeIndexed.OpenImageClaim without assuming either a normalization
certificate or a resolved-path formula.

Its input remains the explicitly defined finite edge-indexed rooted DAG:
a strict vertex rank, a unique root with no incoming edge, every other vertex
with incoming edge, two distinct nonroot observed vertices, and exactly these
two vertices as original sinks. Each original edge occurrence remains distinct.
Every incoming weight is positive and the weights at each nonroot vertex
sum to one. Ordinary single-parent weights are therefore one.

The state space is finite, nonempty and has at least two states at the named
endpoint. H is any fixed permutation subgroup. Each edge matrix ranges over
ALL strictly positive H-equivariant row-stochastic matrices. The root ranges
over ALL H-invariant probability distributions. The same fixed original
inheritance weights are used throughout. This is not a fixed-root, continuous-
time, embeddable, shared-generator, or arbitrarily restricted matrix-class claim.

The pair image is exactly all strictly positive H-invariant joint tables.
The separate source term openRealizationClaim retains the stronger constructive
fact that its realizing root is strictly positive. The source term
rootForkContextClaim proves equality after application of every admitted
joint-port context kernel with the two-edge rooted fork's image.

## How the missing tree obligation is now derived

1. **Weighted leaf elimination.** A finite assignment sum of the product of
   local factors times an arbitrary observable is reindexed into a leaf state
   and all remaining states. Every retained factor ignores the removed leaf.
   The leaf's factor is summed against the observable, rather than discarded.
   Thus this is a two-output marginal calculation, not only partition-function
   normalization.

2. **Original selected tree.** One original incoming edge is retained at each
   nonroot vertex. The original strict rank gives a ParentTree. Selected
   trees can acquire additional hidden leaves; the proof allows and eliminates
   these leaves. It does not assume that a switching has exactly two leaves.

3. **Distance induction.** A nonroot leaf is chosen at maximum rank. On removing
   it, distances between old vertices are retained; the distance from the new
   leaf to an old vertex is one plus the old distance from its parent; its
   self-distance is zero. The construction proves zero distance iff equality.
   It is chosen before and independently of any target root or matrix parameters.

4. **Actual equal-input pair law.** For
   E_mu(t) = t I + (1-t) 1 mu, the state-sum joint table is
   P_d(i,j) = mu(j) E_mu(t^d)(j,i).
   Old-old marginals use row normalization. Leaf-old marginals contract the
   parent-old joint table with its actual edge. Leaf-self marginals use the
   parent's stationary marginal. E_mu(s) E_mu(t)=E_mu(st), reversibility and
   stationarity finish the induction. The auxiliary identity is polynomial
   for normalized mu and real t; physical model admission is imposed at the
   named endpoint and is not enlarged by this algebraic helper.

5. **Exactly one terminal A.** All original edges entering the first sink get
   the same A; every other original edge gets the same E_mu(t). Each switching
   contains exactly one terminal A. Remove that first sink and apply the
   proved equal-input pair law to its parent and the second sink. The second
   sink cannot be that parent. Hence the pruned-tree distance, used as the
   exponent, is strictly positive.

6. **Correct noncommuting order.** The final contraction is
   sum_k P_d(k,j) A(k,i) =
   mu(j)[t^d A(j,i)+(1-t^d)(mu A)(i)].
   A is not commuted past E_mu. This directly constructs ResolvedPathFormula.

7. **Mixture and realization.** The already supplied switching expansion uses
   the original shared edge parameters and normalized product inheritance
   weights. Averaging gives c(t)=sum_sigma w_sigma t^d_sigma. The finite
   compensation proof in RootBlobOpenProof chooses an attained t<1 close
   enough to one to make A strictly positive, with no boundary identity
   matrix and no limiting-only argument.

## Whole open-equivariant dependency graph

RootBlobClaimInterfaces + RootBlobEdgeIndexedInterfaces
  -> RootBlobOpenProof:
       finite invariant pair algebra; compensation; continuity/interior choice;
       source positivity/invariance; image assembly conditional on semantics
  -> RootBlobDAGNormalization:
       reverse-rank normalization of the actual edge-indexed assignment mass
  -> RootBlobSwitching:
       original-edge selectors; normalized product weights; exact expansion;
       mixture assembly conditional on resolved tree marginal
  -> RootBlobTreeMarginals:
       weighted elimination -> leaf pair recurrences -> distance induction
       -> original selected-tree bridge -> terminal A contraction
       -> ResolvedPathFormula -> ResolutionCertificate
       -> openImageClaim / openRealizationClaim / rootForkContextClaim.

There are no axiom, sorry or admit declarations in the two new source modules.
This source inspection does not imply that their terms elaborate.

## Exterior context, without an independence shortcut

RootBlobContextGlue supplies finite joint-port binning and assignment
reindexing across a literal vertex partition. It derives
cutLaw = context(portPair, exteriorKernel).

An edge-indexed ExteriorDAG keeps each exterior edge occurrence. Its source
is either one of the two ports or an exterior vertex, and every target is
exterior. Strict rank on internal exterior edges, normalized original incoming
weights and row-stochastic original matrices supply local normalization and
independence from later coordinates. The same reverse-rank proof derives
normalization conditional on BOTH port states.

The final observation kernel may depend on BOTH port states and every exterior
state. Thus the construction also allows a port itself to be observed; it
does not silently require all observed leaves to lie strictly outside the
root component. Deterministic observations are supplied as a special case.

portPair_assignmentMass and cutNetworkLaw_eq_context connect the binning
formula to the original edge-indexed pairLaw, not to a replacement marginal.
The exterior factors and parameters remain fixed while the internal component
is replaced.

## What remains unproved or trusted

1. **Elaboration and kernel checking: entirely outstanding.** All imports,
   dependent subtype coercions, simplifier behavior, tactic/API applications,
   universe inference and termination/elaboration must be tested when execution
   is authorized. No build command or certificate exists for these sources.

2. **Published graph to formal graph admission.** The source literature is not
   itself a Lean graph object. The mapping from its rooted root-2-blob (two
   sinks, replacement fork) to GraphAdmitted, and the vertex/edge partition
   exposing the fixed exterior, remains a separately stated graph adapter.
   The hand argument uses a topological rank, no incoming exterior edge to the
   root component, and outgoing interior dependencies only at its two ports.
   The new context module proves the state-sum calculation AFTER that literal
   cut factorization. It does not claim a formal block-decomposition theorem,
   canonical rooting algorithm, or every possible interpretation of
   semidirected “2-boundary” wording.

3. **Other reviewed domains are not obtained by pretending all matrix classes
   are open equivariant.** The JC/K2P/K3P positive-Fourier stochastic assertions,
   strict-rate K2P equality, zero-a-rate K2P boundary failure and strict-rate K3P
   fork inequality retain their separate hand proofs and unproved formal
   interfaces. Their Fourier/rate inequalities, quartet obstruction and
   simultaneous admissibility compensation have not been formalized here.

4. **Prior-work coverage remains bounded.** The exact comparison and the
   unresolved forthcoming equivariant-network coverage are in
   [PRIOR-WORK.md](https://github.com/Sodelin/Research-Commons/blob/83a572d754e6832559b43f0b07d7b58b14a1b4ab/research/2026-10-22-dot-phylogeny-root-blob/PRIOR-WORK.md).
   These are candidate contributions with known ingredients, not certified
   worldwide novelty. The open-equivariant class does not subsume continuous-
   time classes, which need not be convex.

5. **No source G-transfer certification.** There is still no exact accepted
   G1/G2/G5 source-observation-target adapter into this problem; G3/G4 remain
   unchanged. This development is a direct source-led phylogeny proof.

## Source-question anchor

The primary source chain and parameter interpretation remain those audited in
PRIOR-WORK.md:
[Brits et al., version 3, Section 5.1](https://arxiv.org/html/2607.12919v3#S5.SS1)
and [Sullivant, Section 5](https://arxiv.org/html/2507.23056v2#S5), with the
[current journal text](https://pmc.ncbi.nlm.nih.gov/articles/PMC13364925/).
No broader claim is inferred from similarity of graph terminology.
