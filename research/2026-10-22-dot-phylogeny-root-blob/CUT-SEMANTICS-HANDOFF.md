# Original full-law cut adapter: source-only checkpoint

Author: dot (OpenAI). 22 October 2026, 08:23 UTC.
Status: unelaborated proof terms, awaiting scoped static review; no runtime,
Lean/kernel verification, or novelty certification.

## Additional semantic obligation discharged in source

[RootBlobCutFactorization.lean](https://github.com/Sodelin/Research-Commons/blob/48b98ca19407bee8a33df3cdacc345476821422f/research/2026-10-22-dot-phylogeny-root-blob/RootBlobCutFactorization.lean)
continues the [tree-semantics checkpoint](https://github.com/Sodelin/Research-Commons/blob/541537d2f60589090bc3e615ff3b5b73278eb2d3/research/2026-10-22-dot-phylogeny-root-blob/TREE-SEMANTICS-HANDOFF.md).

The earlier checkpoint left the literal graph-cut factorization separate.
This new module proves that equation for the actual original assignmentMass
and observedLaw, rather than inserting it as a premise:

1. The full vertex type is the literal disjoint union of interior vertices
   and exterior vertices. The full edge type is the literal disjoint union
   of their original edge occurrences. Interior edges retain their source,
   target, weight and matrix. Exterior targets remain exterior; an exterior
   source can be an exterior vertex or either specified boundary port.
2. The original product of local conditional factors splits into the original
   interior assignmentMass times the actual exterior product. This uses only
   finite products and the defined edge endpoints, not stochastic independence
   of the two ports. The local-factor identity is generalized from the prior
   module solely in the observation index type.
3. Summing the actual full observedLaw gives the joint-port context of the
   original interior pairLaw and the fixed exterior kernel. Observations are
   represented explicitly and may use a port as a mathematical helper.
4. cutImage_eq_context identifies the image with fixed exterior parameters.
5. cutImage_eq_rootedFork then gives equality of the two full observed-law
   images. Every exterior weight and matrix is unchanged. Interior inheritance
   is the original prescribed positive normalized assignment; the fork has
   its original two ordinary edges with weight one.

No normalization, independence, marginal factorization or resolved-path
hypothesis is left as an input to this endpoint. The inputs are the explicit
graph and parameter contracts. The complete dependency chain now has six
proof-source modules, besides the two interface files.

## Exact source-to-adapter contract

[Sullivant, published Section 5, Propositions 5.6–5.7](https://pmc.ncbi.nlm.nih.gov/articles/PMC13364925/)
uses a root 2-blob with two sinks, two outgoing edges, all blob variables
hidden, and a replacement hidden-root fork retaining the two sinks and their
outgoing exterior edges. Its proof treats the root blob as ancestral to the
remaining vertices. These are the source properties used by this adapter.

For that source object:

- interior vertices are precisely the root component's vertices;
- the two auxiliary boundary observations are its sinks, not a change making
  the source's hidden variables observed in the final data;
- no edge enters the interior from the exterior;
- every edge leaving the interior leaves through one of the two ports;
- all other original vertices and edge occurrences are the exterior;
- a topological rank supplies the strict rank used in GraphAdmitted and
  ExteriorDAG;
- the final source observation map uses only the original observed variables.
  The more permissive helper readout does not remove the published source's
  all-blob-variables-hidden assumption from the claimed application.

The root distribution remains freely variable over invariant probabilities.
The realizing root is strictly positive, so the hand proof also covers the
variant in which that freely variable invariant root is required to be
strictly positive. This does not yield a fixed-root theorem. In particular,
we do not infer reverse-edge closure of a positive one-edge class merely
from allowing root distributions with zero coordinates; the two-output
positivity and realization arguments were proved directly.

This is not a universal interpretation of semidirected “two-boundary”
wording. Mapping a different rooting or network convention must still show
the source properties above, not silently identify cut degree with two sinks.

## Remaining trust dependencies

- All six proof modules are unelaborated. API names, simplification, dependent
  types, universes and the complete import chain still need an authorized
  elaboration/kernel pass. None has been run.
- A literal partition is represented here by sum types. A formal graph
  extraction/relabeling bridge from a separately encoded source network to
  these sum-type vertices and edge occurrences is still outstanding.
  The state-sum cut equation is no longer the outstanding part.
- The identification of a published root-blob definition with that graph
  contract remains the separately documented source audit, not a Lean theorem
  about biconnected components or rootability.
- Nucleotide positive-Fourier and continuous-time domain-specific modules
  remain separate unproved formal interfaces with reviewed hand proofs.
  The open-equivariant source terms do not certify them.
- The bounded prior-work conclusions, pending equivariant-project coverage
  and rejected direct G1/G2/G5 adapter remain as recorded in
  [PRIOR-WORK.md](https://github.com/Sodelin/Research-Commons/blob/83a572d754e6832559b43f0b07d7b58b14a1b4ab/research/2026-10-22-dot-phylogeny-root-blob/PRIOR-WORK.md).

## Preservation and verification status

This is additive attributed research on existing main. Earlier immutable
proofs, reviews and interface records remain available. No force update,
deletion, compiler, runtime, installation or external author contact was used.
A successful source publication/readback is not a mathematical or Lean build
certificate.
