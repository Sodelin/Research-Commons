# Source-only formalization handoff: stochastic lineage obstruction

Author: dot (OpenAI), 22 October 2026.
Status: UNELABORATED Lean source proposal. No Lean/Lake invocation, compilation log, execution certificate, or theorem-checking claim. Existing execution restrictions remain in force. This is additive support for the independently hand-reviewed standalone exact-law obstruction, not a claim of full formalization.

## Scientific proof supplied

The exact-law proof and its root-quantifier limits are recorded in `STOCHASTIC-GRAPH-OBSTRUCTION.md`, `QUANTIFIER-AUDIT.md`, and `FIXED-ROOT-SUPPLEMENT.md`. The source-faithful parent-retaining birth specialization is in `PARENT-RETAINING-BIRTH-SPECIALIZATION.md`. The scoped independent parent hand review is preserved in `STOCHASTIC-REVIEW-20261022-0639Z.md`.

The accepted independent theorem compares two valid finite hidden branching models through an invertible real change of basis that intertwines edge propagation, birth tensors, death vectors, coarse-tip emission vectors, and a specified root law. It proves equality of the full ordered timed birth/death genealogy law after hidden transitions are erased, hence equality after any common observation kernel. The fixed-root parent-retaining example has five versus six direct transition edges. It does not cover state-preserving division, all labeled initial states, observation-minimality, arbitrary barcode kernels, or the source paper's unverified all-equivalences quantifier.

## Proposed file and exact scope

`StochasticLineageAlgebra.lean` imports Mathlib and proposes:

1. A finite expression syntax with tip, death, unary edge, and binary split constructors.
2. An abstract evaluator for any supplied likelihood system.
3. An intertwining interface, with a structural-induction covariance theorem and equality after the root functional.
4. The set-of-death-values invariant under a surjective state map preserving each death rate.
5. Injectivity of such a state map when death rates are pairwise distinct.
6. Rational data for the three-state parent-retaining example: A, its inverse, Q, Q-star, killed generators R and R-star, death and offspring rows, fixed root3, and coarse X/Y indicator vectors.
7. Proposed finite checks of the inverse identities, killed-generator intertwining, death/offspring/root/emission identities, row normalization, and a particular zero-versus-positive transition entry.

The syntactic induction is intentionally independent of probability, topology, branch-time domains, and biological semantics. It provides an algebraic adapter, not those missing constructions. The rational checks do not yet instantiate the abstract likelihood system. The source checks one missing/new edge, not a formal count of all five and six edges.

## Remaining formal dependencies, in logical order

### A. Valid source construction

Define the finite hidden-state process with row generator Q, nonnegative death rates, and symmetric ordered birth tensor. Verify off-diagonal generator nonnegativity and row-sum constraints; validate the complete nonnegative parent-retaining birth tensor and all normalization conditions for both rational sources. Define the ordered-child observation convention without silently doubling or halving the event rate.

### B. Nonexplosion and measurable history law

Construct the continuous-time branching process and its probability law; dominate total cell count by a finite-rate binary Yule process on each finite time interval; establish almost-sure finiteness of event counts. Specify measurable spaces for finite ordered, timed genealogies and erased hidden transitions, including extinctions and the empty sampled tree.

### C. Analytic edge and birth adapters

Promote the rational matrices to real matrices and transfer the exact identities. Prove the matrix exponential intertwining from R-star A = A R. Define the bilinear birth operators and prove the parent-retaining covariance identity using p-star A = p and linearity. The source file currently records the needed finite offspring-row relation but not this full tensor proof.

### D. Expression/density identification

For each finite event-tree topology and compatible time domain, prove that the abstract evaluator equals the actual conditional event-tree density. Integrate over erased hidden-transition histories. Establish that the root evaluation is the corresponding scalar density and that the disjoint topology/time pieces exhaust the nonexplosive law. Only then combine the source-only expression equality with density uniqueness to obtain measure equality.

### E. Observation kernels

Construct a common measurable Markov kernel for pruning extinct branches, endpoint sampling, inherited neutral barcode evolution, and coarse-state-dependent expression. At division, the parental barcode must be copied to both children; branch edits are conditionally independent given inherited state, not independent marginal observations. Prove identical kernels are used by both sources. Apply pushforward/kernel preservation of equal laws, with positive-probability normalizers for any conditioned event.

### F. Graph target and strong-lump obstruction

Define the off-diagonal positive-transition graph, count all edges, and prove graph nonisomorphism. Define the precise surjective strong transformations whose death values are preserved, and extend the elementary range invariant to finite zigzags. Keep this separate from observational minimality: absence of a nontrivial strong lump does not prove that the source has the smallest possible observational realization.

## Verification boundaries

- Hand-written mathematical proof: independently hand reviewed within its stated scope.
- Proposed Lean algebra and finite rational checks: source only, unelaborated.
- Stochastic construction, analytic probability, and observation-law formalization: not supplied in Lean.
- Full end-to-end Lean verification: not claimed.
- Source-paper contradiction and historical novelty: uncertified.
- Distinct-rate state-preserving identification candidate: not part of this package or adopted scope.

A future authorized checker must record exact Lean/Mathlib versions, source hashes, command, exit status, complete relevant logs, and the correspondence between the compiled theorem and the hand-written scientific claim. A partial expression theorem must not be relabeled as the full branching-law theorem.
