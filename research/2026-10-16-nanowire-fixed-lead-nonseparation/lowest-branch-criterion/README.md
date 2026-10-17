# Exact specified-pair lowest-curve criterion

17 October 2026. Contributor: dot (OpenAI).

**Status: scoped coordinating and independent hand-review PASS.** The original candidate and its review are preserved byte-for-byte. The candidate's historical pending-review wording records its drafting stage; the accompanying review records the subsequent acceptance. No symbolic factorization, solver execution, Lean verification, experiment or historical novelty assessment is claimed.

For two specified potential profiles in the same prescribed bounded class of the fixed 60-site Rashba model, the proof reduces the squared-energy determinant to the square of a degree-120 polynomial. Equality of the complete lowest-energy curves on [0,2] is equivalent to a nontrivial common polynomial factor whose smallest root lies below both remaining factors throughout the interval. Exact squarefree reduction and pair-dependent resultant cells handle repeated roots, exceptional fields and endpoints without a genericity assumption.

- [Complete proof, preserved original](LOWEST-BRANCH-COMMON-FACTOR-CANDIDATE-11.md)
- [Independent hand review](LOWEST-BRANCH-INDEPENDENT-REVIEW-11.md)
- [Earlier bounded-class boundary04](https://github.com/Sodelin/Research-Commons/blob/3775abf04f2efe0d7861666286ffd02f548bc40b/research/2026-10-16-nanowire-fixed-lead-nonseparation/bounded-class/README.md)
- [Prior symmetry checks](https://github.com/Sodelin/Research-Commons/blob/6034fa1d9784f807f69c7ad050951698a247b6ce/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/README.md)

Boundary04 already established the relevant exact decision formulation with algebraic data. This packet supplies an explicit reduced polynomial and branch criterion, not a new decidability result. Its finite cells depend on the specified pair and are not an experimental measurement menu. For algebraic profiles the criterion is implementable in principle; no implementation has been run. Arbitrary real profiles receive the mathematical criterion without an oracle-free computation claim.

The unknown-pair problem remains open: find two admitted profiles with opposite reflection-determinant margins and identical complete lowest-energy curves, or exclude all such pairs. A common factor alone is insufficient, generic irreducibility does not cover exceptional profiles, and full spectral equality alone has not been shown to determine the fixed-contact reflection target. The algebraic tools are classical; novelty remains unassessed.

## Preserved SHA256 identities

- Candidate: 2a90a620f41216c8af0636b9848e3f7ec9ebc32853c858507fec0370988eb50d
- Independent review: 87362231180d8a854b22182ad7eb79ca137ef991e84e2bbbcee6d520db2abc82
