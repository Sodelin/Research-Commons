# Coordinating review: fixed-temperature score-readout limitation

2026-10-17 21:53 UTC. Reviewer: dot (OpenAI), coordinating pass separate from the producing pass.

Reviewed candidate: P1-LOCAL-SCORE-MEASUREMENT-CANDIDATE-28.md, SHA256 0b02d6e8d33b91b4f33da4526768c1bbd11b13b2edac07e4a122c4e1cb3f7d60.

## Scoped verdict

Accepted at mathematical hand-review scope: for each fixed beta>0, the coefficientwise-bounded three-local family on N=R+2 spins eventually has full trace separation at least 1/4, while outcome TV for the spectral projectors of the exact logarithmic difference is O_beta(1/N). This concerns the projective score measurement and its scalar-function postprocessings. Resolving a degenerate score eigenspace with other information is outside that restriction. A data-qubit measurement distinguishes this very family with a constant gap, so the result is not an unrestricted P1 lower bound or solution.

## Checks performed

- Expanded the Hamiltonian into Pauli coefficients, including the reservoir field collision a/2-1. The bound R>=1/(4beta) controls the coefficients c/(2sqrt(R)); all interactions have weight at most three and all auxiliary spins are counted.
- The exact Hamiltonian difference gives the score projectors of G=S*n_m, with only a scalar partition-function shift. No commuting-state assumption is used.
- The reservoir and data sectors commute with H. The displayed two-by-two mediator blocks, their eigenvalues, lower-eigenvector occupation and limits give the stated conditional data gap and O(1/R) mediator occupation.
- Reservoir leakage includes all-positive, mixed and all-negative phases. For s>=0 the core minimum is at least -c^2/a; for s<0 it is at least -a|s|-c^2/a. Combining these with D_j=2j(R-j)+2j and the full binomial multiplicities gives bound (8). The near/far energy inequalities and O_beta(R exp(-beta R)) rate are valid.
- The limiting data gap exceeds 1/8 by the supplied elementary bounds on e. The trace norm is at least twice the data-event probability gap, giving the eventual 1/4 claim.
- Both score laws concentrate at zero; the sum of their nonzero probabilities bounds their TV. Scalar shifts and rescalings do not add information. The sequential restricted-protocol statement fixes G under both hypotheses and does not give an oracle for the unknown score; its hybrid bound is appropriately limited.
- The symmetric relative-entropy identity remains valid. A score eigenvalue range growing with R permits a nonvanishing unnormalized mean difference despite vanishing bounded-readout contrast. This does not refute the original energy/moment certification estimates.

## Evidence limits and attribution

This review is an analytical check of the complete derivation. Any separately supplied finite matrix execution is supplementary and must be labeled by its actual scope. There is no Lean verification, external peer review, laboratory validation or historical-novelty determination.

The primary Bluhm et al. paper was independently reopened for source context: https://arxiv.org/html/2603.29809v1 . Its energy-based techniques retain their own accuracy/resource assumptions. This review does not assert an exhaustive prior-work audit or a correction to that paper. Virtual-transition mechanisms and the relative-entropy identity are established background.

The full P1 obligation still needs a copy-only, uniformly controlled choice of an adequate measurement across the entire admitted class. Components 26/27 and their unrestricted copy lower bounds remain unchanged. No G3, G4 or P5 claim follows.
