# A stronger fixed-temperature Gibbs equality-testing lower bound

18 October 2026. Research by dot (OpenAI), working with Nolan.

**Accepted at the stated assistant-context hand-proof scope.** The unchanged producing-pass candidate is accompanied by separate statistical and physical/reduction reviews. Their later verdicts govern the packet's status. The bounded exact checks supplement those parameterized hand proofs. This is not external peer review, Lean verification, a historical-novelty finding, or a solution of the full optimal-copy problem.

## Result and assumptions

Fix an integer `k >= 5`, inverse temperature `beta > 0`, and accuracy `0 < epsilon <= 1/4096`. For every sufficiently large physical size `N`, equality testing of two unknown Gibbs states requires

    Omega_{k,beta,epsilon}(N^a / (log N)^(a/(k-1))),
    a = min{(2k+2)/3, (4k-1)/5}.

The promise is exact equality versus **full trace norm at least epsilon**. Each Hamiltonian is at most k-local, with each nonidentity Pauli coefficient bounded by one in magnitude. There is no bounded-degree or bounded-per-site-total-strength restriction. The lower bound allows arbitrary collective quantum measurements and adaptive choice of source, and counts the worst-case TOTAL copies across both sources. The hard subclass is diagonal. Every label, clone, data, reservoir and padding spin is counted.

- For `k=5`: exponent `19/5`, with logarithmic denominator power `19/20`.
- For `k=6`: exponent `23/5`, with logarithmic denominator power `23/25`.
- For `k>=7`: exponent `(2k+2)/3`, with logarithmic denominator power `(2k+2)/(3(k-1))`.

These are fixed-parameter asymptotic statements; constants and size thresholds may depend on k, beta and epsilon. No new k=3 or k=4 result is asserted. The general collective upper bound and this lower bound still leave a gap.

## What changes, and what is reused

The prior draws one light-coordinate fraction from Beta(3,3) for each label, and holds it fixed across both sources and all copies. It also makes common fixed random bit flips. An integration-by-parts score bound suppresses the full two-copy row information. A separate all-count likelihood estimate controls every higher count, including the shared label-mass denominator. Conditioning on far alternatives and the normalized physical-copy simulation are included in the proof.

The precise distinction from the earlier alphabet ceilings is that the bit flips introduce complemented light means `1-ell` and `1-ell +/- delta`, outside their declared alphabet. Prior correlation alone would not evade a pointwise tester. See the separate clarification, which supplements the candidate's compressed comparison paragraph.

Physical admission is reused from [component30](https://github.com/Sodelin/Research-Commons/blob/75077b740d7a6c44aee69cbd776aea5e26a43014/research/2026-10-16-g6-gibbs-certification/conditional-qubit-admission-30/README.md), with common source-independent guards and inverse-polynomial leakage. The random-mass construction and denominator build on [component29](https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/README.md). The earlier [alphabet ceilings](https://github.com/Sodelin/Research-Commons/blob/4e9bbabbf28b96beee04bef9f0352979f40611c6/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/ceilings/unequal-marginals-29c/README.md) and [angular-prior exclusion31](https://github.com/Sodelin/Research-Commons/blob/346f420ce6e21212e9295694bd13454842a4e9cc/research/2026-10-16-g6-gibbs-certification/angular-prior-exclusion-31/README.md) remain valid at their original scopes.

The heavy/light product-distribution method is attributed to Canonne, Diakonikolas, Kane and Stewart, [Testing Bayesian Networks, COLT2017, Section5.2/Theorem40](https://proceedings.mlr.press/v65/canonne17a/canonne17a.pdf). Score bounds, integration by parts, Poissonization and data processing are classical ingredients. Historical novelty of this particular composition has not been established.

## Evidence and reading order

1. `P1-LATENT-LIGHT-FRACTION-CANDIDATE-32.md`: unchanged complete derivation, including its historical pending-review header.
2. `P1-LATENT-LIGHT-FRACTION-CLARIFICATION-32.md`: exact distinction from the earlier conditional alphabet.
3. `P1-LATENT-LIGHT-FRACTION-INDEPENDENT-REVIEW-32.md`: separate assistant-context full statistical hand/source review.
4. `P1-LATENT-LIGHT-FRACTION-ADMISSION-INDEPENDENT-REVIEW-32.md`: separate assistant-context physical admission, farness, normalization and budget review.
5. Author and separately authored review checkers with their successful logs. They verify finite exact identities and small pair-row laws; they do not prove the all-size theorem by execution.
6. `COORDINATION-CHECKPOINT.md` and `MANIFEST.json`: the remaining full-gap obligation and exact file digests.

The full P1 optimal-copy problem remains open. This packet supplies a stronger lower-bound component, with no general tester, matching upper bound, efficient preparation claim or experimental validation.
