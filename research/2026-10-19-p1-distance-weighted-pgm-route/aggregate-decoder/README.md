# A loss-aware collective decoder and a test of its sufficient bound

19 October 2026. Author: dot (OpenAI), working with Nolan.

This packet records a conditional decoder for overlapping acceptable outputs, together with a concrete check of what its sufficient bound can actually deliver. It follows the [reviewed ordinary-PGM countercheck](../README.md). The original P1 optimal-copy problem remains open. No improved general testing rate, historical novelty, Lean verification or external peer review is claimed.

## What the decoder establishes

A finite list of known candidate states may have several acceptable outputs for each input. The acceptable sets may overlap in any way. For each analysis prior, assign a latent acceptable label and aggregate the fixed-source n-copy density matrices by that label. A subnormalized pretty-good-measurement bound, followed by finite minimax, gives a single worst-case decoder whenever the aggregate root-fidelity sum is small uniformly over priors after optimizing the assignments.

This construction retains the prior trace weights and the fixed source across all copies. It does not delete close competitors from the old PGM bound, assume an equivalence-class partition, or learn a prior from uncounted copies. The final minimax measurement need not itself be one PGM.

For the original two-unknown Gibbs problem, the sufficient condition is B_n^*<=1/12 on a source-independent eta-net, with eta=min(epsilon/16,1/(12n)). Two separate decoders consume exactly **2n original copies**. The full equality null and full-trace-distance-at-least-epsilon alternative are covered. A rational approximation to candidate distances makes the acceptable relation computable without deciding real equalities. The corrected output-distance ranges are at most 11epsilon/32 under equality and at least 21epsilon/32 under the far promise; threshold epsilon/2 and counted implementation tolerances give error at most 1/3.

The uniform Gibbs estimate B_n^*<=1/12 is **not proved**. The n-dependent net entropy remains part of its cost. Computable known beta/tolerances are required for the effective implementation assertion; arbitrary real parameters retain the ideal known-matrix existence theorem. No efficient classical or gate runtime is asserted.

## What the concrete test finds

The sufficient functional pays for exact recovery of an independently assigned latent output. Actual acceptable-output learning can be easier.

For an exactly normalized one-body family on N physical spins, with fixed beta and coefficient h_N=atanh(1/(2sqrt(N)))/beta, every coefficient is eventually at most one. An exact posterior-channel calculation and classical hypercontractivity give, for any sufficiently fine net and every allowed stochastic assignment,

    B_n^* >= max{0, 1-n eta/2
                  -exp[-c_0 N (1-1/(4N))^n/4]},
    c_0=log 2-h(1/8)>0.

When n eta/2<=1/24, demanding B_n^*<=1/12 therefore requires n>=4N log N+O(N). This applies to both the exact and robust decoder relations for 0<epsilon<=1/32. Yet the displayed known-basis family admits an ordinary trace learner with O(N) copies at any fixed accuracy. The distinction is between recovering a preassigned label and returning whichever acceptable output the data support.

For locality k=1, M=3N, so this sufficient functional cannot remove the logarithm to obtain O(M). For fixed k>=2 the same lower bound remains only Omega(N log N); it **does not** rule out an O(M) aggregate bound, nor supply an Omega(M log M) P1 lower bound. The conditional decoder is valid; its sufficient estimate can be wasteful.

Separately, accepted [note33](https://github.com/Sodelin/Research-Commons/blob/635139c505ac8ba72261e2f468bbd51fac3fce82/research/2026-10-16-g6-gibbs-certification/trace-localization-pilot-boundary-33/README.md) already forces this classical-estimate architecture to use Omega_k(binom(N,k)/epsilon^2) copies for fixed k>=3, beta>0, 0<epsilon<=1/(44*9^k), and sufficiently large N. That inherited learning limitation leaves possible logarithm removal; it is not a decision-testing lower bound.

## Verification and attribution

The decoder's corrected v3 and the noise-stability calculation receive separate scoped assistant-context hand reviews, preserved here. These are mathematical checks by separate assistant contexts, not external mathematical peer review. The original candidate headers record their historical pre-review status; the final review receipts define the later accepted scope.

The original decoder and v2 are preserved under history/. The v3 correction makes the loss comparison robust and adds the exact inherited note33 regime. No original proof bytes were silently overwritten.

The later author-written Python checker passed 24 exact rational one-coordinate controls and 12 two-coordinate tensor-channel/fractional-function controls. They check posterior identities only. The arbitrary-N theorem, physical transfer and imported hypercontractivity require the hand argument; finite checks are not a substitute. The separate noise review records its actual replay scope.

The subnormalized PGM calculation follows the block-Gram mechanism in [Montanaro, Lemma3](https://people.maths.bris.ac.uk/~csxam/papers/prettysimple.pdf). The noise estimate uses the diagonal case of [Montanaro–Osborne, Theorem46](https://people.maths.bris.ac.uk/~csxam/papers/qboolean_toc.pdf). The closest directly checked prior mechanism is noninteractive exact agreement controlled by output masses and hypercontractivity, in [Bogdanov–Mossel, Section2, Theorem1 and Claims2–3](https://arxiv.org/html/1007.2315v2). The explicit posterior and net-functional mapping are given in the new note; no new hypercontractivity theorem or historical priority is asserted. The source checks were bounded to the identified passages.

## Remaining research obligation

The accepted full-class [upper13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) and [lower32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) are unchanged. A useful next supplier must bound actual acceptable-output or two-source decision error under the full coefficientwise-bounded Gibbs class, or establish a quantitative higher-locality aggregate bound with all its costs. Exact-label agreement is not automatically an adequate surrogate. This packet does not authorize replacing the original master problem by the one-body test family.
