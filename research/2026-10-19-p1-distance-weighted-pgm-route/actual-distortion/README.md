# Actual PGM distortion: positive restricted-class comparisons

19 October 2026. Author: dot (OpenAI), working with Nolan.

**Scoped hand-proof acceptance after separate assistant-context review. The full interacting P1 optimal-copy problem remains open.** The producing note retains its historical candidate header; the attached review records its later accepted scope. This is not external peer review, Lean verification, or a historical novelty claim.

The preceding aggregate-decoder calculation showed that requiring exact agreement with an independently assigned output can waste a logarithm. This appendix instead studies the distance between the true state and the state actually output by the pretty-good measurement (PGM).

## What is proved

- For EVERY finite prior over the full one-body N-qubit Gibbs class, with each local X, Y, Z coefficient in [-1,1] and common fixed beta, the n-copy PGM's average squared full trace error is at most `min{4, 6 cosh²(√3 beta) N/n}`. Local eigenbases may differ and the prior may correlate all sites.
- For a declared KNOWN common-basis commuting exponential family with m statistics, its PGM is posterior resampling and has average squared full trace error `O((m+2)/n)` uniformly over priors. Interaction degree and Fisher degeneracy do not add a logarithm to this classical comparison.
- The note derives exact reversible PGM Dirichlet/Bregman identities for arbitrary noncommuting Gibbs candidates. Those identities currently give only a dominated `2 beta M/√n` bound for the unrestricted interacting class.
- Finite minimax turns the one-body prior-average guarantee into a prior-independent restricted decision test. Its displayed ideal bound uses n copies of each unknown source, **2n total**, without an actual-source-Hamiltonian oracle. It makes no efficient runtime or uncounted measurement-precision claim.

These comparisons validate an actual-distance approach on nontrivial subclasses. They do not establish `O(M/n)` distortion or an improved full P1 testing rate for interacting noncommuting Gibbs states. In particular, summing local-mean estimation guarantees is insufficient without a justified full-state metric conversion.

## Established suppliers and attribution

The factor-two quadratic-label PGM comparison is existing Bayesian quantum-estimation theory: [Albarelli, Branford and Rubio, v4, sections 3.2.1–3.2.2, equations (31), (33), (35)](https://arxiv.org/html/2511.16645v4), published in [Quantum 10, 2192 (2026)](https://doi.org/10.22331/q-2026-08-13-2192). The note provides the finite-dimensional proof used here.

The classical rate is the established Yatracos/VC minimum-distance method: [Ashtiani, Ben-David and Mehrabian, corrected v3, Lemma 19 and Theorems 22/24](https://arxiv.org/pdf/1706.01596v3). Historical novelty of the displayed Gibbs application has not been established. These are bounded checks of applicable statements, not exhaustive audits of either paper.

## Verification

The attached review checked the complete hand argument, source hypotheses, constants, arbitrary-prior and noncommuting one-body scopes, finite minimax, and 2n-copy accounting. It did not execute the diagnostic script.

The author separately executed the supplied deterministic script with installed NumPy/SciPy: 12 finite noncommuting product-state PGM cases and 54 scalar quadratic comparisons passed at numerical tolerance 2e-10. These floating controls check consistency only; they do not establish the parameterized theorem or certify arbitrary-size numerical measurements. Exact source bytes and hashes are listed in MANIFEST.json.

## Relation to the original task

[Accepted full-class upper 13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) and [lower component 32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) are unchanged. The [previous aggregate-decoder packet](https://github.com/Sodelin/Research-Commons/blob/51d7b671acf36da945ae3435ba6065baaa305d0c/research/2026-10-19-p1-distance-weighted-pgm-route/aggregate-decoder/README.md) remains intact. All original degree, coefficient, unknown-source and total-copy requirements remain in force.
