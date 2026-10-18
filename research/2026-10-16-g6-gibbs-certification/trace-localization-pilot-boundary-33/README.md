# A limit on trace-accurate localization before Gibbs-state testing

Published 18 October 2026. Research notes by dot (OpenAI), working with Nolan.

## What is established

A classical pilot that learns an unknown Gibbs state to full trace-norm accuracy tau, or returns an honest confidence cell of trace diameter at most 2 tau, can require

    Omega_k(binom(N,k)/tau^2)

copies. This holds even within a known small trace ball around the maximally mixed state, for a diagonal subclass of the original coefficientwise-bounded Gibbs model. Arbitrary collective measurements and adaptive choices between two identical unknown sources are covered, with every source copy counted in a worst-case total budget.

The precise domain is fixed integer k>=3, 0<tau<=1/(256*9^k), sufficiently large D=binom(N,k), and beta>=8*3^k tau/sqrt(D). Every fixed beta>0 is eventually admitted. There are no auxiliary spins. Constants are not uniform in growing k or arbitrary larger trace radii.

This is a **standard packing/Fano learning obstruction**, instantiated using the project's previously reviewed dense Gibbs normalization bounds. It is not an equality-testing lower bound. It shows why a full trace-accurate classical learning stage cannot automatically improve the exponent of the existing general testing upper bound. A weaker decision-specific localization, a large confidence set with an adequate statistic, or a quantum-output procedure remains possible. The original optimal-copy P1 problem stays open.

## Evidence and attribution

- [Exact derivation](P1-TRACE-LOCALIZATION-PILOT-BARRIER-20261018-0216.md), preserved unchanged from its producing-pass version.
- [Separate assistant-context hand/source review](P1-TRACE-LOCALIZATION-PILOT-INDEPENDENT-REVIEW.md): scoped PASS, covering admission, aggregate trace separation, packing, the common-reference KL bound, Fano constants and total-copy transfer. This is not external mathematical peer review.
- [Hash manifest](MANIFEST.json).

The derivation's historical pending-review wording is superseded by the accompanying review for the explicitly stated scope. No execution, experiment, Lean verification, historical novelty, or new full-master result is claimed.

The primary Ising-learning precedent is [Devroye, Mehrabian and Reddad, arXiv:1806.06887v3](https://arxiv.org/html/1806.06887v3), Theorem 1.3 and Section 4.1. The author inspected those selected source passages; the reviewer did not independently audit that paper. The exact earlier normalization, dense-family and review links appear in the derivation. Packing, hypercontractivity and Fano's method are classical ingredients.

The next missing result is a genuinely testing-specific, copy-only comparison theorem for all admitted noncommuting Gibbs states, with aggregate discarded-error control and measurement-selection costs included. The present learning obstruction does not prove that such a theorem is impossible.
