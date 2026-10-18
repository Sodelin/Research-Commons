# Reviewed nonlinear collective mixture selection component

18 October 2026 UTC. Author: dot (OpenAI), working with Nolan. Separate assistant-context hand/source review: scoped PASS.

## Result and limits

The frozen note provides an explicit source-independent collective POVM for a known finite family of Hermitian losses satisfying the stated null mean/second-moment calibration. Noncommuting losses are permitted. Its proof controls both hypotheses using a known lower bound on the prior mass of sufficiently negative witnesses. For paired source samples it uses exactly **2n original copies**, with n and all constants specified in the note.

This closes the generic selection implementation gap for this calibrated finite-family mixture. It does not supply an inexpensive source-uniform good-witness mass bound. The Fourier specialization costs **O(M log² M)** at fixed parameters, still dominated by accepted [upper13, O(M log M)](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md). A better source-independent good-mass guarantee, or fully paid adaptive selection with conditional null calibration, remains missing. No efficient circuit claim is made.

The input family and null identity are inherited from the [reviewed Fourier adequacy packet](https://github.com/Sodelin/Research-Commons/blob/a91f02657b622b364a6cc366aac67d4883c77cf0/research/2026-10-18-dot-new-attacks-0509z/p1-fourier-adequacy/README.md). Exponential concentration and inverse operator Jensen methods are established ingredients; the note gives exact attribution and a self-contained inverse-comparison proof. Historical novelty is unresolved. All original master claims remain open, and [lower32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) is unchanged.

## Review and evidence

- [Frozen candidate](P1-NONLINEAR-EXPONENTIAL-MIXTURE-CANDIDATE-20261018.md): exact reviewed bytes preserved. Its original opening “separate review pending” records the producing-pass status; the subsequently completed [independent review](P1-NONLINEAR-EXPONENTIAL-MIXTURE-INDEPENDENT-REVIEW.md) and this README establish the current scoped PASS.
- [Author checker](check_nonlinear_exponential_mixture_20261018.py) and [executed author log](check_nonlinear_exponential_mixture_20261018.log): 41 finite exact rational checks and 23 floating-point diagnostics. The diagnostics are noncertifying; neither group proves the arbitrary-dimension theorem.
- The separate review is a hand/source review and claims no execution. Publication adds no independent execution claim. No Lean verification, external peer review, optimal-copy result or full P1 closure is claimed.
- The limited quadratic symmetry statement applies only to its explicitly affine variance certificate, not arbitrary tests or the nonlinear mixture.

The SHA256 manifest pins the five content files. No prior source or result was replaced.
