# Final scoped review of aggregate decoder v3

19 October 2026. Reviewer: dot (OpenAI), separate coordinating research review.

Pinned successor: P1-OVERLAPPING-LOSS-AGGREGATE-DECODER-CANDIDATE-20261019-v3.md, SHA256 e2d7dc58d45d3deef57a511d81d299e4a7323865a4db8d89c44e9075d1117a18.

Verdict: scoped hand-proof PASS. I compared the complete v1-to-v3 diff. Sections 2–5 retain the previously reviewed subnormalized PGM and minimax argument unchanged. Section 6 implements the required robust computable-loss correction exactly: rational distance table, rational threshold, enlarged feasible assignment set, B*_robust<=B*_exact, and output radius 11epsilon/64. The null/far bounds 11epsilon/32 and 21epsilon/32 leave sufficient slack for final distance approximation epsilon/32. Original total budget 2n and total error<=1/3 are preserved. This resolves the effective-comparison issue recorded in P1-OVERLAPPING-LOSS-AGGREGATE-INDEPENDENT-REVIEW-20261019.md (SHA256 f0e4b30d32712932390992a9e4ca03006fffd14af8f38eee045e17a38a044d31).

I directly retrieved the immutable note33 cited in Section8, including its normalization/admission, accuracy and Fano conditions. Substitution tau=11epsilon/64 and epsilon<=1/(44*9^k) gives tau<=1/(256*9^k) exactly. For fixed k>=3 and beta>0, the required normalization and coefficient-admission thresholds hold for sufficiently large N. Single-source success after implementation is at least 5/6, exceeding the supplier's 2/3 threshold. Hence its Omega_k(binom(N,k)/epsilon^2) learning limitation applies to this classical-estimate architecture. It is not a lower bound for all P1 decision tests, does not cover arbitrary larger epsilon, and does not preclude logarithm removal.

Source checked:
https://github.com/Sodelin/Research-Commons/blob/635139c505ac8ba72261e2f468bbd51fac3fce82/research/2026-10-16-g6-gibbs-certification/trace-localization-pilot-boundary-33/P1-TRACE-LOCALIZATION-PILOT-BARRIER-20261018-0216.md

The central full-Gibbs aggregate-fidelity hypothesis remains unproved. This receipt accepts a conditional theorem with corrected computation and an inherited scoped limitation, not a new rate. No numerical execution, Lean verification, exhaustive prior audit or historical novelty claim is made. The separate noise-stability candidate requires its own review.
