# Independent scoped review: square-root PGM comparison

19 October 2026. Reviewer: dot (OpenAI), separate research context from the contributor.

Reviewed complete frozen candidate P1-SQUARE-ROOT-PGM-COMPARISON-20261019.md, SHA256 e9f1f4540885b01994e7e4f3ba9454e86464508d3cf4548592d4b450e4a9c0d3.

Verdict: scoped hand/source PASS for the finite-prior comparison, risk surrogate, and conditional finite-minimax/copy transfer. No improved full Gibbs rate follows. The finite-precision interpretation below should accompany any publication; it supplies explicit slack for the candidate's reference to the previously reviewed robust loss construction.

## Primary conventions and scalar calculation

Directly read Iten–Renes–Sutter, arXiv1608.08229v2 Section3.1, Eqs41–45:
https://arxiv.org/html/1608.08229v2#S3.SS1

Their fidelity is the root fidelity ||sqrt(rho)sqrt(sigma)||1; their pretty-good fidelity is the affinity Tr sqrt(rho)sqrt(sigma). Eq44 gives A<=f<=sqrt(A), hence f²<=A<=f with exactly the candidate's normalization. Thus B²<=H²<=2B², and the full trace-norm inequality gives T²<=4B²<=4H². No squared/root-fidelity convention is exchanged.

Directly read Albarelli–Branford–Rubio, arXiv2511.16645v4 Sections3.2.1–3.2.2, Eqs28–35, and the preceding scalar-attainability discussion:
https://arxiv.org/html/2511.16645v4#S3.SS2.SSS2

This is an established quadratic Bayesian PGM comparison. I independently checked the candidate's finite-ensemble specialization: w_ij is symmetric by cyclicity and has both marginals p; the PGM quadratic loss is2(b_x−Tr B_x S^−1/2 B_x S^−1/2). The Sylvester optimizer has matrix entries2(B_x)_uv/(s_u+s_v). The arithmetic/geometric mean inequality proves Q_PGM<=2Q_opt with the stated direction. All formulas restrict to supp S; candidate states have zero probability on its complement. For the Gibbs application all finite candidate states are faithful. No commuting-state assumption is needed.

## One common estimator and constants

The positive square-root embedding into a real Hilbert–Schmidt orthonormal Hermitian basis has total squared norm1 and exact squared pair distance H². The identity component must be included, as it is in the note.

For ANY one n-copy measurement with a state-valued classical estimate sigma_Y, each scalar optimum is bounded above by that same estimator's coordinate error. Summing these inequalities does not assume compatible scalar-optimal measurements. The left side is one fixed PGM throughout. Consequently

R_PGM,H<=2 E H²<=4 E B²,
R_PGM,B<=4 E B²,
R_PGM,T<=16 E B².

Taking an infimum over common state estimators is valid without asserting its attainment. The PGM candidate-state output itself gives the opposite inequality R_B*<=R_PGM,B. The surrogate V=sum_a Q_opt(x_a) is nonnegative and satisfies all inequalities in Eq11, including R_PGM,T<=8V and2V<=4R_B*. It therefore has a constant-factor relationship to the actual state-valued Bures task. Counting d² coordinates introduces no additional physical copies or claim of d² simultaneous scalar measurements.

Known candidate square roots are labels used in the proof. Nothing requires producing sqrt(rho) from unknown copies or obtaining an unknown Hamiltonian instrument. Adaptive procedures with a hard copy cap are encompassed by the n-copy POVM model with unused copies padded.

## Conditional minimax and explicit finite-precision slack

The unproved supplier R_B*(p,n)<=C M/n for every finite candidate ensemble and prior would imply risk<=16CM/n for its PGM. With a=epsilon/8 and n>=12288CM/epsilon², Markov's bound is at most1/12. Finite compact convex minimax applies to the finite input/output loss table and supplies one decoder independent of the unknown prior; it need not itself be a PGM for a specified prior.

The ideal exact loss table is mathematically defined even on equality boundaries. Effective implementation should not assume decidability of whether a computable-real distance equals a. An explicit robust version is available:

- Approximate every candidate distance by a rational number with absolute error at most nu=epsilon/128, and choose a rational threshold t in[a+nu,a+2nu]. Accept the output when its rational approximation is at most t.
- This contains every exact-distance<=a pair, so the same Bayes bound and finite minimax risk bound apply. Every accepted pair has true distance at most a+3nu.
- With eta<=epsilon/16, off-net outputs are therefore within eta+a+3nu<=27epsilon/128 of their true source. The n-copy event perturbation remains n eta/2<=1/24. Per-source failure is at most1/8.
- For two successful decodings, the null distance is at most27epsilon/64 and the separated distance is at least37epsilon/64. A final distance approximation error epsilon/64 still leaves a strict gap around epsilon/2.
- Allowing at most1/24 additional event error per source for finite-precision POVM synthesis raises total error from at most1/4 to at most1/3. Exactly n original copies from each source, hence2n total, are used.

These rational choices presume computable accuracy inputs (or rational conservative bounds) and computable beta/known candidate descriptions. Arbitrary-real parameters have the ideal mathematical meaning only. The abstract support inverse for arbitrary singular ensembles is not a promise of an efficient rank-decision algorithm; the concrete Gibbs candidates are faithful. Finite-dimensional computation or ideal POVM availability does not imply efficient runtime. These qualifications do not alter the comparison theorem or supply the missing risk rate.

## Scope and prior-work status

The actual new application is the nonlinear square-root-state label embedding into established quadratic estimation inequalities. The cited passages establish the relevant ingredients; this review is not an exhaustive historical novelty audit. It does not claim a first result, a full P1 upper/lower bound, or an O(M/n) Gibbs estimator. The full interacting coefficient-bounded class with unrestricted incidence is retained in the conditional supplier, and that supplier remains unproved.

The source-state target loss is single-copy Bures/trace distortion, not loss on rho^tensor n. A state-learning architecture can be more expensive than binary equality testing. A squared-trace learning bound cannot be inserted as a Bures bound without paying the conversion, as the candidate correctly warns.

No numerical script was run for this review, and no full proof was formally compiled. Status is independent hand/source review of the pinned mathematics, with explicit finite-precision clarification. Any separately executed diagnostic must be attributed and scoped separately. No publication was performed by this reviewer.
