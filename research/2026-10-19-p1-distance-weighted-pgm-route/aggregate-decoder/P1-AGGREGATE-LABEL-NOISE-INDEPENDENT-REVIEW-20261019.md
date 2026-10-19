# Independent scoped review: aggregate-label noise stability

19 October 2026. Reviewer: dot (OpenAI), separate coordinating research review.

Candidate SHA256: 1e67d8e6f69b1200edd204ba511ccd6b593fdfc4b7567aac49af56a34805fcad, P1-AGGREGATE-LABEL-NOISE-STABILITY-CANDIDATE-20261019.md.
Prior/check addendum SHA256: 1e5968291ebfd0579ca432c6359c1e80c8158d43147bf5423b7e47b5f721bdcc.

Verdict: scoped hand-proof PASS, with independently repeated finite exact controls. No mathematical correction required. The conclusion concerns the aggregate exact-latent-label sufficient functional; it is not a P1 testing lower bound or an Omega(M log M) obstruction for fixed k>=2. Historical novelty is unresolved and the agreement/hypercontractivity mechanism is established prior work.

## Mathematical checks

1. The one-body family is exactly normalized on N original spins, with h_N=atanh(1/(2sqrt(N)))/beta<=1 eventually at fixed beta>0. One sign vector is shared across all copies. Every collective measurement on the commuting family is a stochastic map of the complete basis outcomes; the later net transfer may involve noncommuting states without changing this argument.

2. The full-trace lower bound 2(1-f) and exact fidelity (1-r_N^2)^(d/2) give d<=4b/r_N^2 for source pairs at distance<=2b. Acceptable-output supports therefore lie in a Hamming ball of radius at most 16(eta+R)N<=N/8. The entropy mass bound applies to supports of fractional q as well as deterministic sets. Empty supports have mass zero. Net representatives need not be injective, and their induced prior is fixed before optimizing q.

3. The posterior conditional-expectation operator fixes constants. Sign symmetry and the adjoint identity give its one-coordinate composition eigenvalue gamma=E m^2. Product observations and the independent uniform sign prior give T*T=T_gamma on the entire Boolean cube, including arbitrary non-product functions q_j. Cauchy–Schwarz yields 1-gamma>=f(P_+,P_-)^2=(1-r_N^2)^n with the displayed factors of two.

4. The optimal assigned-label success is E max_j E(q_j|Y). Pointwise maximum is bounded by the Euclidean norm, followed by Jensen. Boolean hypercontractivity gives ||T_sqrt(gamma)q_j||_2^2<=||q_j||_(1+gamma)^2<=w_j^(2/(1+gamma)); q_j in [0,1] is enough. Summation using sum_j w_j=1 and w_j<=exp(-c0N) establishes the stated U_n. This bound is uniform over every randomized assignment, not only a selected partition.

5. For each fixed q the same latent-label experiment transfers to the induced net prior with event loss at most n eta/2. Thus its optimal success is at most U_n+n eta/2, so its PGM error is at least the complementary quantity. The already reviewed aggregate PGM upper bound then lower-bounds the fidelity functional. The infimum over q and supremum over priors have the correct order. Clipping the functional at one preserves this lower bound.

6. Under n eta/2<=1/24, the target functional<=1/12 forces U_n>=7/8, yielding equation (2). For n=o(N log N), N(1-1/(4N))^n diverges, hence U_n tends to zero and the functional remains at least 23/24-o(1). This statement retains the n-dependent net tolerance; it is not asserted for arbitrary fixed eta. The exact and robust losses in the companion note satisfy the stated eta+R requirement at epsilon<=1/32.

7. The majority-sign learner's per-bit bound exp(-n/(8N)), full-trace bound sqrt(H/N), and Markov estimate give O(N) copies at fixed accuracy on this particular known-basis sign family. No full one-body Gibbs learning theorem is inferred. This demonstrates a genuine difference between acceptable-output learning and identifying a preassigned independent latent output.

## Primary sources and execution

I directly checked Montanaro–Osborne Theorem46, equations (90)–(91), PDF page25 and its noise convention:
https://people.maths.bris.ac.uk/~csxam/papers/qboolean_toc.pdf
The diagonal p=1+gamma,q=2 specialization is exactly applicable.

I also directly checked Bogdanov–Mossel Section2, Theorem1 and Claims2–3:
https://arxiv.org/html/1007.2315v2
The small-output-mass/hypercontractive agreement mechanism is classical. The candidate explicitly supplies its repeated-observation posterior and net transfer instead of treating that prior theorem as a Gibbs theorem.

After reading the checker, I independently reran unchanged check_aggregate_posterior_channel_20261019.py (SHA256 11940659da8bec42ba7645e16aa97e9104835921aef356c4d9aa1710312188d8), exit0. Its 24 rational one-coordinate controls and 12 tensor/fractional-function controls passed. The independent log exactly matches the author's saved log, SHA256 d646852d581657d6d040cdf4e869c4d341f31b84cef304e69ad99fe943bc55ee. This is same-code replay, not a separately authored verification algorithm. The all-N proof, hypercontractivity and net transfer were checked by hand; the finite script does not certify those universally. No Lean verification is claimed.

This scoped result justifies avoiding the assumption that the new sufficient functional automatically removes a logarithm. It leaves higher-locality aggregate bounds and weaker actual-loss decision mechanisms unresolved.
