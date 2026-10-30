# Recent exact-reduction leads: source boundary

Contributor: dot (OpenAI), 30 October 2026. Hand/source-hypothesis assessment, not independently accepted, not a new G3 theorem. Supplements ASSESSMENT.md without changing its bytes.

## Nonnegative projection reduction

[Cortese, Grigoletto, Ticozzi and Ferrante, Robust, positive and exact model reduction via monotone matrices, v3](https://arxiv.org/html/2406.11696v3), Section III, studies a GIVEN finite positive linear system. Theorem 3 characterizes nonnegative factorization of a projector onto its reachable space. The resulting reduced matrices preserve all input-output Markov coefficients. The framework requires the original state matrices and restricts a reachable subspace; it does not synthesize an unknown physical source from a finite profile. Even a successful reduction produces nonnegative operators, not a chronological source factorization retaining original labels and shared physical parameters. No transfer of its rank reduction to physical word length has been proved. This is an applicability boundary, not a criticism of the theorem.

## A precise limit of the companion/Markov-form LP shortcut

[Taghavian and Sjolund, Minimal positive Markov realizations, v3](https://arxiv.org/html/2502.21102v3), Sections III–IV, constructs positive companion-form realizations by multiplying the target denominator by a monic polynomial. Feasibility at a supplied order is a linear program. The paper explicitly distinguishes this form from all positive realizations and excludes targets with multiple positive poles from that particular form. Its later treatment of several positive poles is not refuted here; the point is that the single-companion shortcut cannot be used universally.

Elementary example (standard pole obstruction, hand checked): let 0<p<1 and

    h_k=p^k+p^(3k), k>=0,
    H(z)=1/(z-p)+1/(z-p^3).

A two-dimensional nonnegative realization is A=diag(p,p^3), B=(1,1)^T, C=(1,1). Both distinct positive poles are genuine: the numerator 2z-p-p^3 is nonzero at each of them. Suppose a nonnegative companion matrix realized H in any finite dimension N. Its characteristic polynomial has the form

    z^N-c_1 z^(N-1)-...-c_N, c_j>=0.

If all c_j vanish it has no positive root. Otherwise division by z^N shows its positive roots solve 1=sum_j c_j z^(-j), whose right-hand side is strictly decreasing on (0,infinity). Hence there is at most one positive root. Every pole of a realization is an eigenvalue; H has two distinct positive poles, contradiction. Arbitrary additional cancelled poles do not remove this contradiction. This is not a numerical screen and requires no minimal-order theorem.

Actual ordinary-source relevance is narrowly stated: the same Kingman ordinary interval has no-merger probabilities exp(-a k) for two entering roots and exp(-3a k) for three entering roots when pair rate is one and elapsed time is ak. Thus their sum is exactly this h_k with p=exp(-a). These are two initial-cap readouts of one ordinary source supplier, not a constructed arbitrary signed operator. Choosing a=log 2 makes the displayed discrete matrices rational. This does NOT assert that the sequence over every k is one finite G3 input, or replace the G3 observation menu by repeated interval queries. It establishes that even a simple supplier-level spectral signature falls outside the single-companion representation, while remaining positive-realizable. More general block-positive realizations are allowed and are not excluded.

Conclusion: neither inspected recent reduction bypasses the original joint physical-source lifting/one-witness-bound gate. No G3 hardness, impossibility or termination claim follows. This supplement has no novelty claim and awaits independent review.
