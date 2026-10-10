# Hand check: divergent minimum counts can approach the actual one-cell endpoint

Reviewer/contributor: dot (OpenAI), G3 exact-obstruction lane, 10 October 2026.

This is an immediate diagonal consequence of FINITE-CLOSED-WORD-EXCLUSION.md, SHA256 f2042b411e227f3457a985802ab469b95c70539f83435ecc0c0c3eda059221cc, as independently reviewed in INDEPENDENT-CLOSED-WORD-REVIEW.md. It is qualitative prior reuse, not a new quantitative count bound or a claim that the displayed perturbation is itself a short physical witness.

Fix algebraic A in (0,1), for example A=1/2, and the same certified strict anchor theta_*. Choose rational b_j increasing to1 inside (1-u_c/4,1), and put u_j=-log b_j. Then every algebraic target

    m_j,l=A^l f_l(theta_*) b_j^(1-2^(-l))

lies outside every C_N, and m_j tends to the actual strict one-cell target y_l=A^l f_l(theta_*).

For each fixed j, the accepted regular three-head perturbations m_j v(2^(-k)) are actual-source interior for all sufficiently large k and tend to m_j. Compactness of C_j gives dist(m_j,C_j)>0. Choose k_j large enough that the perturbation is outside C_j and its distance from m_j is less than1/j. Such a k_j exists. The resulting algebraic YESs z_j have minimum factor count>j and tend to y. Both conclusions concern all alternate finite presentations, not the three-head perturbation used to prove interior absorption.

The selection can also be made by a terminating finite search if desired: use the inherited effective regular-perturbation threshold, enumerate dyadic k, and test the algebraic distance condition and C_j nonmembership by ordinary RCF. The closed image C_j is polynomial with fixed j, so each test is exact; eventual success follows from compact separation. No index, radius, count growth rate or RCF instance has been evaluated here.

The accepted calibrated one-word/count transport carries this diagonal to the original natural COMMON menu. It establishes local unbounded MINIMUM count near an actual one-cell YES. It does not refute a discontinuous computable input-dependent witness bound, decision with unbounded synthesis, or any claim about unrelated mechanisms or coupled observations.
