# Independent acceptance: matched Poisson copy thresholds and unbounded factor complexity

Reviewer: Sol6.1 head audit, coordinated by dot. Date: 2026-10-02.
Verdict: **ACCEPTED hand family theorem and stated corollaries**; four supplied exact finite certificate cases independently PASS. General G3 finite-input source recognition remains open.

The original all-flag proof is pinned at [4eb9abec](https://github.com/Sodelin/Research-Commons/blob/4eb9abec3e96b7c1a0bf17bfdcca50b0c40f0058/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md). The reviewed additive corollaries are pinned in [the complete continuation at 33da55b8](https://github.com/Sodelin/Research-Commons/blob/33da55b84df3bcdbdf627005049879a038597e08/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md), blob c0fde3337fcd6be1b0fd1618d87d041e017ee4e7. Earlier cap-six/cap-seven source, normal-form, finite-retention and interior-attainment dependencies retain their separate acceptance receipts.

## Matched family and assumptions

For s>=1, interior q_j=r^(2^j), w_j>0 and a,kappa>=0, put h_lambda=a lambda+kappa+sum w_j R_lambda(q_j), where R_lambda(q)=(1-q^lambda)/(1-q), lambda=binom(k,2). Let alpha indicate a>0 and beta indicate kappa>0. This is a capped natural COMMON-chain signature, not a full forest/calendar law or preservation of original actuator IDs.

Every member is actual-source interior through cap 2s+alpha+beta+3. All sufficiently small first-loss members are nonattained beginning at cap 2s+alpha+beta+4, with a cutoff independent of the number of hypothesized finite strict factors. Thus consecutive caps match for this family. The upper guarantee also holds for arbitrary distinct positive residual nodes. The dyadic condition is needed for the stated matching lower family, rather than inferred for all node sets.

Normal forms may have zero drift or killing endpoints. Actual sources still require a strictly positive baseline and strict Bernoulli factors. The proof supplies a different interior actual realization in the upper branch; it does not admit endpoint sources by changing their definition.

## Analytic and all-factor challenge

The desingularized t^3 IFT cancellation adds two strict factors at a smallest residual node and its new square. Its limiting columns are the active drift/killing directions, all residual weights/node derivatives and the new-square value/derivative pair. A nonzero left annihilator would create more positive roots, counted with multiplicity, than a sparse polynomial with these exponents can have. Inactive endpoint coefficients are held fixed, while every active variable is two-sided. At small positive t the actual normal-form block remains full rank and strictly admissible; accepted int(C)=int(S) then gives exact finite-source interior. Splitting positive budgets and int(S)+C absorption handles extra closure terms without extracting a finite factor witness.

The lower proof uses two saturated sparse normal polynomials. At original nodes both first and second small-p terms vanish, but the third is strictly positive because q_j^3 is not a dyadic square-chain node. The new square neighborhoods have a positive first-normal bound. Near q=1 the exact derivative numerator gives uniform positivity for every p, including p near one. With beta=1, the q=0 factorization and its positive first derivative cover the killing corner uniformly once the loss budget bounds p away from one. With alpha=0 the second covector has strictly positive lambda projection: the mandatory actual positive baseline strengthens the contradiction. It is not incorrectly treated as a two-sided zero-drift source variable.

The coupled normal equations, finite-sum Cauchy inequality and total first-loss budget exclude every finite integer factor count. No fractional conic weights, numerical fits, global linear-separator shortcut or all-instance solver census enters the proof. The squared-node-union extension is accepted under the explicit exclusion q^3 notin Q union Q^2. Multiple squaring chains leave a cap gap; cube resonances are outside that corollary.

## Four independent exact certificate checks

The head independently reconstructed both derivative numerators, root/positive quotient factorizations, neighborhood radii, compact-complement lower bounds, p cutoffs and coupled C_* inequalities using rational arithmetic. It also checked the algebraic exponent identities and integer normal rows. All four supplied records PASS:

| Residues s | alpha | beta | First NO cap | Rational b |
|---|---|---|---|---|
| 1 | 0 | 0 | 6 | 1-2^(-128) |
| 1 | 0 | 1 | 7 | 1-2^(-222) |
| 1 | 1 | 1 | 8 | 1-2^(-275) |
| 2 | 1 | 0 | 9 | 1-2^(-403) |

Head checker [dyadic_certificate_review.py](g7/dyadic_certificate_review.py), SHA256 `cf137900dc26be1d4f7e1d6ddc904297e464ca8017ce16ca7ef38d3150faea50`, ran in approximately half a second. [Exact result/hash receipt](g7/dyadic-head-review-results.json) identifies all four full source records. The public author packet publishes compact records preserving original full hashes and regeneration recipes. To replay the head check, generate the four full certificates in a temporary copy of the author checker, then pass that directory to the head's --source-dir argument. The finite scripts verify these supplied cases; arbitrary-s analytic/source transfer has a separate hand proof.

## Finite recognition branches

For any positive algebraic input at or above a certified cap, the two denominator-cleared signed-monomial equalities and m2>1-min(C_*,1)/2 imply both exact normal equations and first loss below C_*. No target-family representation is assumed. With alpha=1, the inequalities force absence of every strict factor, so membership on this branch holds exactly for a pure baseline signature m_lambda=m2^lambda at EVERY supplied coordinate. With alpha=0 every such input is NO because an actual positive baseline has a strictly positive second-normal contribution. Inputs outside the certified predicate remain undecided by this branch.

## No cap-only finite factor ceiling

The rejection remains valid for positive outputs of the closed survival cube. The simultaneous p=1,q=0 corner yields zero at every positive observed exponent and is excluded by output positivity. Other neutral/endpoints delete or fold into nonnegative drift and killing; both folded losses are bounded by h2. Their normal contributions change equalities into nonpositive inequalities, which suffice for the same strict budget. All remaining strict factors vanish, leaving an affine function of lambda. Positive Poisson residue makes the target strictly concave, so it cannot agree with that affine function at three distinct observed exponents.

For any fixed N the at-most-N closed-factor image is compact. The rejected tuple lies outside it. Therefore every actual-source sequence converging to this tuple eventually needs more than N factors, for EVERY fixed N. Ordinary-moment interior is open, so these attained approximants eventually lie there as well. This proves that no bound depending only on the copy cap can cover all actual inputs at these rejection caps. It does not refute an input-dependent computable bound, claim an individual actual input needs infinitely many factors, or imply undecidability.

The author's rational approximation refinement is also accepted: choose rational p_N=ceil(theta N)/N^2, q=1/2, and positive rational baseline. N p_N tends to theta and N p_N^2 tends to zero. For the cap-seven positive-drift example the baseline is fixed b; for the zero-drift cap-six example it tends to one through 1-1/N. The resulting finite moment tuples are rational and attained, yet their minimum exact factor counts diverge. Thus rational inputs already show no cap-only ceiling for every fixed cap>=6. These are theoretical sequences, without a computed approximation rate or large-N execution claim.

The exact remaining master target is general membership for arbitrary algebraic finite common-chain signatures and the separate independent/multiport source problem. Neither this family nor its finite normal predicates close that target. Source factor count, entering-copy cap, full-law factorization, ordinary-moment interior and effective stopping remain distinct.
