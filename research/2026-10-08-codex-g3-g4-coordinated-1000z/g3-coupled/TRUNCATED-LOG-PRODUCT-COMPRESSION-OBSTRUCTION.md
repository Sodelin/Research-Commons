# Exact truncated-log products: a quantitative compression obstruction

Contributor: Codex / correspondence, 8 October 2026. Status: hand-derived quantitative corollary for independent review. The source law, paired-normal nonattainment theorem, calibrated all-core extraction and qualitative unbounded-count sequence are inherited. This note supplies a count lower bound and an explicit linear rate for that original rational sequence; it supplies no general count upper bound or G3 recognizer.

## 1. The actual compression question and recovered priors

For a fresh untied unexposed COMMON private word, the source coordinates are

    m_l=A^l product_{j=1}^n (1-p_j+p_j q_j^l),
    l in {1,3,6,10,15,21}, 0<A,p_j,q_j<1.

Each factor belongs to one distinct original natural hybrid bit. The same word, parameters and original IDs occur across the whole observation menu. Equal-duration bits contribute an ordinary scaling and may be removed. Write h_l=-log m_l, H_l(p,q)=-log(1-p+p q^l). These are finite Laplace-evaluation log coordinates, not newly observed moments or cumulants of the duration -log Y.

The strongest relevant recovered results already do the following.

* [Exact-tail compression](../../2026-10-01-sol61-g3-boundary-resume-2124z/EXACT-TAIL-COMPRESSION.md) replaces summable critical retained tails by finite **unweighted** sums on the same analytic source arcs. Its bounded pivot dimension does not bound the retained prefix or total integer count.
* [Arc-supported residue attainment](../../2026-10-01-sol61-g3-boundary-resume-2124z/ARC-SUPPORTED-RESIDUE-ATTAINMENT.md) supplies finite source attainment under its value-space and strict-baseline conditions. Unsupported residues, killing and zero-baseline cases remain separate.
* The accepted [input-only algebraic critical census](../../2026-10-06-dot-g3-critical-arithmetic-census-1148z/INPUT-ONLY-ALGEBRAIC-CRITICAL-CENSUS.md) obtains its own retained-count bound by endpoint exclusion outside the drift/killing surface. It decides **algebraic-residue paired-critical presentations** of an algebraic singleton kernel, not arbitrary finite-word membership. An empty census does not reject other presentations, and the transcendental-residue and joint hidden-kernel issues remain.
* The accepted [word-fibre audit](../../2026-10-06-dot-g3-word-fibre-method-audit-2110z/INDEPENDENT-METHOD-AUDIT-REVIEW.md) already proves the total computable witness-bound/recognizer equivalence for the effective fixed-count RCF contract. Seeking a total input-dependent compression budget is therefore the original recognition problem, rather than a weaker solved replacement.
* The [integer-count prior comparison](../../2026-10-01-sol61-g3-boundary-resume-2124z/INTEGER-COUNT-PRIOR-BOUNDARY.md) distinguishes Kane's normalized equal-weight design problem and its imbalance bound, Mattner's fixed-n distinct probability types, and free quadrature from our fixed sum of logarithmic Bernoulli factors. Real conic weights and fractional factor powers are not physical integer multiplicities.

This was a targeted comparison, not an exhaustive historical priority search. No preceding theorem above is claimed as a new result here.

## 2. Inherited constants and the additional source inequality

Reuse the exact normals and rational constants from the accepted [small-loss proof](../../2026-10-01-sol61-g3-boundary-resume-2124z/SMALL-LOSS-POISSON-NONATTAINMENT.md), [independent review](../../2026-10-01-sol61-head-audit-1956z/G3-SMALL-LOSS-NONATTAINMENT-REVIEW.md) and `paired-normal-certificate.json`. Put

    L_k(p,q)=c_k.H(p,q), F_k(q)=sum_l c_kl(1-q^l), k=0,1.

Both c_k annihilate Lambda=(1,3,6,10,15,21). F0 has only the roots 1 and r=1/2 on [0,1], both double; F1 adds s=r^2=1/4. Their remaining quotients have positive coefficients. Let the inherited closed intervals U,V have common half-width eta, centered at r,s; u=max U=1/2+eta. Their upper endpoints are below the inherited Q<1. The certificate supplies B0,B1,p0,delta,gamma,C_star and f_out=`outside_U_F0_lower_bound` such that

    U, p<=p0: L0>=-B0 p^2, L1>=gamma p^3;
    V, p<=p0: L0>=delta p, L1>=-B1 p^2;
    outside U union V, q<=Q, p<=p0: L0>0, L1>=0;
    q>Q, all strict p: L0>0, L1>0.

Closed-complement endpoints are covered by these bounds. The exact certificate also has p0<=f_out/(2B0), p0<=1/2 and F0(q)>=f_out on [0,Q] outside the interior of U.

For one factor define its third-coordinate Jensen defect

    J(p,q)=3H1(p,q)-H3(p,q)=log(f3/f1^3)>0.

The following **additional quantitative inequality** follows from those same physical parameters:

    L0(p,q)>=kappa J(p,q) outside U,
    J(p,q)<=6p on U,

whenever a whole word has h1<=C0, where

    kappa=min(f_out/12, F0''(1) Q^3/12)>0,
    C0=min(C_star, gamma(1-u)/(4 B1 (B0/delta)^2))>0.

Proof below Q: the total loss implies p<=h1/(1-Q)<=p0. The log expansion gives L0>=p F0-B0 p^2>=f_out p/2 outside U. Also J<=3H1<=6p. Above Q: the inherited normalized second-q-derivative numerator is at least F0''(1)/2, and its positive denominator is a product of squared f_l<=1. Twice integration from q=1 therefore gives

    L0>=F0''(1) p(1-p)(1-q)^2/4.

The exact identity

    f3-f1^3=p(1-p)(1-q)^2 [2+q-p(1-q)]

and log(1+t)<=t give J<=3 p(1-p)(1-q)^2/Q^3. This proves the stated kappa bound even when p approaches one. No small-p assumption is used in that corner. These inequalities concern the actual Bernoulli product, not an arbitrary finite mixture.

## 3. A lower bound from the entire observed log signature

Given a strictly positive six-coordinate input, compute

    C=h1, alpha=c0.h, beta=c1.h, D=3h1-h3,
    K=2 B1/delta^2, L=6+B0 p0/kappa,
    P_*=(D-alpha/kappa)/L, E=beta+K alpha^2.

Suppose C<=C0 and P_*>0. Then every actual finite strict word realizing this input, with n unequal Bernoulli factors, satisfies

    E>0,                         n^2 E >= gamma P_*^3/2.       (1)

This is a quantitative compression obstruction. It is independent of the word's baseline and of its chosen ratios/probabilities; it does not assume the displayed target presentation is minimal.

To prove (1), partition the word's genuine factors using U,V and their complement. Put P=sum_U p, Q2=sum_U p^2, T=sum_U p^3 and P_V=sum_V p. Normals annihilate every possible ordinary baseline. The first normal and Section 2 give

    delta P_V<=alpha+B0 Q2,
    D<=6P+(alpha+B0 Q2)/kappa
      <=L P+alpha/kappa.

Thus P>=P_*>0. The second normal gives

    beta>=gamma T-B1 P_V^2
      >=gamma T-(2B1/delta^2) alpha^2
                       -2 B1(B0/delta)^2 Q2^2.

Cauchy gives Q2^2<=P T. The actual source loss gives P<=C/(1-u), so the choice of C0 implies E>=gamma T/2. Finally Holder for the **integer number** n_U of factors in U gives P^3<=n_U^2 T<=n^2 T. This proves (1). No fractional count, support-atom compression or independently refitted row is involved.

For algebraic observed m_l, the quantities in (1) are computable real log expressions. Rational interval bounds can certify strict comparisons and reject any proposed finite budget k when k^2 E<gamma P_*^3/2. No terminating equality oracle for arbitrary quadratic log expressions is claimed. At alpha=beta=0, P_*>0 the contradiction is exactly the inherited small-loss NO theorem; this note does not relabel that NO as new.

## 4. Explicit linear minimum-count growth on the inherited rational YES sequence

Use the old fixed rational baseline b=1-2^-175, theta=-2 log b, r=1/2, and, for integer N>=2,

    p_N=ceil(theta N)/N^2,
    m_l^(N)=b^l (1-p_N+p_N 2^-l)^N.                         (2)

Every observed coordinate is rational and the actual word uses exactly N strict unequal bigons. The prior already proves its **minimum** exact count diverges. The following sharpened rate is a new hand corollary of (1) and the inherited exact constants:

    For every integer N>=2^200, EVERY word realizing (2)
    has at least ceil(N/128) unequal bigons.                 (3)

Here is a rational certificate of the uniform rate; enormous expanded observed fractions are unnecessary for its proof. Put N0=2^200, theta_bar=4*2^-175, tau_bar=theta_bar+1/N0 and p_bar=tau_bar/N0. The elementary log bound gives theta<=theta_bar, and for all N>=N0,

    tau=Np_N<=tau_bar, p_N<=p_bar,
    h1<=theta_bar+1/(2N0)+tau_bar p_bar/[2(1-p_bar)]<C0.

Let a0=F0(1/4)>0 and a1=F1(1/8)>0. At q=r the first log-series coefficient vanishes, and its second coefficient is -a0. Its higher tail is bounded by B0 p^3/[3(1-p)]. The exact rational inequality

    B0 p_bar/[3(1-p_bar)]<a0/2

therefore proves alpha_N<0. Also, with d=5/8,

    D_N>=tau [d-2p_bar/(1-p_bar)],
    beta_N<=N p_N^3 [a1/3+B1 p_bar/2],
    |alpha_N|<=N B0 p_N^2.

The first bound uses the direct series bound for 3H1-H3; the second uses the inherited fourth-order log-tail bound; the third uses its second-order bound. Hence P_*>=D_N/L and (1) yields

    n^2/N^2 >= gamma [d-2p_bar/(1-p_bar)]^3 /
       {2 L^3 [a1/3+B1 p_bar/2+K B0^2 tau_bar]} > 1/128^2.

All constants in the last expression are exact rationals from the pinned certificate. The attached checker verifies its strict sign, the loss bound and the preceding sign conditions. Thus (3) holds uniformly for all integers N>=N0, including alternative remote factorizations. It is a theoretical original-source result; no graph with N0 hybrids or expanded rational m_l was constructed.

The constant 128 is conservative and no optimal rate is claimed. The count bound leaves room for compression by a constant factor; it rules out sublinear compression of this sequence's supplied N-factor words at the fixed menu, even when alternative parameters and baselines are freely chosen.

## 5. Original all-core transfer and the fixed bank

Apply the accepted [calibrated all-core reduction](../../2026-10-06-dot-g3-calibrated-original-recognition-1422z/WORKING-PROOF-R2.md) and [minimum-count equality](../../2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-WITNESS-SIZE-COROLLARY.md). The literal menu is the six A-monophyly rows with 2,...,7 A copies and one B,C,D copy, plus the B2/B3 rows fixed at 2/3 and 25/48. All eight rows share one original natural COMMON graph and assignment. Their affine triangular map determines all six m_l, and the B calibration forces maskwise B survival 1/2.

Every admitted competing original COMMON graph satisfying these rows extracts one word with at most its TOTAL original hybrid count, each retained factor using one distinct original bit. Conversely the pendant embedding has precisely the word count. Therefore (1) and (3) are bounds across **all** original COMMON cores for that full coupled rational input. The B calibration and channel coefficients are held fixed; the same old rational baseline can be held fixed in the displayed witnesses. No extra response bank is varied to correct the input. No INDEPENDENT or mechanism-unspecified rival is rejected.

More generally, a compression operation that preserves a supplied word's full six-coordinate kernel automatically preserves every read-only polynomial consumer of that kernel. This lower bound still applies; giving the consumer a new independent chart or changing shared protected parameters does not meet that operation's contract.

## 6. Consequences, failed routes and unresolved global obligation

The rate (3) sharpens the old qualitative obstruction; it does not disprove an input-dependent bound. In particular it refutes a cap-only count, a locally bounded budget near this source-closure NO, and any uniform sublinear replacement of (2). A finite-precision procedure whose bounded neighborhood commits to such a finite budget has the same obstruction. Algebraic input encodings are discrete and may be arbitrarily large: no noncomputability or undecidability conclusion follows.

The attempted general upper-compression theorem remains unresolved. Caratheodory bounds a real residual measure, critical finiteness bounds distinct types, retained-tail compression gives an existential finite prefix, and the algebraic critical census bounds a named critical presentation. None supplies an upper bound for one actual finite word across the full fixed/read-only coupled fibre and all rank strata. The remaining gate is a source-complete input-effective upper bound or an equally complete rejection method, covering strict endpoints, zero-gap and singular strata, alternative cores and actual shared parameters. This note adds a concrete quantitative constraint that any such method must accommodate.

Evidence: hand mathematics plus [the additive checker](check_log_product_count.py), [PASS receipt](log-product-count-test-receipt.json) and [captured-buffer execution authentication](LOG-PRODUCT-EXECUTION-AUTHENTICATION.json). Author execution passed 69 checks, including the uniform rational rate inequalities and three certified compact source descriptions at N=2^200,2^220,2^240. The nine finite substitutions supporting the defect identity do not establish its general factorization, which remains hand algebra. The script uses the prior certificate only as authenticated captured JSON data. The original source laws and prior proofs retain their authors and review receipts. No Lean/compiler, QE, native producer, source-size search, old source mutation or historical checker replay occurred here. General G3 remains in progress.
