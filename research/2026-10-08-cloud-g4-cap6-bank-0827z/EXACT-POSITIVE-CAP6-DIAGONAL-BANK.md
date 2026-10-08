# A different actual positive bank matches all ordinary diagonals through six

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 08:27 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No mathematical, symbolic, numerical, source, practical-solver, compiler, Actions or API execution occurred. The linear systems below are hand existence constructions, not executed parameter extractions. Metadata hashing does not check the mathematics.

The accepted eight-cell cap-five ordinary source has a strictly negative sixth Newton difference. Its fixed leading bank therefore cannot become an ordinary cap-six source by changing placements or later Taylor coefficients. This note changes the actual arm bank and proves exact diagonal feasibility through six, with several positive and negative third-source coefficients. It does **not** prove any full-forest ordinary return or prescribed-conjugator membership.

## 1. Actual cells and the four equations

Use the original private INDEPENDENT current-root bigon with fair coin, not independent rerouting of descendant leaves. For fixed positive means A_i put

    x_i=1-A_i*t-sqrt(w_i(t))*t^(3/2),
    y_i=1-A_i*t+sqrt(w_i(t))*t^(3/2),
    q_i=b2(B_i)=1-A_i*t/2,
    b_n(B_i)=2^-n sum_k binom(n,k)
                    x_i^binom(k,2)*y_i^binom(n-k,2).

All parameters are shared across every entering arity and every response coordinate. The [accepted general-ratio source calculation](../2026-10-08-cloud-g4-general-ratios-0318z/GENERAL-RATIO-DIAGONAL-FEASIBILITY-AND-RESPONSE-GAP.md) and [accepted sixth-source extension](../2026-10-08-cloud-g4-sixth-diagonal-0722z/SIXTH-DIAGONAL-SEPARATES-THE-CAP5-RETURN.md) give, for D_j=Delta_n^j log b_n at n=0,

    D3=(-A^3/8+3w/4)*t^3+O(t^4),
    D4=(3A^4/16-3Aw/2)*t^4+O(t^5),
    D5=(-3A^5/8+15A^2w/4)*t^5+O(t^6),
    D6=(15A^6/16-45A^3w/4)*t^6+O(t^7).          (1)

The sixth formula includes the original h^4 logarithmic cancellation; omitting that term would not justify it. The estimates apply to a fixed finite bank and a bounded positive-weight neighborhood. They are not uniform in cell count or arity.

No-merger probabilities multiply under original serial graft composition. Ordinary edges have D_j=0 for j>=3. Thus the four leading ordinary-diagonal conditions for a bank are exactly

    sum_i A_i^k*w_i = sum_i A_i^(k+3)/[2(k+3)],
    k=0,1,2,3.                                      (2)

Here w_i denotes the leading positive weight. This is a linear moment problem tied to the actual same arm means, not four independently supplied response coordinates.

## 2. A finite positive solution of all four moment equations

Choose a sufficiently large integer N ONCE, before taking t to zero, and set

    A_i=i/(N+1),  1<=i<=N,
    bar_w_i=A_i^2*(1-A_i)/2 >0.                      (3)

For k=0,...,3 the polynomial

    f_k(x)=x^k*x^2*(1-x)/2-x^(k+3)/[2(k+3)]

has integral zero on [0,1]: both terms integrate to 1/[2(k+3)(k+4)]. Let E_k=sum_i f_k(A_i). These are the raw errors in (2). They are uniformly bounded in N. Indeed |f_k'|<=k+3; the right-endpoint Riemann error with mesh 1/(N+1) is at most (k+3)/[2(N+1)]. Removing its endpoint x=1 changes the sum by f_k(1)=-1/[2(k+3)]. Consequently

    |E_k| <= (k+3)/2+1/[2(k+3)] <4.                 (4)

Fix four disjoint closed intervals I_j=[tau_j-h,tau_j+h], with tau_j=j/5, j=1,...,4, and h=1/100. Each lies strictly inside (0,1). Define

    M_kj(N)=sum_(A_i in I_j) A_i^k,  k=0,...,3.

The matrices M(N)/(N+1) converge to H_kj=int_(I_j) x^k dx. Explicitly, after division by 2h, the four rows of H are

    1; tau_j; tau_j^2+h^2/3; tau_j^3+tau_j*h^2.

Subtracting (h^2/3) times row0 from row2 and h^2 times row1 from row3 gives the ordinary four-node Vandermonde. Therefore

    det H=(2h)^4 product_(j<l)(tau_l-tau_j)>0.        (5)

For all sufficiently large N, M is invertible and M^-1=O(1/N). Solve the EXACT rational four-by-four system

    delta(N)=-M(N)^-1 E(N).                          (6)

Add delta_j to EVERY baseline weight whose mean is in I_j, leaving the other weights untouched. Call the results w_i^0. Equations (4)-(6) give delta_j=O(1/N). On the four fixed intervals the baseline x^2(1-x)/2 has a positive uniform minimum; choose N sufficiently large that each |delta_j| is less than half that minimum. All modified weights are positive, and all unmodified weights remain positive, including those near the endpoints. By definition of M, the resulting weights solve (2) exactly.

This gives an explicit finite rational construction conditional only on choosing N sufficiently large. No particular N or weight tuple has been extracted by execution. The argument requires no limit word and does not let N grow with t.

## 3. Several positive and negative source coefficients

The actual third-source coefficient is Gamma_i=A_i^3/12-w_i^0/2. Before correction,

    bar_Gamma(A)=A^2*(4A-3)/12.                     (7)

The grid intervals (1/10,3/20) and (9/10,19/20) avoid every correction interval. For N sufficiently large, each contains at least two grid points. At the former points Gamma_i<0; at the latter Gamma_i>0. Thus the bank has at least two coefficients of each sign. Other coefficients can vanish; no nonvanishing assertion for all cells is needed.

The first equation in (2) implies sum Gamma_i=0, as the original leading source requires. The remaining equations impose the actual same-mean constraints, rather than making the Gamma_i free signed weights. Multiple positive coefficients remove the premise of the one-positive-cell obstruction; they do not supply a full-response cancellation.

## 4. Exact actual diagonal matching by a source IFT

Fix such an N and its finite leading tuple. Select any four distinct grid means, keep all other weights fixed, and vary the corresponding four physical squared-arm weights. Define

    F(t,w)=(sum_i D3(B_i)/t^3,
            sum_i D4(B_i)/t^4,
            sum_i D5(B_i)/t^5,
            sum_i D6(B_i)/t^6).

This extends analytically through t=0. The original half-coin forest polynomials are even in the arm difference h, so substituting s=1-A_i*t and h^2=w_i*t^3 makes every finite-arity coefficient analytic in (t,w). The accepted expansions (1) show the required divisibility. The logarithms are analytic near their value b_n=1.

At t=0, F=0 by (2), and its four weight columns are

    (3/4, -3A_i/2, 15A_i^2/4, -45A_i^3/4)^T.

For increasing selected means, the determinant is exactly

    (6075/128) product_(j<l)(A_l-A_j)>0.             (8)

The analytic inverse-function theorem therefore supplies actual weights w_i(t)=w_i^0+O(t) satisfying D3=D4=D5=D6=0 EXACTLY for all sufficiently small positive t. Since N and every leading weight are fixed and positive, every corrected weight stays positive. Also sqrt(w_i(t))*sqrt(t)<A_i and A_i*t+sqrt(w_i(t))*t^(3/2)<1 for sufficiently small t. Hence every arm is strictly between zero and one. The half coin is strictly physical. The analytic extension at negative t is only a proof device; physical sources use t>0.

## 5. Same fixed positive target and actual ordinary calibration

Fix d in (0,1), independently of t. Give the word a leading edge and one ordinary edge after each cell, all with survival e^-t. Its raw pair survival is

    v_raw(t)=e^(-(N+1)*t) product_i (1-A_i*t/2) ->1.

For small positive t, d<v_raw<1. Append an ordinary population with survival z=d/v_raw in (0,1). Adjacent ordinary populations may be merged; all durations remain strictly positive. The resulting legal finite positive source K_t has b2=d. Calibration leaves D3,...,D6 zero. Binomial Newton inversion, with b0=b1=1, now gives

    b_n(K_t)=d^binom(n,2), 0<=n<=6.                 (9)

No connector is an inverse population and the target d does not depend on t or N. These same cells and weights define one original source at every arity, even though (9) is proved only through six. Cell order can be any fixed permutation without changing this diagonal statement.

The proposition is **exact actual diagonal6 feasibility**, not an ordinary full cap-six return, an open full-forest chart or membership of the original prescribed factors. The [complete six-root residual basis](CAP6-FULL-FOREST-RESIDUAL-COORDINATES.md) and [next source gate](NEXT-SOURCE-GATE.md) specify the genuine remaining equations.

Prior boundary: the inherited uniform-time rare-arm theorem already proves ordinary diagonal feasibility at arbitrary finite caps in a different actual source family. No historical novelty or new all-cap diagonal theorem is claimed. This fair, balanced, multi-sign bank is intended as a concrete higher-cap full-forest starting point after the accepted fixed eight-cell sixth defect.
