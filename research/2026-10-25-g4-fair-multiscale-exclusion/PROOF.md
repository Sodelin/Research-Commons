# Exclusion of arbitrary multiscale fair weak returns at bounded hazard

25 October 2026. dot (OpenAI-assisted research), prepared for Nolan.
**Scoped hand-reviewed theorem relative to the cited accepted source identities.** See REVIEW.md. No new mathematical runtime or formal verification. This reuses the accepted cap-nine source representation, cap-six covector, and full-operator identity. It does not assert original G4 closure.

## Theorem

For every finite H>0 there is epsilon(H)>0 such that no nonempty finite serial word of fair independently routed bigons, with actual positive arm durations a_i+b_i and a_i-b_i and positive ordinary connectors, can have complete labelled forest kernel E_h through cap nine, 0<h<=H, if max_i a_i<epsilon(H).

There is no count bound, common scale, normalized-shape compactness, or small-total-bigon-hazard assumption. Fair coins, serial source grammar, all-small arms, complete cap-nine equality, and bounded target pair hazard remain essential. In particular this would not handle persistent nonweak cells, biased coins, arbitrary original architectures, or all finite natural-I panels. Any original legal-observation application still needs the accepted eligible-wrapper tomography, not direct observation of hidden forests.

The improvement over the accepted compact-fair proof is to KEEP the quadratic diagonal correction and control it using short physical-time intervals, rather than assume each normalized defect is small.

## 1. Sequential setup and inherited local facts

Suppose a counterexample sequence exists with A=max a_i tending to zero. Put z_i=b_i^2, and

    L=sum a_i, S=sum a_i^3, R=sum a_i^4,
    S6=sum a_i^6, Z=sum z_i, T=sum a_i^2 z_i, M=sum a_i z_i.

All sums are finite for each word, but counts may grow. Write c_i=-log q2(B_i). For small a_i, the previously proved fair pair bound gives c_i>=a_i/4; also c_i<=C a_i uniformly for 0<=z_i<a_i^2. Pair matching gives sum c_i<=H, hence L<=4H. In particular S<=A^2 L tends to zero.

The accepted scalar expansions, summed with uniform analytic remainder ideals, give

    Z=S/6+O(A S),                                          (1)
    0=3R/16-3M/2+O(sum a_i^5+T+sum z_i^2).                (2)

The cap-six pair-normalized source J_i=B_i E_(-c_i) satisfies in a fixed full-forest matrix norm

    J_i-I=(a_i^3/8-3z_i/4) U3+R_i,
    sum ||R_i|| <= C A S,                                 (3)

after (1). Here the full-operator identity V3=−3U3/4 is the accepted direct labelled-forest hand identity, valid for arbitrary opaque incoming roots. The analytic remainder before summing is O(a^4+a z+z^2). The published covector ell gives uniformly at ordinary placements p in [0,H]

    v0 Ad_p(J_i-I) ell = exp(-9p) a_i^2 z_i/4
                         +O(a_i^6+a_i^3 z_i+z_i^2).       (4)

These are exactly the local inputs of the accepted count-uniform cap-six argument, with (3) additionally using the accepted operator identity.

## 2. Extending the cap-nine energy estimate to these scales

This is the first load-bearing extension checked in the scoped hand review.

Use the accepted 9/7/6/4 upper-triangular source representation, normalized as C_i=E_(-c_i)B_i. Its exact structural identities are X_i=Y_i=x_i, V_i=0. With kappa=5/3, analyticity of the fair source in (a,z) and the accepted fair-parabolic expansion give

    x_i=(a_i^3-6z_i)/120+O(a_i^4+a_i z_i+z_i^2),
    |T_i-kappa x_i|+|U_i+kappa x_i|
                         <=C(a_i^5+a_i^2 z_i+z_i^2),
    ||diag C_i-I|| <=C(a_i^3+z_i).                         (5)

Why the second remainder is justified beyond a compact parabolic chart: substitute a=2h epsilon^2 and z=16u^2 epsilon^6 into the analytic Taylor series. The accepted O(epsilon^10) remainder holds on an open set of h>0 and u^2>0. Thus every polynomial coefficient of weighted order below ten vanishes. The only monomials not divisible by a^5, a^2 z, or z^2 are exactly the forbidden lower weighted orders. The same argument gives the first remainder and diagonal estimate. The exact X=Y,V=0 identities are source identities, not inferred from a finite sample. Square-root analyticity is unnecessary: fairness makes the law analytic in z=b^2.

Let E=sum(a_i^5+a_i^2 z_i+z_i^2). Since z_i<=a_i^2, E<=C A^2(S+Z)<=C A^2 S. Also sum |x_i|<=C S and sum ||diag C_i-I||<=C S.

Repeat the accepted finite upper-triangular product accounting, now keeping norm sums rather than N epsilon powers. The diagonal products are bounded by exp(C S). If s_i are the decreasing physical suffix positions and w_i=exp(15s_i)x_i, define the same three horizontal moments M0,Mplus,Mminus. Exact ordinary equality implies

    |M0|+|Mplus|+|Mminus| <= C_H(E+S^2),
    |kappa sum_(i<j) w_i w_j [exp(6(s_i-s_j))-1]|
                                      <= C_H(S E+S^3).   (6)

The errors are, respectively, horizontal mismatch plus horizontal times accumulated diagonal error; and one mismatched horizontal in a two-edge path plus diagonal weighting of two horizontals. There are only the inherited XU and YT central paths, and no bare V term. Constants are independent of count.

For F(x)=sum w_i sinh(6|x-s_i|) on [-1,H+1], the SAME exact Green identity and boundary moment control yield

    ||F||_(H^1)^2 <= C_H [S E+S^3+(E+S^2)^2]=o(S^2).    (7)

Consequently the signed measures S^(-1)sum x_i delta_(s_i) converge weakly to zero: test F''-36F=12 sum w_i delta_(s_i) against a smooth cutoff times exp(-15x)phi(x), then use bounded total variation and density. The expansion in (5) gives

    S^(-1) sum (a_i^3-6z_i) delta_(s_i) -> 0 weakly.      (8)

Pass to a subsequence with total h convergent. Prefix positions p_i satisfy p_i=h-s_i-c_i, and max c_i=O(A), so (8) holds with p_i as well.

## 3. Retain, rather than discard, atomic diagonal corrections

Write d_i=(a_i^3-6z_i)/8. The exact normalized cap-six product, (3), and sum ||J_i-I||=O(S) imply that replacing its quadratic terms by d_i d_j Ad_(p_i)(U3) Ad_(p_j)(U3) costs O(A S^2); all cubic and higher products cost O(S^3). Both are o(S^2).

The normalized signed d measure tends weakly to zero by (8), with bounded total variation. The ordered two-point kernel has a continuous symmetric extension across the diagonal, exactly as in the accepted compact-fair proof. Its product-measure integral is therefore o(S^2). HOWEVER, the diagonal correction is not dropped: its absolute value is at most

    C_H sum d_i^2 <= C_H(S6+sum z_i^2).                    (9)

Applying ell, using the positive leading term in (4), and absorbing sum a_i^3 z_i<=A T, gives

    T <= C_H(S6+sum z_i^2)+o(S^2).                        (10)

The o(S^2) is along the alleged sequence; it need not have a claimed effective rate. In particular T=O(S6+S^2), because sum z_i^2<=Z^2=O(S^2).

Now sum a_i^5<=A R, S6<=A^2 R, and S^2<=A L R. Thus the error in (2) is o(R), and

    M=R/8+o(R), hence M>=R/16 eventually.                 (11)

Cauchy-Schwarz, (1), and (10) give

    c R^2 <= C_H S(S6+sum z_i^2)+o(S^3).                 (12)

The term S6 S/R^2 vanishes uniformly: S6<=A^2 R, S<=L^(1/3)R^(2/3), and R>=A^4 imply

    S6 S/R^2 <= L^(1/3) A^(2/3) ->0.                     (13)

Also S^3/R^2<=L<=4H, so the normalized o(S^3) in (12) is o(R^2).

## 4. Localize positive mass in physical time

The positive measures S^(-1)sum a_i^3 delta_(p_i) have mass one. Pass to a weakly convergent subsequence with limit nu. By (1),(8), S^(-1)sum z_i delta_(p_i) converges to nu/6. Choose a finite partition of [0,H] into K intervals of length at most delta, whose internal boundaries are not atoms of nu; a shifted uniform mesh gives K<=H/delta+2.

Let S_j,R_j,Z_j,L_j denote the sums within interval j. For this FIXED partition,

    Z_j=S_j/6+o(S) for every j,
    sum_i z_i^2 <=sum_j Z_j^2
                         =(1/36)sum_j S_j^2+o(S^2).     (14)

No factorization of correlated weak limits is used. This compares the actual positive measures in intervals and retains individual atomic squares via the inequality in (14).

Physical ordering supplies a local exposure bound. Prefix positions of consecutive cells differ by at least the earlier cell's c_i. Thus for all cells whose prefix is in one interval, the sum of their c_i is at most delta+max c_i: only the final cell can extend beyond the interval. Since a_i<=4c_i,

    L_j<=4delta+C A=:beta.                                (15)

This holds independently of the number of cells, including arbitrarily short connectors and highly unequal scales. Local Hölder gives S_j^3<=L_j R_j^2 and hence

    sum_j S_j^(3/2) <=sqrt(beta) R.                       (16)

For K nonnegative numbers S_j, norm comparison gives

    (sum_j S_j)(sum_j S_j^2)
                   <=K^(1/3)(sum_j S_j^(3/2))^2
                   <=K^(1/3) beta R^2.                  (17)

Indeed sum S_j<=K^(1/3)(sum S_j^(3/2))^(2/3), while sum S_j^2<=(sum S_j^(3/2))^(4/3).

Substitute (13),(14),(17) into (12), divide by R^2>0, and take the sequence limit with delta fixed:

    c <= C_H ·4delta·(H/delta+2)^(1/3).                  (18)

The right side tends to zero with delta. Choose a sufficiently small fixed delta to contradict (18). This proves the theorem, using the source-extension and product estimates (5)-(7) established above.

## 5. Exact significance and review scope

The proof does not assume the diagonal correction vanishes. Its mechanism is local physical-time exposure plus moment interpolation, converting concentrated defect mass into the small factor delta K^(1/3). The prior negative multiscale covector example remains valid: it does not satisfy K4, let alone the full cap-nine energy constraints.

The scoped hand review checks: analytic extension of the cap-nine coefficient ideals; the count-free sums in (6); weak-measure transfer and partition boundary handling; local exposure bound; and the inequalities (12)-(18). No additional polynomial coefficient, numerical base, or new source compiler execution is claimed.

The theorem only excludes all-small FAIR SERIAL returns at bounded target hazard. It would not supply a finite natural-I certificate against all original rivals, nor a fixed-target all-panel counterexample. A source-faithful extension dealing with genuinely biased weak cells and persistent nonweak components would remain necessary before this could become the decisive exact-fibre supplier.

## Attribution and immutable inputs

- Cap-nine exact source and energy proof: https://github.com/Sodelin/Research-Commons/blob/efd8ed7a9d23be13eede73019618c4cd4b62c23e/research/2026-10-08-dot-g4-fair-energy-hazard-1220z/WORD-COUNT-UNIFORM-FAIR-BIGON-HAZARD-BOUND-CANDIDATE.md . Its historical candidate header is governed by the packet's accepted review.
- Arbitrary-fair local cap-six/scalar estimates and prior count-uniform small-total-hazard theorem: https://github.com/Sodelin/Research-Commons/blob/941cb171242115236368c84774de1705c6fb3a44/research/2026-10-21-g4-count-uniform-hazard/PROOF.md .
- Complete cap-six covector source: https://github.com/Sodelin/Research-Commons/blob/6b876e4a138ad8d9c37ad78a6a95bd4fbf5744d8/research/2026-10-21-g4-positive-base-obstruction/ADDENDUM.md .
- Accepted full-operator identity and compact-fair cross-cap proof: [October22 source packet](https://github.com/Sodelin/Research-Commons/tree/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-22-g4-chronological-roughness), including THIRD-OPERATOR-IDENTITY.md, COMPACT-FAIR-NO-RETURN.md and COMPACT-FAIR-REVIEW.md.

This is a scoped hand proof, not a claim that search absence establishes novelty. The original master quantifiers remain unchanged. The source-byte editorial mapping and verification limits are recorded in EVIDENCE.md.
