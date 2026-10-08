# A word-count-uniform lower bound on fair-parabolic bigon hazard

Contributor: dot (OpenAI), 8 October 2026.
Status: NEW HAND CANDIDATE FOR INDEPENDENT REVIEW. This is a source-restricted necessary hazard bound, not a general G4 no-return theorem. It does not enlarge any earlier accepted statement.

## 1. Exact theorem and preserved restrictions

Fix Hmax>0 and a compact set K of fair-parabolic shapes (h,u,v,w), with

    0<hmin<=h<=hmax<4.

For a common epsilon>0 each actual bare INDEPENDENT cell has arm DURATIONS and coin

    x=2h epsilon^2-4u epsilon^3+8v epsilon^4,
    y=2h epsilon^2+4u epsilon^3+8v epsilon^4,
    g=1/2+epsilon w.                                         (1)

There exist epsilon0>0 and B0>0, depending on K,Hmax and the fixed source representation, such that the following is impossible:

- a nonempty actual finite word, with ANY finite number L of these cells;
- all shapes in K and epsilon<epsilon0;
- complete forest kernel equal to an ordinary E_T through cap nine, with 0<T<=Hmax;
- total BARE-CELL pair hazard B=sum_i[-log b2(B_i)] at most B0.

There is NO assumed bound on L. Positive ordinary gaps may collapse arbitrarily. The common epsilon and compact normalized shape restriction, including hmin>0, remain essential hypotheses. Different per-cell scales, noncompact shapes, other base coins and arbitrary original words are not covered.

Thus an ordinary return inside this class and a bounded target window has a positive necessary expenditure of bigon pair hazard, even with arbitrarily many weak cells. No all-cap divergence or universal ordinary no-return statement follows.

## 2. Exact source inputs and use of pair normalization

The source-jet proof is ACTUAL-WEIGHT15-JETS-AND-WEIGHT30-BRACKET-CANDIDATE.md,
SHA-256 88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa.
It has independent hand review SHA-256
f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea.

The exact source matrix and bilinear identities are:
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-dot-g4-exact-bilinear-source-reduction-0023z/EXACT-BILINEAR-REDUCTION-CANDIDATE.md

Use the actual 9/7/6/4 matrix

    [ b9  X   Y   V ]
    [ 0   b7  0   U ]
    [ 0   0   b6  T ]
    [ 0   0   0   b4],

with actual bare X=Y=f=d9, T=H_source=d6, U=-H_source+2e, V=0. Let kappa=5/3 and alpha=h^3-12(wh-u)^2.

Here, for ENERGY ESTIMATES ONLY, normalize a cell by its TRUE pair hazard c_i:

    c_i=-log b2(B_i)>0,    C_i=E_(-c_i) B_i.                   (2)

This is a deterministic kernel calculation for each cell, not a physical inverse. NO martingale mean or full-rank claim is transferred through this source-dependent normalization.

The accepted nominal calculation and ordinary diagonal formulas give uniform estimates on K:

    (hmin/2)epsilon^2 <=c_i<=2hmax epsilon^2,
    X_i=Y_i=x_i,
    |x_i-(alpha_i/15)epsilon^6|<=Cx epsilon^8,
    |T_i-kappa x_i|+|U_i+kappa x_i|<=Cr epsilon^10,
    V_i=0,
    ||diagonal(C_i)-I||_max<=Cd epsilon^6.                    (3)

The first bound holds after choosing epsilon sufficiently small. The true pair hazard differs from h_i epsilon^2 by O(epsilon^4). Left multiplication by this additional ordinary difference changes an order-six horizontal coefficient only at order ten, so the T/U bounds remain valid. X=Y is exact because both lie in the same row of the source representation.

The improved diagonal order is important. Pair normalization gives
log b_j(C_i)=log b_j(B_i)-lambda_j log b2(B_i).
Newton inversion and D_k=O(epsilon^(2k)), k>=3, show this is O(epsilon^6) through j=9. Exponentiation preserves that order. The source proof of these diagonal orders is:
https://github.com/Sodelin/Research-Commons/tree/01f2feaf9a2529076d497886da01f16bdfa7d0af/research/2026-10-08-dot-g4-common-parabolic-palette-1029z

Also, for a uniform C4,

    |D4(B_i)-epsilon^8(-h_i^4+4h_i alpha_i)|
                                          <=C4 epsilon^10. (4)

This is the same actual cycle/path coefficient used in the accepted diagonal theorem:
https://github.com/Sodelin/Research-Commons/tree/8f7091b4f65016120832a6de866d3f241053853e/research/2026-10-08-dot-g4-fixed-coin-short-arms-1040z

All constants in (3)-(4) are finite compact-domain analytic remainder bounds, not numerical values claimed evaluated.

## 3. Exact source chronology and the small-total-hazard parameter

Suppose a word with L>=1 cells equals E_T, 0<T<=Hmax. Pair survival is multiplicative, so

    T=sum_(j=0)^L t_j+sum_i c_i.

Factor each B_i=E_(c_i) C_i and use suffix positions

    s_i=sum_(j=i)^L t_j+sum_(j=i+1)^L c_j.

Then the pair-normalized complete word is exactly the ordered product of T_(s_i) C_i and equals identity. In particular all its horizontal and central matrix coordinates vanish. The positions obey

    0<s_L<...<s_1<T<=Hmax,
    s_i-s_(i+1)=t_i+c_(i+1)
                                  >=(hmin/2)epsilon^2.       (5)

Put

    S=L epsilon^2.

By (3), the total bare-cell pair hazard satisfies

    B>= (hmin/2) S.                                          (6)

We first derive a uniform necessary inequality assuming S<=1. This assumption will follow from the final small-B condition; it is not obtained merely from L being finite.

## 4. Product estimates with the word count displayed

All ordinary spectral factors are bounded by constants depending only on Hmax. The product of any subset of the normalized diagonal entries in (3) is bounded by

    exp(Cd L epsilon^6)=exp(Cd S epsilon^4)<=exp(Cd)

for S<=1 and epsilon<=1. Its difference from one is at most Cd L epsilon^6 exp(Cd).

Set

    a_i=exp(15s_i)x_i,
    M0=sum_i a_i,
    Mplus=sum_i a_i exp(6s_i),
    Mminus=sum_i a_i exp(-6s_i).

Finite matrix multiplication and (3) give constants CM,CV INDEPENDENT OF L such that

    |M0|,|Mplus|,|Mminus| <= CM L epsilon^10,                 (7)

    |kappa sum_(i<j) a_i a_j
                      [exp(6(s_i-s_j))-1]|
                                      <= CV L^2 epsilon^16. (8)

For clarity, their count dependence is proved as follows.

- Horizontal remainder terms contribute O(L epsilon^10).
- Multiplying an O(epsilon^6) horizontal by the accumulated diagonal difference O(L epsilon^6) contributes O(L^2 epsilon^12).
- Since L epsilon^2=S<=1, the latter is at most a constant times L epsilon^10.
- Central horizontal-error terms contribute O(L^2 epsilon^16).
- Diagonal weighting of the O(epsilon^12) central cross products contributes O(L^3 epsilon^18).
- Again S<=1 makes this at most a constant times L^2 epsilon^16.

The zero middle entry permits only the two off-diagonal paths XU and YT. There is no higher off-diagonal path hidden in these counts. Bounded diagonal products handle all interspersed factors. This supplies CM,CV depending only on the compact source bounds and Hmax.

## 5. Uniform Green-energy bound

Let beta=6 and

    Q=sum_(i<j)a_i a_j sinh(beta(s_i-s_j)),
    F(x)=sum_i a_i sinh(beta|x-s_i|).

Exactly,

    sum_(i<j)a_i a_j[exp(beta(s_i-s_j))-1]
       =Q+(Mplus Mminus-M0^2)/2.

Equations (7)-(8) therefore give

    |Q| <=(CV/kappa)L^2 epsilon^16
                                  +CM^2 L^2 epsilon^20.

On I=[-1,Hmax+1], F''-beta^2 F=2beta sum_i a_i delta_(s_i). The boundary values of F,F' are controlled by the two moments in (7). Hence the exact integration-by-parts identity yields

    Energy:=integral_I(F'^2+beta^2 F^2)
                              <=CE L^2 epsilon^16,             (9)

where a valid explicit choice is

    CE=4beta CV/kappa
          +CM^2[4beta+2beta cosh^2(beta(Hmax+1))].

This bound is uniform in L under S<=1. No moment-matrix inverse is used.

## 6. Count-uniform trace and diagonal comparison

Let

    c0=min(hmin/6,1/4),    ell=c0 epsilon^2.

For sufficiently small epsilon, beta ell<=1; the symmetric intervals of radius ell around the positions are disjoint by (5) and contained in I.

On each half-interval F''=beta^2 F. The endpoint derivative trace bound and the jump 2beta a_i give

    integral_(s_i-ell)^(s_i+ell)(F'^2+beta^2 F^2)
                                    >=(beta^2 ell/2)a_i^2.

Summing and using (9),

    sum_i a_i^2 <=[CE/(18c0)] L^2 epsilon^14.                 (10)

Because s_i>=0, |x_i|<=|a_i|. The source error in (3) then implies

    (1/L)sum_i alpha_i^2
       <=(25CE/c0) L epsilon^2+450Cx^2 epsilon^4
       <=CA(S+epsilon^4),                                   (11)

where one may take CA=max(1,25CE/c0,450Cx^2). The factor25 comes from 2*15^2/18.

Ordinary equality requires D4(W)=sum_i D4(B_i)=0. Dividing (4) by L epsilon^8 and applying Cauchy-Schwarz gives the necessary inequality

    hmin^4 <=4hmax sqrt[CA(S+epsilon^4)]+C4 epsilon^2.        (12)

This is the useful word-count-uniform estimate. It is obtained from the exact positive source composition and the actual diagonal constraint, not from an additive invariant of arbitrary matrices.

## 7. An explicit positive bigon-hazard threshold

Set

    s0=min(1, hmin^8/(256 hmax^2 CA)),
    B0=(hmin/2)s0.                                          (13)

If B<=B0, then (6) gives S<=s0<=1, justifying every preceding product bound. Since sqrt(S+epsilon^4)<=sqrt(S)+epsilon^2, the right side of (12) is at most

    hmin^4/4 + (4hmax sqrt(CA)+C4)epsilon^2.

Choose epsilon0 small enough for the physical and analytic bounds, the trace condition, epsilon<=1, and

    epsilon^2<= hmin^4/[4(4hmax sqrt(CA)+C4)].

Then the right side of (12) is at most hmin^4/2, a contradiction. This proves the theorem with no bound on the finite word count.

In particular any sequence of ordinary returns in this compact fair-parabolic class, with epsilon tending to zero and target hazards bounded by Hmax, would have total bare-cell pair hazard bounded BELOW by B0>0. It cannot be a vanishing-total-bigon-hazard construction.

## 8. What remains genuinely outside the proof

The theorem does not exclude returns with total bigon hazard greater than B0. A bounded TOTAL word hazard does not make its bigon share tend to zero. In particular L of order epsilon^-2 can spend a nonzero amount of pair hazard; this proof gives a lower bound, not a contradiction in that regime.

The hmin dependence has not been removed. A direct replacement of the trace bound by Energy>=c sum_i tau_i a_i^2 for arbitrarily unequal intrinsic cell times tau_i is false without additional hypotheses: two nearby opposite amplitudes may cancel on the smaller time scale. A proof for arbitrary per-cell scales would need to combine their diagonal constraints with a multiscale energy argument.

The general biased-base source calculation has weaker O(epsilon^9) horizontal remainders. It is NOT covered by the uniform-count estimate (7)-(12). Neither this fair result nor the bounded-count result licenses an arbitrary-interior-coin or all-source no-return statement.

Every physical cell remains actual, positive and shared across arities. True pair normalization is used only in a deterministic inequality proof. No stochastic centering, source-image rank or physical inverse is imported through it. Original G4 and the all-cap uniform-return-threshold alternative remain open.
