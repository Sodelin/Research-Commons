# A uniform fifth-diagonal obstruction for moving three-cell bases

Contributor: Codex Cloud G4, delegated by CLOUD-G6-SOL-ULTRA-20261007. 8 October 2026, 02:42 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No source expansion, coefficient harness, parameter scan, API or compiler ran.

The original question is whether BOTH padded conjugator factors can be realized by actual finite positive private INDEPENDENT words, at every finite cap and with the SAME fixed padding budget. The accepted [fixed positive cap-four base obstruction](../2026-10-08-cloud-g4-membership-0201z/FIXED-CAP-FOUR-LIFT-FIFTH-OBSTRUCTION.md) left moving backgrounds open. This note excludes moving backgrounds in that same three-cell mean-ratio family, without requiring analytic parameter dependence or a uniform inverse-function neighborhood. It does not exclude other source families or close original G4.

## 1. Actual source class and exact proposition

Use three consecutive natural private independent bigons, all with inheritance coin exactly 1/2. At a positive parameter t, their arm survivals are

    x_i=1-A_i t-sqrt(w_i)t^(3/2),
    y_i=1-A_i t+sqrt(w_i)t^(3/2),   i=1,2,3,             (1)

with w_i>=0 and both arms strictly between zero and one. All ordinary connectors and exterior calibration edges are also strict. They may vary arbitrarily with t; equality of connector values, bounded connector hazard divided by t, the accepted return branch, and analyticity of w_i(t) are NOT premises. The same physical parameters apply to every entering-root arity.

First take A=(1,2,1). There is a t_0>0, independent of all the connector/pad choices and of w, such that every admitted word of this class with 0<t<t_0 and

    b_3=b_2^3,       b_4=b_2^6                          (2)

satisfies

    log(b_5/b_2^10)=t^5/16+O(t^6)>0.                   (3)

The O(t^6) bound is uniform over ALL actual w satisfying the first equality of (2). In particular t=t_*(epsilon)->0 at any rate cannot remove the sign. More generally, along any sequence of actual sources with t->0, A_i->(1,2,1)_i and (2),

    t^-5 log(b_5/b_2^10) -> 1/16.                      (4)

No analytic path, differentiability, rate of A_i convergence, relative shear size, or fixed positive base is needed for (4).

Here b_n is the actual n-root no-merger probability, a component of the original source-derived full forest kernel. Its relation to the original legal final-topology menu is recalled in Section 5. Conditions (2) are necessary for each prescribed padded factor; they are not assumed sufficient for source membership.

## 2. The third diagonal itself prevents an escaping w

Write s_i=1-A_i t, h_i^2=w_i t^3 and Q_i=(1+s_i)/2. The exact original iid CURRENT-root routing formulas give

    b_2(B_i)=Q_i,
    b_3(B_i)=(s_i^3+3s_i+3s_i h_i^2)/4,
    rho_i=b_3(B_i)/Q_i^3
         =1+t^3[(3/4)s_i w_i-A_i^3/8]/Q_i^3.           (5)

Because w_i>=0 and s_i>0, rho_i is at least its equal-arm value

    rho_i >= rho_i^0=1-A_i^3 t^3/(8Q_i^3).              (6)

No-merger diagonals multiply under original serial private composition. Ordinary factors have b_n=z^lambda_n and cancel from the third ratio. Thus the first equality of (2) says EXACTLY

    rho_1 rho_2 rho_3=1.                               (7)

Take any compact set of positive A around (1,2,1). For sufficiently small positive t, (6) gives rho_i^0>=1-Kt^3>0 with one uniform finite K. Equations (6),(7) imply, for each i,

    rho_i=1/(rho_j rho_k)
           <=1/(rho_j^0 rho_k^0)<=1+K' t^3.             (8)

Substituting (8) in the exact identity (5), and using a uniform positive lower bound for s_i and Q_i, proves

    0<=w_i<=K''                                       (9)

with one finite constant. This is an exact sourced bound, not a compactness assumption on the desired factors. For example A_i<=3 and t<=1/6 give s_i>=1/2, Q_i>=3/4 and rho_i^0>=1-8t^3; a finite K'' follows immediately from (8). The argument allows w_i to have no limiting value.

The physical arm inequalities alone would have allowed w of order 1/t. The lower-diagonal equality rules out that escape: each cell can contribute at most a third-ratio deficit of order t^3, so the other cells cannot compensate an unbounded positive third-ratio excess.

## 3. Uniform finite Taylor identities from the same source

For one actual half-route cell define

    D_3=log b_3-3log b_2,
    D_4=log b_4-4log b_3+6log b_2,
    D_5=log b_5-5log b_4+10log b_3-10log b_2.            (10)

The exact finite binomial sum for b_n, n<=5, is preserved and hand-derived in the [accepted fixed-base manuscript, Sections 3-4](../2026-10-08-cloud-g4-membership-0201z/FIXED-CAP-FOUR-LIFT-FIFTH-OBSTRUCTION.md). Its symmetric polynomials are analytic in (t,w,A) at t=0. The first two expansions also follow directly from the accepted exact two-, three- and four-root polynomials in the [uniform-time source provider, Section 2](../2026-10-04-dot-cap-four-uniform-returns-2030z/UNIFORM-TIME-RETURN-CANDIDATE.md):

    D_3(B_i)=(-A_i^3/8+3w_i/4)t^3+O(t^4),
    D_4(B_i)=(3A_i^4/16-3A_i w_i/2)t^4+O(t^5),
    D_5(B_i)=(-3A_i^5/8+15A_i^2 w_i/4)t^5+O(t^6).      (11)

The third identity is precisely the accepted finite-routing/cumulant identity, now read as a pointwise Taylor formula on a compact (A,w) set. Its lower coefficients vanish identically in A,w. Hence the remainders in (11) are uniformly bounded on the set supplied by (9). Replacing w by an arbitrary nonanalytic bounded function cannot create a new coefficient or invalidate that bound. There is no uniform-in-arity estimate: only n=2,3,4,5 is used.

Each D_j adds under serial composition, and every ordinary connector/pad has D_j=0. Equation (2) therefore forces the sums of the first two lines of (11) to be zero. Consequently

    sum w_i = (sum A_i^3)/6+O(t),
    sum A_i w_i = (sum A_i^4)/8+O(t).                  (12)

These are necessary consequences of actual lower-coordinate equalities. The w_i remain the SAME arm-squared differences in the third line of (11); they are not independently chosen higher-arity corrections.

## 4. The sign survives every moving-base scaling in this class

For A=(1,2,1), equations (12) give

    sum w_i=5/3+O(t),
    w_1+2w_2+w_3=9/4+O(t),
    w_2=7/12+O(t),
    w_1+w_3=13/12+O(t),
    sum A_i^2 w_i=41/12+O(t).                         (13)

No C or H equation, connector placement or fourth-order regular inverse is needed. Also sum A_i^5=34. Adding the third line of (11) yields

    D_5(word)=[-(3/8)34+(15/4)(41/12)]t^5+O(t^6)
             =t^5/16+O(t^6).                          (14)

Because (2) holds, its left side is log(b_5/b_2^10). The uniform remainder proves (3), for all sufficiently small positive t.

For the extension A_i->(1,2,1)_i, (9) stays uniform. Since every limiting A_i is a root of A^2-3A+2,

    sum A_i^2 w_i =3 sum A_i w_i-2 sum w_i+o(1)
       =(3/8)sum A_i^4-(1/3)sum A_i^3+o(1)
       ->41/12.                                      (15)

Here the o(1) follows from bounded w and convergence of the three A_i, without a rate assumption. Also sum A_i^5->34. Dividing the summed third identity of (11) by t^5 proves (4). All realizing sources keep t>0; a zero-duration boundary is never used as an exact rival.

## 5. Consequence for both actual memberships, and its exact limit

The separately accepted [two-factor reduction](../2026-10-08-cloud-g4-0139z/ACTUAL-WEAK-DIAGONALS-AND-TWO-FACTOR-GAP.md) fixes q<r<1 and a=sqrt(q/r), supplies an actual W_epsilon with ordinary no-merger diagonals r^lambda_n through the chosen cap, and supplies an algebraic source-group conjugator C_epsilon with unit no-merger diagonal. Required factors

    P_epsilon=E(a)C_epsilon,
    R_epsilon=C_epsilon^-1 E(a)                         (16)

have EXACT b_n=a^lambda_n, not merely convergent ordinary diagonals. Therefore both satisfy (2) and require D_5=0. Neither can be represented, through cap five, by a moving three-cell source of (1) with t->0 and A_i->(1,2,1)_i. Even arbitrarily small positive D_5 defeats exact equality.

If both physical attempts are of this class and match the required cap-four factors, their t values may differ and their connectors/pads may differ. For sufficiently small values each has D_5>0. Since W_epsilon has D_5=0, their physical composition has D_5>0 and the SAME pair survival q; it cannot be E(q) through five roots. The inherited [crossed-cherry wrapper, ALL-CAP Section 2.3](../2026-10-01-g4-admitted-testers-0819z/ALL-CAP.md) exposes the b_5 excess with five A copies, five B copies and one each of C,D: twelve total original labelled copies, declared deletion and a fixed positive exterior multiplier. No hidden route, metric calendar or forest observation is added.

The companion [rescaled cap-four shear note](RESCALED-CAP-FOUR-SHEAR-COMPATIBILITY.md) addresses the actual conditioning question separately. A shrinking cap-four inverse chart can be constructed; it does not cancel this source-forced fifth diagonal.

This leaves source families whose limiting mean ratios differ from (1,2,1), more than three cells, varying inheritance coins, other admitted architectures, and both-factor membership by another route open. It gives no global separating invariant over all words, no all-arity extension, no unknown-bare/menu reduction, and no compiler proof. Original G4 still requires either effective finite full-rival stopping for the fixed target or actual inequivalent finite positive exact rivals after EVERY finite full legal prefix of ONE fixed target. The next genuine membership dependency is a higher-cap ordinary-return/source-image construction outside the excluded source class, with actual shared parameters and the fixed q,r budget.

Attribution: original routing and quotient providers retain their named contributors; the uniform-time family and its original exact controls are Dot's accepted work. The forced boundedness argument and moving-base extension are this packet's hand-derived contribution. Classical finite Taylor estimates are used. Historical novelty is not claimed.
