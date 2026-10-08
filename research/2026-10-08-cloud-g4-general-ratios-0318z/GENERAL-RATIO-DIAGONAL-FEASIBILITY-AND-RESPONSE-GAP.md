# Other cell ratios can cancel the fifth diagonal in actual positive words

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 03:18 UTC. **SOURCE-ONLY HAND ANALYTIC CANDIDATE; UNCOMPILED; independent review pending.** All rational calculations below are hand derivations. No deterministic symbolic exploration, coefficient harness, source producer, parameter scan, numerical job, API or compiler ran.

The accepted [moving-base theorem](../2026-10-08-cloud-g4-moving-base-0242z/MOVING-BASE-FIFTH-DIAGONAL-OBSTRUCTION.md) excludes the half-coin three-cell family with limiting ratios (1,2,1). Does its fifth-diagonal sign extend to every positive ratio triple? It does not. This note gives an exact positive-source family with ratios (1,6,10) whose ordinary no-merger diagonals match through five roots. In the displayed chronological order its full C/H response cannot be ordinary, so this is not an ordinary-return or factor-membership theorem.

## 1. Original actual sources and inherited finite coefficients

Use three serial private natural INDEPENDENT bigons. Each CURRENT ROOT routes independently with coin 1/2; a merged subtree routes as one root. For fixed A_i>0 take

    x_i=1-A_i t-sqrt(w_i)t^(3/2),
    y_i=1-A_i t+sqrt(w_i)t^(3/2),       t>0, w_i>=0,     (1)

with both arms and all ordinary connectors/pads strictly between zero and one. All probabilities below use this SAME physical parameter assignment across arities. The original routing formula is

    b_n(B_i)=2^-n sum_(k=0)^n binom(n,k)
               x_i^lambda_k y_i^lambda_(n-k),
    lambda_n=binom(n,2).                               (2)

Define D3,D4,D5 as the Newton log differences in the [accepted source coefficient derivation](../2026-10-08-cloud-g4-moving-base-0242z/MOVING-BASE-FIFTH-DIAGONAL-OBSTRUCTION.md), Section 3. No-merger diagonals multiply under actual private serial grafting, so these defects add, and every ordinary source edge has zero defect. Uniformly for fixed A and bounded w, the exact finite n<=5 routing polynomials give

    D3(B_i)=(-A_i^3/8+3w_i/4)t^3+O(t^4),
    D4(B_i)=(3A_i^4/16-3A_i w_i/2)t^4+O(t^5),
    D5(B_i)=(-3A_i^5/8+15A_i^2 w_i/4)t^5+O(t^6).       (3)

These coefficients are identities in the actual A,w, not free formal coordinates. The symmetric routing sums are polynomial in h_i^2=w_i t^3, and their logarithms have analytic extensions at t=0. Thus the three normalized WHOLE-WORD maps D3/t^3,D4/t^4,D5/t^5 are jointly analytic in (t,w). Negative t is only an analytic calculation point; realizing sources always have positive t.

For arbitrary actual paths at fixed positive A, exact D3=0 forces bounded w, by the same source-ratio argument as in the accepted moving-base proof: each exact ratio

    b3(B_i)/b2(B_i)^3
      =1+t^3[(3/4)(1-A_i t)w_i-A_i^3/8]/(1-A_i t/2)^3

has an equal-arm lower bound 1-Kt^3>0; their product is one, so each has an upper bound 1+K't^3. Substitution gives a finite upper bound on every w_i. Constants may depend on this fixed ratio triple. No free compactness premise is needed for the limiting feasibility analysis.

## 2. The precise leading moment gate

Write S_j=sum_i A_i^j. Exact D3=D4=0 forces

    sum w_i=S3/6+O(t),
    sum A_i w_i=S4/8+O(t).                             (4)

If D5=0 as well, its necessary leading third moment is

    sum A_i^2 w_i=S5/10+O(t).                          (5)

Let M0=S3/6 and define

    mu=3S4/(4S3),          nu=3S5/(5S3).               (6)

Any limiting nonnegative weights solving all three leading equations give a probability distribution p_i=w_i/M0 supported on the three actual values A_i, with mean mu and second moment nu. Conversely, such a distribution supplies exactly those leading weights. Thus the leading gate is precisely

    (mu,nu) in conv{(A_i,A_i^2):i=1,2,3}.              (7)

For distinct sorted ratios a<b<c this is the explicit finite set of inequalities

    a<=mu<=c,
    L(mu)<=nu<=U(mu),
    U(mu)=(a+c)mu-ac,
    L(mu)=(a+b)mu-ab       if mu<=b,
          (b+c)mu-bc       if mu>=b.                  (8)

The lower boundary is the two adjacent-node interpolation of the convex parabola; the upper boundary is its endpoint chord. These statements follow directly by convex combinations, not an inference of actual-word membership from matrix positivity.

This also identifies the sign gate under only exact D3=D4=0. Along any bounded-weight subsequence the fifth coefficient lies in the interval obtained from

    -3S5/8+(15/4) M0 v,       L(mu)<=v<=U(mu).         (9)

If nu<L(mu), it is uniformly positive for all sufficiently small actual sources satisfying the lower equalities; if nu>U(mu), it is uniformly negative. The finite margin and forced boundedness give these uniform conclusions by taking subsequential limits in (3),(4). If the point (mu,nu) lies strictly inside the triangle, a strictly positive leading solution exists. The next section shows that such an interior solution does extend to exact actual diagonals. Boundary solutions, repeated ratios and full forest equality are separate questions.

## 3. An explicit strictly positive 1:6:10 solution

Take the ordered fixed ratio triple

    A=(1,6,10),
    S3=1217,       S4=11297,       S5=107777,
    w0=(393/50,327281/2400,9377/160).                 (10)

Every entry is strictly positive. Exact hand substitution gives

    sum w0_i=1217/6,
    sum A_i w0_i=11297/8,
    sum A_i^2 w0_i=107777/10.                         (11)

For transparent common-denominator checks, write w0=(18864,327281,140655)/2400. The three numerators after multiplication by 1,A,A^2 are respectively

    486800,        3389100,        25866480,

which are 2400 times the three right sides of (11). This is arithmetic in the preserved hand proof, not an executed harness. Positivity places (mu,nu) strictly inside the moment triangle.

Let F(t,w) be the EXACT normalized source vector

    F=(D3(word)/t^3,D4(word)/t^4,D5(word)/t^5).         (12)

Ordinary connectors do not enter F. By (3),(11), F(0,w0)=0. Its w-Jacobian is

    [3/4              3/4             3/4;
     -3A1/2           -3A2/2          -3A3/2;
     15A1^2/4         15A2^2/4        15A3^2/4].       (13)

Its determinant is the product of the three row constants and the Vandermonde determinant:

    -(135/32)(A2-A1)(A3-A1)(A3-A2)
      =-(135/32)(5)(9)(4)=-6075/8 !=0.                (14)

The analytic IFT therefore gives an actual analytic w(t) with w(0)=w0 and F(t,w(t))=0 exactly. At sufficiently small positive t, w_i(t)>0 and the actual arm values (1) lie strictly between zero and one: bounded sqrt(w_i)t^(3/2) is smaller than A_i t, and all arms tend to one from below. Coins remain exactly 1/2. This is an exact strictly positive finite source family, not a formal product or a truncated root.

For these sources D3=D4=D5=0 implies, successively,

    b3=b2^3,       b4=b2^6,       b5=b2^10.            (15)

The normalized source IFT solves three REAL equations with the SAME three physical arm-difference parameters. It makes no claim about an additional higher coordinate or about independent fits at different arities.

The exact source consequence is stronger than failure of a uniform positive bound. There are actual lower-diagonal families with either fifth sign nearby. At the leading level perturb w0 by

    w0+delta(-4,9,-5).                                (16)

Both sums in (4) are unchanged, while the A^2-weighted sum changes by -180delta. For small fixed positive or negative delta, every weight stays positive. Hold w3=w0_3-5delta and apply the two-equation IFT to D3/t^3,D4/t^4 in w1,w2; the minor is -45/8, so exact lower-diagonal matching exists. Its fifth coefficient is -675delta, by (3). Thus small positive delta yields a strictly NEGATIVE fifth defect for sufficiently small positive t; negative delta yields a positive one. These are still genuine source diagonals, and still do not assert full kernel equality.

## 4. Calibration to ONE fixed positive ordinary diagonal target

Fix a in (0,1) BEFORE choosing t. Choose the two actual internal connectors and a trailing ordinary edge all with survival z=1-t. Their durations -log(1-t) are strictly positive and finite. The uncalibrated word pair survival is

    q_raw(t)=product_i(1-A_i t/2)(1-t)^3 ->1.           (17)

For sufficiently small positive t, a<q_raw(t)<1. Supply a genuine leading ordinary population with survival

    zeta(t)=a/q_raw(t) in (0,1),
    duration -log zeta(t)=-log a+log q_raw(t)>0.        (18)

This preserves three bigons and positive connectors. Every arm duration is -log x_i or -log y_i, positive and finite. No physical inverse, negative duration, removed protected edge or limiting zero-edge source is used. Ordinary calibration changes log b_n only by lambda_n log zeta and preserves every D_j exactly.

Consequently the calibrated actual word has

    b_n=a^lambda_n,           n=0,1,2,3,4,5,           (19)

for every sufficiently small positive t in the analytic family. The target a is unchanged throughout. If desired a may equal sqrt(q/r) from the accepted fixed-budget two-factor route, but (19) says only that its DIAGONALS agree with each required factor. It does not realize their prescribed shears or any higher cap.

## 5. Exact full-response obstruction in this chronological order

The original four-root quotient of a bare half-route cell has H_i=0 and

    c_i=C(B_i)=(A_i^3/12-w_i/2)t^3+(A_iw_i/4)t^4.      (20)

For the exact family w(t)->w0, its leading coefficients are

    gamma1=-577/150<0,
    gamma2=-240881/4800<0,
    gamma3=51869/960>0.                               (21)

Hence c1<0,c2<0,c3>0 for sufficiently small positive t. This is a statement about the SAME actual arm parameters that solve (12), not a separate sign ansatz.

Now allow ANY strict internal connector survivals z1,z2, not only the calibration choice (17). Write Q_i=b2(B_i)>0 and R_i=b4(B_i)>0. Exact original serial quotient composition gives for the body B1 E(z1) B2 E(z2) B3

    C=alpha1 c1+alpha2 c2+alpha3 c3,
    D=C+H=beta1 c1+beta2 c2+beta3 c3,

    alpha1=z1 z2 Q2 Q3,
    alpha2=R1 z1^6 z2 Q3,
    alpha3=R1 R2 z1^6 z2^6,
    beta1=1,  beta2=R1 z1^6,  beta3=alpha3.            (22)

All coefficients are strictly positive, and their exact ratios satisfy

    beta1/alpha1=1/(z1 z2 Q2 Q3)
      >beta2/alpha2=1/(z2 Q3)>beta3/alpha3=1,          (23)

because z1 Q2<1 and z2 Q3<1. If C=0, substitute alpha3 c3=-alpha1 c1-alpha2 c2 in D:

    D=alpha1 c1(beta1/alpha1-1)
             +alpha2 c2(beta2/alpha2-1)<0.             (24)

Thus C=H=0 is impossible at these SAME source parameters, whatever the positive connectors are. This is the source-faithful chronological two-moment obstruction; no unobserved calendar law is assumed.

Genuine leading/trailing ordinary padding E(zeta),E(u) changes the quotient by

    C_full=zeta^6 u C,
    H_full=zeta^6[H+(1-u)C].                          (25)

If C_full=0 then C=0, and (24) gives H_full=zeta^6 H<0. Therefore the calibrated fixed-a sources of Section 4 cannot equal the complete ordinary cap-four forest kernel even though ALL no-merger diagonals through five roots are ordinary. The quotient C,H is reconstructed from the original authorized full forest tomography; an additional hidden observation is not introduced. This obstruction holds for this chronological sign arrangement, not all permutations or all words.

## 6. What is decided, and the next actual source equation

The earlier 1:2:1 moving-base fifth obstruction is accepted and unchanged. It cannot be promoted to all positive cell ratios: an interior moment solution produces an exact actual diagonal family, and even nearby negative fifth defects occur under the lower equalities. Architecture need not change merely to cancel the fifth DIAGONAL.

The ordered 1:6:10 construction nevertheless fails the complete cap-four ordinary response by (24). A permutation placing its positive c cell between its negative c cells removes this particular one-sign-change separator, but does not solve C=H=0, the remaining exact forest equations, the prescribed P/R responses or any higher arity. A next bounded source task may examine that exact permutation and legitimate connector freedom; it must derive joint equations from the same parameters, rather than declare diagonal feasibility sufficient.

Original G4 still asks for finite positive inequivalent exact rivals after every FULL legal finite prefix of ONE fixed target, or full-rival finite forcing with effective detectable stopping. Both padded factors' actual membership at every cap under the same fixed q,r budget, higher forest grades, unknown bare/menu completeness and all-arity compatibility remain open. This packet supplies no full ordinary return, no full-factor realization, no global nonstopping result and no Lean theorem.

Attribution: original iid-current-root routing, serial quotient and legal tomography retain their inherited contributors. Dot supplied the accepted uniform-time source family and exact lower-coordinate polynomials. The general moment gate, explicit 1:6:10 source IFT, nearby sign contrast and exact chronological limitation are this packet's hand-derived contribution. Finite-dimensional convex hulls, Vandermonde determinants and the analytic IFT are classical tools; historical novelty is not claimed.
