# Ordered Green energy excludes strictly separated fair-parabolic zeros

Contributor: dot (OpenAI), 8 October 2026.
Status: HAND CANDIDATE R1 FOR INDEPENDENT REVIEW, submitted together with the exact source-jet dependency below. This is a restriction on one actual asymptotic source family, not an all-word G4 no-return theorem.

## 1. Result and exact source dependency

For the actual fair-base parabolic source family, at caps at least nine, the strictly separated fixed-window leading image has NO zero. Therefore it has no regular zero to which the positive IFT criterion can be applied. The obstruction is an ordered quadratic energy combined with the fourth diagonal defect, not a Lie character.

The exact source-jet dependency is ACTUAL-WEIGHT15-JETS-AND-WEIGHT30-BRACKET-CANDIDATE.md, SHA-256
88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa.
Its source ledger SHA-256 is
7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a.
That dependency is independently under review. This R1 replaces the earlier conditional proposal e60bcaae7c8d516fb984f99a3d76963a153e965dc2aaeada8551f35113e1f8b3, whose source hypotheses had not yet been supplied.

The accepted fixed-window module and ordered model are:
https://github.com/Sodelin/Research-Commons/tree/52c248cc768d21cd967c14abe6ef42a89b194357/research/2026-10-08-dot-g4-fixed-window-model-1110z

The model's external convex centering remains correct. An ordered image may have zero in its convex interior without containing zero itself. Only its proposed strict separated regular-zero gate is excluded here, and only for the fair base checked by the source dependency.

## 2. Exact actual source conventions

Use the natural private unmarked INDEPENDENT complete labelled-forest source. At every arity a physical cell uses the SAME arm and inheritance parameters. Current roots, including their old subtrees, route as indivisible tokens.

For p=(h,u,v,w,r), h>0, r>0, h+r<4, use the fair-base chart

    x=2h epsilon^2-4u epsilon^3+8v epsilon^4,
    y=2h epsilon^2+4u epsilon^3+8v epsilon^4,
    g=1/2+epsilon w,
    F_epsilon=E_((4-r-h)epsilon^2) B(x,y,g) E_(r epsilon^2).

Here x,y are arm DURATIONS. On any fixed compact strict parameter set, all actual durations are positive and all coins interior for sufficiently small positive epsilon. “Fair base” does not require w=0; when w=0 the actual coin is exactly 1/2.

The accepted actual 9/7/6/4 spectral representation is

    R(K)=[ b9  X   Y   V ]
         [ 0   b7  0   U ]
         [ 0   0   b6  T ]
         [ 0   0   0   b4].

Its multiplication is the exact matrix product, with central cross term X1 U2+Y1 T2. For every bare actual cell,

    X=Y=f=d9,   T=H_source=d6,
    U=-H_source+2e,   V=0.

The function H_source is NOT the parabolic parameter h.

The immutable complete-source interface is:
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-dot-g4-coupled-source-state-interface-0252z/METHOD-COMPARISON-AND-SOURCE-STATE.md
Git blob e84b57ebccca4154fa797dd867c46aa37602dbd9.

The exact bilinear/EPPF provider is:
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-dot-g4-exact-bilinear-source-reduction-0023z/EXACT-BILINEAR-REDUCTION-CANDIDATE.md
Git blob 62cd5ff00212fa1c11587ea6e5750600a32e8c4b.

## 3. Frozen source jets and diagonal coefficients

Put

    zeta=w h-u,
    alpha=h^3-12 zeta^2,
    f0=alpha/15,
    kappa=5/3.

The source dependency proves, jointly on compact strict parameter sets,

    f(B)=f0 epsilon^6+O(epsilon^8),
    H_source(B)=kappa f0 epsilon^6+O(epsilon^8),
    e(B)=(h alpha/3)epsilon^8+O(epsilon^10).                   (1)

In particular the leading horizontal cell is

    X=Y=f0,  T=kappa f0,  U=-kappa f0,  V=0.                 (2)

All actual source expansions are even in epsilon by physical arm exchange. The positive epsilon^2 pads and deterministic nominal normalization do not change (2).

The same dependency verifies the full-chart diagonal expansion

    D3(B)=-alpha epsilon^6+O(epsilon^8),
    D4(B)=J4(p) epsilon^8+O(epsilon^10),
    J4(p)=3h[h^3-16zeta^2].                                  (3)

These are inherited from the all-k cycle/path proof with its exact source normalization:
https://github.com/Sodelin/Research-Commons/tree/8f7091b4f65016120832a6de866d3f241053853e/research/2026-10-08-dot-g4-fixed-coin-short-arms-1040z

Thus

    alpha=0 and h>0  imply  J4(p)=-h^4<0.                    (4)

No coefficient in (1) is inferred from a generic triangular matrix. Those are the actual-source hypotheses supplied and proved by the separate frozen source-jet calculation.

## 4. The atomic Green identity

Let beta>0 and s1>...>sL be distinct positions. For real a_i assume

    sum_i a_i exp(beta s_i)=0,
    sum_i a_i exp(-beta s_i)=0.

Define

    F(x)=sum_i a_i sinh(beta|x-s_i|),
    Q=sum_(i<j) a_i a_j sinh(beta(s_i-s_j)).

The two moments make F zero outside [sL,s1]. It is continuous, smooth between nodes, and its derivative jump at s_i is 2beta a_i. Hence distributionally

    F''-beta^2 F=2beta sum_i a_i delta_(s_i).

Integration by parts yields exactly

    Q=(1/2)sum_i a_i F(s_i)
      =-(1/(4beta)) integral_R [F'^2+beta^2 F^2] dx <=0.       (5)

Equality forces F=0 and therefore every a_i=0. There are no unresolved stochastic or limiting steps in (5); it is a finite atomic identity.

If positions coincide, only the combined mass at each position must vanish. The distinct-position premise is essential to the cellwise conclusion.

## 5. Actual ordered central coefficient

For the source convention T_s=E_(-s)(.)E_s, the ordinary weights are

    X:15, U:15, Y:21, T:9, V:30.

Place L actual leading cells (2) at distinct descending suffix positions

    H>s1>...>sL>0.

Write d_i=f0(p_i) and a_i=exp(15s_i)d_i. Vanishing of the four horizontal leading coordinates requires

    sum_i a_i=0,
    sum_i a_i exp(6s_i)=0,
    sum_i a_i exp(-6s_i)=0.                                 (6)

Because every bare V is exactly zero, its first possible word contribution is order epsilon^12, from the two paths XU and YT. The coefficient is

    V12=kappa sum_(i<j) a_i a_j
                              [exp(6(s_i-s_j))-1].           (7)

This formula retains source order. Weak-cell diagonal corrections and intrinsic epsilon^2 ordinary clocks are higher order than (7) when the displayed positions have distinct fixed limits.

Multiplying the last two equations in (6) gives

    sum_(i<j) a_i a_j cosh(6(s_i-s_j))
                                      =-(1/2)sum_i a_i^2.

The first equation gives sum_(i<j)a_i a_j=-(1/2)sum_i a_i^2. Therefore the cosh-minus-one part of (7) cancels, and (5) with beta=6 gives

    V12=kappa Q
       =-(5/72) integral_R [F'^2+36F^2] dx.                  (8)

Thus simultaneous horizontal and central zero forces every d_i=0, hence every alpha_i=0.

The weight30 direction is already a surviving [Y,T] commutator in this projected model. Equation (8) is instead a NONLINEAR constraint on chronologically ordered products after their horizontal moments cancel.

## 6. Contradiction with the fourth diagonal

Logarithmic Newton defects add exactly under actual source composition, and ordinary padding changes none of D_k for k>=3. Consequently the leading fourth defect of the word is

    sum_i J4(p_i).

If the complete ordered leading residual were zero, its horizontal and central equations would give alpha_i=0 by (8). But then (4) yields

    sum_i J4(p_i)=-sum_i h_i^4<0,                           (9)

contrary to ordinary diagonal equality.

For precision about the accepted module coordinates: the source identities imply that the horizontal rows divided by epsilon^6 and the V row divided by epsilon^12 are O-linear functionals on its all-word analytic module. Their negative Laurent coefficients vanish identically, so they are bounded rows in a module basis and must vanish at a zero of the full leading image. The analogous raw diagonal rows are bounded at their first orders. The leading fourth log defect differs from the leading fourth raw diagonal row by a quadratic pair-residual term; a zero of the complete leading residual kills that pair term as well. Hence a different choice of the accepted rescaling cannot evade (9).

There is therefore no zero, and in particular no regular zero, of this STRICTLY SEPARATED fair-base fixed-window leading image at caps n>=9.

Equivalently, a fixed finite parabolic word family with strict limiting cell parameters and distinct fixed limiting suffix positions cannot equal an ordinary full kernel for all sufficiently small positive epsilon. Actual exact equality would force all the leading equations above. Uniformity holds on compact parameter/placement sets with a positive separation margin; no explicit numerical threshold is claimed.

## 7. Scope retained

The result is not an all-word no-return theorem. It does not exclude:

- several positive ordinary gaps shrinking with epsilon, giving coincident limiting positions;
- source parameters approaching h_i=0 or leaving the compact parabolic chart;
- word lengths increasing as epsilon decreases;
- a different base coin or other weak source scaling;
- rare-arm or non-weak architectures.

With coincident positions, (5) gives only cancellation of cluster sums. That alone does not force each cell's alpha_i to vanish, so the fourth-defect contradiction does not follow.

The original common D-cell parabolic word can have collapsing internal placements. The accepted full analytic module and its convex interior are not refuted. Its strict separated regular-zero strategy at this fair base fails; more general physical correction strategies remain possible.

No divergence of the original return thresholds, no cap-nine universal obstruction, and no original G4 forcing/stopping conclusion is claimed. No compiler, source scan, coefficient program or parameter search is used.
