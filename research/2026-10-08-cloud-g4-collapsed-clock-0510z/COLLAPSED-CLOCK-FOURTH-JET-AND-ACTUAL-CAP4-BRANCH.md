# A physical collapsed-clock cap-four branch, with its full fifth-root gate retained

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 05:10 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No mathematical producer, coefficient expansion script, deterministic symbolic exploration, parameter scan, numerical solver, compiler, Actions or API ran. All expansions, counts and the analytic IFT below are hand arguments; hashes/links/readback are preservation metadata.

The [uniform response proof](../2026-10-08-cloud-g4-degenerate-response-0441z/UNIFORM-FIVE-RESPONSE-BOUND-AND-COLLAPSE-GATE.md) forces dominant-block ordinary connectors to collapse along hypothetical full cap-five returns, but does not exclude intrinsic clock-scale gaps. This note gives a genuine positive source scaling which survives COMPLETE cap four: each block's connectors have duration ell_j*t+v_j*t^2 with ell_j>0, and two actual second-order corrections make their inverse cap-four response exact. The whole FULL five-root residual is O(t^5), rather than the nonzero order-three interior jet. Its three fifth coefficients remain separate unresolved source equations; no full cap-five return or prescribed conjugator is claimed.

## 1. Actual cells and source clock moments

Use the SAME exact half-coin1:6:10 family as the [accepted diagonal result](../2026-10-08-cloud-g4-general-ratios-0318z/GENERAL-RATIO-DIAGONAL-FEASIBILITY-AND-RESPONSE-GAP.md). Each cell's arms are 1-A t plus/minus sqrt(w_A(t))*t^(3/2), with positive analytic w(t) solving D3=D4=D5=0 on the three-cell body. Parameters are shared over all input arities; no higher forest parameter is independently fitted. Its leading coefficients are

    gamma_1=-p=-577/150,
    gamma_6=-s=-240881/4800,
    gamma_10=q=51869/960=p+s.                         (1)

For a chronological order (A1,A2,A3), suppose the actual internal ordinary connectors satisfy

    z1=1-ell1*t+O(t^2),  z2=1-ell2*t+O(t^2),
    ell1,ell2>=0.                                     (2)

Every connector remains strictly positive below one at every positive t. The coefficient zero is a permitted limiting statement, never a realizing zero-duration edge. Write

    d1=ell1+A2/2,     d2=ell2+A3/2,
    g1=d1+d2,        g2=d2,       g3=0,
    L=sum_i gamma_Ai g_i
      =gamma_A1 d1-gamma_A3 d2.                      (3)

This L is fixed by ACTUAL clock positions, including intrinsic cell q_i=1-A_i*t/2. It is not a free formal shear. The exact corrected atom law of the uniform packet gives weights omega_i=gamma_Ai*t^3+eta_i*t^4+O(t^5), with sum gamma=sum eta=0 and sum omega=-(107777/8)t^5+O(t^6). Its effective positions before trailing padding are

    Xhat1=1+g1*t+O(t^2),
    Xhat2=1+g2*t+O(t^2), Xhat3=1.

Thus the body's exact normalized cap-four coordinates have

    U_body=5 L*t^4+O(t^5),
    W_body=6 L*t^4+O(t^5).                           (4)

Here U=C/pair^6 and W=(C+H)/pair^6. The order-three coefficient vanishes because sum gamma=0; the common order-four weight sum also vanishes by the SAME source diagonal identities. This is why replacing the effective positions by the ordinary-only ones would miss the A2/2,A3/2 terms in (3).

## 2. The FOURTH full-forest operator is determined, without a count-only substitution

Let Q,R and R_X=E(X)R E(1/X) be the COMPLETE ten-shape operators of the [accepted full-five source jet](../2026-10-08-cloud-g4-full-five-jets-0420z/PRIMARY-REVIEW-RECEIPT.md). The third primitive R has only diagonal, pair-merger and rooted triple-merger entries, the last of which uses TWO actual binary mergers. Put R'_X=dR_X/dX, a hand derivative of the displayed finite transport matrices. It is an auxiliary signed derivative, not an admitted generator.

For one bare cell, every completed five-tree requires all five current roots to choose the same arm. Its probability vector is exactly

    (A5(x)+A5(y))/32 * (1/6,1/3,1/2).

The ordinary small-duration complete-to-one probability satisfies A5(exp(-tau))=(15/2)tau^4+O(tau^5), because the product of actual root-count exit rates is 10*6*3*1 and four ordered waiting integrations divide by 4!. The actual arms have tau_x=A*t+O(t^(3/2)), tau_y=A*t+O(t^(3/2)); arm symmetry and h^2=w*t^3 make their summed coefficient analytic in t. The bare completed fifth FOURTH coefficient is therefore (15*A^4/32)*(1/6,1/3,1/2), exactly that of E(q), q=1-A*t/2. Their fourth completed-tree DIFFERENCE is zero.

In a three-cell body with ordinary connectors (2), the fourth difference from its matched ordinary E(pair) comprises one bare fourth insertion or one third R insertion adjacent to an ordinary first-order Q. A third R insertion changes root count by at most two, and one Q insertion adds at most one binary merger. Neither can complete FIVE roots, which need four mergers. Products of two third insertions start at order six. Thus every completed-five-tree FOURTH difference of the body is zero. Algebraic ordinary normalization of its pair survival does not create a fourth completed-tree coefficient: its first-order prefix Q with a third R again performs at most three mergers (and the summed body third operator is zero).

The normalized body's diagonals through five are EXACTLY one, so all fourth diagonal differences are zero. Its lower full four-root coefficient is determined by (4), including C=5L,H=L; lower arities two/three vanish. The complete deletion reduction says that a five-root signed row with specified lower full row and fifth diagonal is uniquely fixed once its THREE completed-tree entries are fixed. This uniqueness applies to signed Taylor coefficients by linearity; no new stochastic source is assumed.

The operator L*R'_1 has the same data: its diagonals have zero derivative; its cap-four C,D coefficients are 5L,6L since C(R_X)=X^5,D(R_X)=X^6; and f7'(1)=f8'(1)=f9'(1)=0 by the preserved FULL-shape polynomials. Hence it is the body's UNIQUE full fourth operator, including labelled histories and graft action:

    N_body=I+L*t^4 R'_1+O(t^5).                     (5)

This argument retains all ten shape classes and actual rooted triple histories. A partition or root-count projection would not supply its uniqueness premise.

For a fixed trailing ordinary survival u in (d,1), fixed pair target d in (0,1), and positive leading calibration

    zeta=d/[product_A q_A*z1*z2*u],
    K_d=E(zeta)B1 E(z1)B2 E(z2)B3 E(u),

put x=1/u. Algebraically N_d=E(d)^-1 K_d=E(x)N_body E(1/x). The chain rule for R_X gives E(x)R'_1E(1/x)=x R'_x. Therefore

    N_d=I+x L*t^4 R'_x+O(t^5).                       (6)

All realizing factors are strictly positive for sufficiently small positive t: zeta tends to d/u<1, and cell arms/connector durations are positive. Equations (5),(6) determine the first collapsed full-shape correction in this O(t)-clock regime. They do not determine its next, fifth coefficient.

## 3. Distinct-anchor comparable-scale matching forces both clock moments zero

Suppose t_R=k*t+O(t^2), k>0, each block has (2), and its trailing survival has a fixed limit u_P,u_R within the genuine fixed-pair ranges. Let x_P=1/u_P,x_R=1/u_R. The whole-product anchors are z_P=x_P/b,z_R=x_R. Assume they are distinct; strict choices u_P in (a,1),u_R in (b,1) below ensure z_P>1/b>z_R.

Equations (5),(6) and the exact normalization across the SAME fixed b give the whole fourth coefficient

    z_P L_P R'_(z_P)+k^4 z_R L_R R'_(z_R).           (7)

Complete exact cap-four matching forces

    L_P z_P^5+k^4 L_R z_R^5=0,
    L_P z_P^6+k^4 L_R z_R^6=0.

The two-anchor determinant is nonzero, so L_P=L_R=0. The same conclusion applies with only a positive limiting scale ratio and O(t^2) connector expansions, by taking the coefficient limit; no analytic pad path is needed to force these L values. Consequently the FULL fourth coefficient then vanishes, not merely its cap-four projection. This is a precise compatibility gate, rather than a fourth-order full-five obstruction. Coincident anchors at the seam and unequal scales remain separate from this two-anchor assertion.

For positive d1,d2 in (3), L=0 is possible only when the first and third gamma signs agree. Thus these three-cell words must have the positive label10 in the MIDDLE, one of orders (1,10,6) or (6,10,1). Both can obey strict original clock admission. In fact choose

    order P=(1,10,6):
        ell_P2=1,  ell_P1=4s/p-5,
    order R=(6,10,1):
        ell_R1=1,  ell_R2=6s/p-1/2.                  (8)

Since s>50 and p<4, all four ell values are strictly positive. For P, d2=4,d1=4s/p and L=-p*d1+s*d2=0. For R, d1=6,d2=6s/p and L=-s*d1+p*d2=0. These are legitimate finite coefficients of small POSITIVE durations, not physically inverted cell clocks. A fixed exterior pad margin admits their possibly large finite values by taking t sufficiently small.

## 4. Actual second-order connector freedoms make the two cap-four equations EXACT

Fix any a,b in (0,1), u_P in (a,1), u_R in (b,1), and any k>0. Use the physical slopes (8), scale t_P=t,t_R=k*t, the SAME diagonal functions w(t_P),w(t_R), and connectors

    z_d1=exp[-ell_d1*t_d-v_d*t_d^2],
    z_d2=exp[-ell_d2*t_d].                            (9)

The real variables v_P,v_R may have either sign, but the actual durations are positive for all sufficiently small positive t because ell_d1>0 and the v values below stay finite. Calibrate each leading pad by the exact formula in Section 2. The strict limit margins d/u_d<1 ensure finite positive calibration at every sufficiently small positive t. The ordinary population coefficient/duration is exactly -log(zeta); neither a negative source edge nor a formal positive matrix is substituted.

By (5)-(8) the source kernels' normalized perturbations start at order five. The original half-coin finite route/graft coordinates are even in arm difference, w(t) is analytic and (9) is analytic; hence all kernel coordinates are analytic in (t,v_P,v_R). Define their original normalized C,D coordinates U_P,W_P,U_R,W_R. The exact cap-four inverse equations, divided by t^5,

    G1=(U_P+b^5 U_R)/t^5,
    G2=(W_P+b^6 W_R)/t^5,                            (10)

extend analytically to t=0, for every finite v_P,v_R.

Changing v_d changes only the first connector's second-order placement at this order. In the exact atom law it adds gamma_first*v_d*x_d times R'_x_d to the full normalized fifth operator; alternatively this follows by differentiating the third insertion transport, whose position shift is v_d*x_d*t_d^2. Terms of order four or higher change only at order six or higher under this second-order connector shift. Thus the two columns of the t=0 Jacobian of (10) are exactly

    column P=(5 gamma_Pfirst x_P^5,
              6 gamma_Pfirst x_P^6)^T,
    column R=k^5(5 b^5 gamma_Rfirst x_R^5,
                 6 b^6 gamma_Rfirst x_R^6)^T.        (11)

Here gamma_Pfirst=-p, gamma_Rfirst=-s. The hand determinant is

    30 k^5 gamma_Pfirst gamma_Rfirst b^5 x_P^5 x_R^5
                                        *(b*x_R-x_P), (12)

strictly negative because x_P>1 and b*x_R<1. At t=0 the two equations are affine in v_P,v_R; no second powers of v enter until higher order. Write h=(G1(0,0,0),G2(0,0,0)), an exactly defined finite source coefficient vector, and J for (11). Its unique real zero is

    (v_P^0,v_R^0)^T=-J^-1 h.                         (13)

This definition uses the actual original route/graft coefficient, not freely assigned fifth forest data. Its coordinates need not be numerically evaluated to prove they are finite real numbers. The analytic implicit-function theorem at (0,v_P^0,v_R^0) gives bounded analytic v_P(t),v_R(t) solving BOTH exact source equations (10) for every sufficiently small positive t. Equations (8),(9) then keep all connector durations strictly positive; actual arm and calibrated exterior-pad inequalities also persist.

We have therefore proved a genuine analytic family of TWO actual positive words at the SAME fixed a,b such that

    K_P(t)K_R(t)=E(ab) through COMPLETE cap FOUR,
    b_n(K_P)=a^lambda_n, b_n(K_R)=b^lambda_n, n<=5,
    ||three completed-five residuals||=O(t^5).        (14)

The full inverse notation only describes their cap-four relation. Each factor is realized by the original positive generator word; their internal connector durations shrink linearly, and their distinct exterior anchors stay strictly within the fixed budget. This supplies an actual cap-four boundary branch and shows why the strict-interior nonzero order-three obstruction cannot be extended to this path. It does NOT supply a full cap-five branch.

## 5. The precise remaining THREE fifth-coordinate equations

For a factor with (8),(9), define the FULL source operator

    V_d=[t_d^5](E(d)^-1 K_d(t_d,0)-I).               (15)

The bracket is the analytic coefficient of the finite ORIGINAL half-coin route/graft product with its exact w(t_d), positive clocks and calibrated leading pad. No source expansion program has evaluated it. The second-order connector dependence is exactly

    N_d=I+t_d^5[V_d+v_d gamma_dfirst x_d R'_x_d]
                                                     +O(t_d^6). (16)

At the branch from (13), only v_P^0,v_R^0 enter its fifth coefficient. In the whole-unit normalization set z_P=x_P/b,z_R=x_R. Complete lower matching gives the EXACT residual functions from the accepted finite forest formula. Their leading bound and explicit unresolved coefficient are

    r=(ab)^10 t^5 F5+O(t^6),
    (F5)_j=[e0(E(b)^-1 V_P E(b)+k^5 V_R)]_j
         +v_P^0 gamma_Pfirst z_P f'_j(z_P)
         +k^5 v_R^0 gamma_Rfirst z_R f'_j(z_R),
                              j=7,8,9.              (17)

All f_j are the three preserved full-shape polynomials, not a count-only moment. The value F5=0 has NOT been proved or disproved. Individual first coefficients may vanish; no joint nonzero order-five claim follows merely from (14). A full cap-five return would require all three exact source residual functions to vanish, including later orders, under strict parameters. Evaluating V_P,V_R in (15), then the three linked coefficients in (17) after the uniquely fixed corrections (13), is the next genuine original-source step. The cap-four source corrections v_P,v_R have already been spent; they cannot be declared independent free five-tree corrections.

The slope choices (8) can also be varied along their positive L=0 lines; exterior anchors and k remain source parameters. No claim that those remaining parameters have rank three for F5, admit a zero, or solve every exact later coefficient is made. The more degenerate coincident-anchor or unequal-scale cases are separate. Even a full cap-five product return would still need binding the left factor to the GIVEN conjugator of the SAME middle source, then all caps, legal prefix completeness and positive rival inequivalence for the original endpoint.

## 6. Exact scope, observation and attribution

The result is source-only hand mathematics for this two-block 1:6:10 half-coin family. Original full five-token histories, rooted shapes and subtree-preserving current-root grafting are retained. Their forest coordinates are the inherited internal representation recovered by original private topology tomography, not new hidden observations. Parameters at all arities are the same actual source parameters. Inverses and derivative operators are algebraic proof devices; every constructed population has strictly positive finite duration at every t>0 sufficiently small.

No prescribed P=E(a)C_given or R=C_given^-1 E(b) membership, full five-response equality, arbitrary architecture, all-copy extension, unknown bare/menu reduction, effective stopping or general G4 closure is proved. Original ONE-fixed-target/full-legal-prefix/unknown-size G4 remains OPEN. No Lean declaration has been checked or historical novelty asserted.

Attribution: original positive word grammar, private routing, full forests, quotient and tomography retain their contributors. Dot supplied original source polynomials; earlier Cloud source/diagonal/full-five proofs and independent receipts are linked. The collapsed fourth-operator identification and actual positive second-order cap-four IFT construction are this packet's hand contribution. Classical finite source expansion, linear deletion uniqueness and analytic IFT are used; inherited controls were not rerun.
