# A uniform five-root response bound and the necessary dominant-block collapse

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 04:41 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No coefficient harness, deterministic symbolic exploration, mathematical source execution, parameter scan, numerical solver, compiler, Actions or API ran. Source/byte/link checks are preservation metadata only.

The [preceding full-five jet](../2026-10-08-cloud-g4-full-five-jets-0420z/FULL-FIVE-SOURCE-JETS-AND-TWO-BLOCK-OBSTRUCTION.md) excludes fixed strict limiting placements and comparable scales in two actual 1:6:10 three-cell words. Pointwise nonzero jets do not exclude paths approaching placement collisions or unequal scales. Here a polynomial with repeated positive roots gives a UNIFORM response bound without dividing by any placement gap. Every hypothetical exact cap-five return sequence must collapse the ordinary internal connectors of each dominant-scale block. The fully collapsed boundary is not excluded: separate higher-order terms of the two actual sources remain in its exact equations.

## 1. The unchanged actual-source family and the quantified statement

Fix a,b in (0,1) BEFORE choosing any sequence. Each factor is one of the genuine positive words of the [accepted diagonal family](../2026-10-08-cloud-g4-general-ratios-0318z/GENERAL-RATIO-DIAGONAL-FEASIBILITY-AND-RESPONSE-GAP.md), with an arbitrary permutation sigma of cell labels 1,6,10:

    K_d=E(zeta) B_sigma1(t) E(z1) B_sigma2(t)
                          E(z2) B_sigma3(t) E(u),
    q_A=1-A t/2,
    x_A=1-A t-sqrt(w_A(t))t^(3/2),
    y_A=1-A t+sqrt(w_A(t))t^(3/2),
    zeta=d/[product_A q_A *z1*z2*u],       d=a or b.    (1)

The SAME positive analytic w(t) solves the exact three source diagonal equations D3=D4=D5=0. Its label-attached value is (393/50,327281/2400,9377/160). Every arm, connector and pad is strictly in (0,1); in particular product(q_A) z1 z2 u>d. Thus -log(zeta), -log(z1), -log(z2), -log(u) and both arm durations are finite and positive at every admitted point. No zero-duration edge is realized; identity is used only as a limit in a compactness argument. Every factor has the fixed ordinary diagonals d^lambda_n through n=5.

Allow t_P,t_R>0 and all ordinary placements to vary arbitrarily, including nonanalytic paths. Let

    T=max(t_P,t_R),    lambda_P=(t_P/T)^3,
    lambda_R=(t_R/T)^3.                               (2)

At least one lambda equals 1. There is no lower bound on the other. Assume only that the ACTUAL product K_P*K_R agrees with E(ab) through COMPLETE cap four. Let r=(r7,r8,r9) be its three original completed-five-tree orbit residuals, as in the [full forest reduction](../2026-10-08-cloud-g4-two-factors-0356z/CAP5-FULL-FOREST-RESIDUAL-COORDINATES.md). Each fifth diagonal already matches. Consequently r=0 is equivalent to complete cap-five product equality, retaining every labelled genealogy history and graft action.

For each factor set the ORDINARY-only downstream positions

    X1=1/(z1*z2*u), X2=1/(z2*u), X3=1/u.

Use whole-product positions Z_Pi=X_Pi/b and Z_Ri=X_Ri. Strict positive calibration gives

    1/b<Z_P3<Z_P2<Z_P1<1/(ab),
    1<Z_R3<Z_R2<Z_R1<1/b.                            (3)

These inequalities hold at EVERY positive source point, even when their gaps tend to zero. Attach the original leading cell coefficients to their labels:

    gamma_1=-p=-577/150,
    gamma_6=-s=-240881/4800,
    gamma_10=q=51869/960=p+s.                         (4)

The signed six-cell measure is

    mu=sum_i lambda_P gamma_sigmaP_i delta_(Z_Pi)
          +sum_i lambda_R gamma_sigmaR_i delta_(Z_Ri),
    M_k=integral x^k dmu,       M0=0.                 (5)

It is a bookkeeping object forced by the ACTUAL third source jet, not an admitted signed source process. Put B=1/(ab), and let v_P,v_R be the positions of the positive label-10 cells. Define

    c_*=(v_P^2+4 v_P v_R+v_R^2)/(2(v_P+v_R)),
    D=sum_(negative cells i) |weight_i| Z_i^5(Z_i+c_*)
                          *(Z_i-v_P)^2*(Z_i-v_R)^2.  (6)

All terms of D are nonnegative. There are constants C_1,C_2,T0>0, depending only on the FIXED a,b and this fixed analytic source family, uniformly over all strict admissible placements, both positive scales and all 36 order pairs, such that for T<T0

    D <= C_1 (||r||_infinity/T^3+T),                  (7)
    ||r||_infinity >= C_1^-1 T^3 D - T^4.             (8)

Equation (8) is just (7) rearranged with the same constant; it is a lower bound and may be negative. Enlarging a constant is harmless. Let delta be the minimum separation between the six distinct positions in (3). Since the total negative weight is q(lambda_P+lambda_R)>=q, (6),(7) also imply

    delta^4 <= C_2 (||r||_infinity/T^3+T).             (9)

In particular EXACT full-five returns would require D=O(T) and delta=O(T^(1/4)). More substantively, along EVERY sequence of exact full-five returns with T->0, the connectors z1,z2 of any block with liminf lambda>0 must tend to 1. For comparable scales both blocks must collapse their internal ordinary placements. If t_R/t_P->0, this conclusion is proved for P; it makes no collapse assertion for R. The reversed statement applies when P is smaller.

The theorem is a NECESSARY escape condition, not an actual return construction or a uniform impossibility at the collapsed boundary. Sections 5-6 retain the exact higher-source equations needed there.

## 2. Why the source expansion is uniform up to ordinary placement collisions

Calibration (1) bounds each ordinary survival of K_a below by a, and each of K_b below by b: the other factors in its calibration product are at most one. The same is true of the leading calibrated pad. For sufficiently small scales, all cell arms and q_A are bounded away from zero, and the preserved analytic w(t) is bounded and positive. We may therefore close the ordinary parameter ranges to [a,1] and [b,1] when estimating finite matrices. They are compact; their boundary matrices are used only to bound actual positive sources.

Through cap five, the original current-root route/graft formula is a finite polynomial in arm survivals and ordinary E(z) has finite rational-polynomial coordinates. Half-coin symmetry makes the source even in the arm difference, hence analytic in t and w(t). The derived complete forest operator R satisfies uniformly

    B_A(t)=E(q_A)+gamma_A t^3 R+O(t^4).               (10)

This is the FULL-shape operator from the preceding note, including rooted triple histories; it is not merely a merger-count diagonal. Ordinary normalizations remain bounded on these compact ranges. Replacing an insertion's own q_A or its downstream cell q factors by 1 changes its third term by O(t^4), uniformly, because each q_A=1+O(t). Therefore the ordinary-only positions in (3) are a legitimate uniform THIRD-order representation even when connectors collapse faster than t. They are not claimed to be the exact positions of all higher corrections.

For a single block let N_d=E(d)^-1*K_d in the finite complete forest algebra, an algebraic normalization. There is an EXACT analytic remainder operator A_d, bounded uniformly on the above closed placement ranges, such that

    N_d-I=t_d^3 R_d+t_d^4 A_d,
    R_d=sum_i gamma_sigma_i R_(X_i),
    R_X=E(X)R E(X^-1).                               (11)

Division by t_d^4 in this definition has a removable singularity by (10) and the finite product expansion. E(X), X>1, is auxiliary algebraic notation and is never a negative-duration realizing source edge. No source premise assigns A_d freely: it is the remainder of the ORIGINAL word (1) at its SAME parameters.

The exact whole-product normalization is

    N=E(ab)^-1 K_P K_R=E(b)^-1 N_a E(b) N_b.

Writing tilde for conjugation by E(b)^-1 on the left and E(b) on the right gives

    N-I=t_P^3 tilde(R_P)+t_R^3 R_R
            +t_P^4 tilde(A_P)+t_R^4 A_R
            +t_P^3 t_R^3 [tilde(R_P)+t_P tilde(A_P)]
                                      [R_R+t_R A_R]. (12)

In particular tilde(R_X)=R_(X/b), giving (3),(5). The two fourth-order remainder operators and the cross product in (12) are retained separately. Their sum is uniformly O(t_P^4+t_R^4+t_P^3 t_R^3)=O(T^4). Nothing here replaces a smaller factor's correction by the larger factor's correction, assumes a positive limiting scale ratio, or extends a merely pointwise O(t^4) estimate to a moving placement without control.

## 3. Exact lower matching controls all five relevant moments

The complete original four-root C,D=C+H product, after normalization by each factor's fixed pair diagonal, gives the EXACT lower equality conditions

    U_P+b^5 U_R=0,       W_P+b^6 W_R=0,
    U_d=C(K_d)/d^6,      W_d=D(K_d)/d^6.              (13)

From (10)-(12), their uniform leading expansions imply

    |M5|+|M6| <= C T.                                (14)

For example U_P+b^5 U_R=b^5 T^3 M5+O(t_P^4+t_R^4); the analogous identity uses b^6 M6. The fixed b is not a scale-dependent fitting parameter.

Complete lower matching means N-I is zero on every input row with at most four current roots, including prebuilt histories. Thus the fresh-five completed-tree residual satisfies EXACTLY

    r_j=(ab)^10 [e0(N-I)]_j,          j=7,8,9.        (15)

All other prefix forest terms have fewer roots and cancel; this is why full lower equality, rather than selected coordinates, matters. Apply the preserved explicit full-shape functions f_j(X)=[e0 R_X]_j to (12). Since M0=0, one obtains uniformly

    r/[(ab)^10 T^3]
        =L (M7,M9,M10)^T+J (M5,M6)^T+O(T),          (16)
    L=[15/28  -5/2   15/8;
       -10/7   5/2   -5/4;
        5/14    0    -5/8],
    J=[ 3/4  -5/8;
        3/2  -5/4;
       -3/2  15/8],       det L=375/448 !=0.

Together (14),(16) give a constant C_0 with

    max_(k in {5,6,7,9,10}) |M_k|
                       <= C_0 (||r||_infinity/T^3+T). (17)

This estimate holds whether or not r vanishes. It uses the three separate full completed-tree shapes; no count-only or partition-only quotient can replace them. Exact source diagonals through five and deletion make r=0 a complete cap-five statement for these actual words, not just a three-event diagnostic agreement.

## 4. A repeated-root separator has no singular gap constant

Consider the polynomial

    P(x)=x^5 (x-v_P)^2 (x-v_R)^2 (x+c_*).             (18)

The fourth-degree factor expands as

    x^4-2(v_P+v_R)x^3
       +(v_P^2+4v_Pv_R+v_R^2)x^2
       -2v_Pv_R(v_P+v_R)x+v_P^2v_R^2.

Multiplication by x+c_* makes its x^3 coefficient zero by (6). Hence P belongs EXACTLY to span{x^5,x^6,x^7,x^9,x^10}; its x^8 coefficient vanishes. It is nonnegative for x>0 and zero at BOTH positive-weight positions. Therefore

    integral P dmu = -D.                             (19)

The coefficient l1 norm of P is at most

    K_B=(1+B)^4(1+3B).                               (20)

Indeed each positive root is at most B; c_*=s2/s1 for the four roots (v_P,v_P,v_R,v_R), and 2s2<=3B s1, so c_*<=3B/2. The slightly larger 3B in (20) is a convenient safe bound. No root-gap division appears. Equations (17),(19),(20) give (7). If delta is the minimum of all pairwise support separations, each negative cell is at least delta from EACH positive cell; x^5(x+c_*)>=1 on [1,B]. Thus

    D >= q(lambda_P+lambda_R) delta^4 >= q delta^4,

proving (9). A further useful localized consequence at an exact return is

    sum_(negative i) |weight_i|
         distance(Z_i,{v_P,v_R})^4 <= D <= C_1 T.     (21)

Any negative atom with weight bounded below must approach one of the two positive positions at rate O(T^(1/4)). This is an estimate across collisions, not a claim that an exact return exists at that rate. In particular the source's intrinsic O(T) clock separations lie well inside the region not excluded by (9).

For fixed distinct supports D>0, recovering the previous strict-interior obstruction with a quantitative margin. On collapsing supports it may tend to zero, and the retained O(T^4) terms can dominate the leading response. The bound explicitly exhibits that limitation rather than discarding those terms.

## 5. Every active block must collapse, including on unequal-scale sequences

Suppose exact full-five returns exist along T_n->0. Pass to ANY convergent subsequence of the positions in the compact intervals (3) and lambda_P,lambda_R in [0,1]. At least one limiting lambda is 1. From (17) every limiting moment at powers 5,6,7,9,10 is zero. From (7), D tends to zero.

Because every term of (6) is nonnegative, every limiting negative atom with nonzero weight lies at one of the two limiting positive positions v_P*,v_R*. Thus the limiting signed measure is supported at these at most two points. If they are distinct, its coefficients vanish separately: the two equations M5=M6=0 have determinant (v_P*)^5(v_R*)^5(v_R*-v_P*) !=0. If they coincide, M5=0 alone gives zero net coefficient. The LIMIT MEASURE IS ZERO, not merely one of its moment projections.

The two CLOSED block support intervals meet only at chi=1/b. Away from chi a zero total measure means that each block measure is zero separately. Each block also has total mass lambda(gamma_1+gamma_6+gamma_10)=0; consequently its remaining possible mass at chi must be zero too. This prevents cancellation across the seam from hiding a nonzero block measure.

For a block with positive limiting lambda, divide by that lambda. Its measure has precisely one positive coefficient q=p+s and two negative coefficients -p,-s, with p,s>0. Such a three-atom measure is zero only when ALL THREE positions coincide: if the positive position coincided with just one negative, a nonzero remaining coefficient would persist at that point and at the other negative point. Thus every active block's three ordinary-only positions must coalesce. Since X1/X2=1/z1 and X2/X3=1/z2, its two genuine internal connector survivals must tend to 1.

If liminf lambda for a block is positive, a contradictory noncollapsing subsequence would have a convergent subsequence of the preceding kind, so the collapse conclusion holds on the whole sequence. Comparable positive scales therefore force BOTH blocks to collapse their internal ordinary connectors. If only one scale is dominant, the conclusion applies to that block; the inactive block may still supply a smaller higher-order correction. The trailing/leading ordinary pads need not vanish: their common placement anchor can remain inside its fixed-a or fixed-b budget. Orders may vary among finitely many permutations; subsequence selection and constants uniform over that finite set handle them without a new generic assumption.

This is stronger than excluding only comparable scales at fixed strict placements, but it is still a necessary-boundary result. It does not conclude that collapsed sources fail to return or that a smaller source can actually repair their residual.

## 6. The exact cap-four atoms expose the higher-order boundary dependency

The ordinary-only positions used for (10)-(21) must NOT be treated as an exact signed measure for the full nonlinear source. Here is the exact corrected cap-four formula, derived directly from the original [source quotient multiplication, equation (2)](../2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md).

For a chronological block write q_i=b2(B_i), r_i=b4(B_i), c_i=C(B_i), and set

    kappa_i=r_i/q_i^6,       xi_i=c_i/q_i^6,
    omega_1=xi_1,
    omega_2=kappa_1 xi_2,
    omega_3=kappa_1 kappa_2 xi_3,
    Xhat_1=1/(z1*q2*z2*q3*u),
    Xhat_2=1/(z2*q3*u),       Xhat_3=1/u.             (22)

Positive leading calibration cancels upon division by d^6. The quotient product and trailing padding give EXACTLY

    U_d=sum_i omega_i Xhat_i^5,
    W_d=sum_i omega_i Xhat_i^6.                       (23)

For instance the first C term is z1 z2 q2 q3 u c1; dividing by (q1 z1 q2 z2 q3 u)^6 yields xi_1 Xhat_1^5. The second and third terms give the successive kappa factors. D is unchanged by trailing E(u), giving sixth powers. This derivation uses actual current-root routing and subtree-preserving grafting, not a formal shear assumption.

The source diagonals and the previously accepted fifth-order cell identity imply, for EVERY chronological order,

    sum_i omega_i=-(107777/8)t_d^5+O(t_d^6).          (24)

To see the order scope, xi_i=-(2/3)D3_i+(2/3)D4_i-(1/2)D5_i-(A_i^5/8)t_d^5+O(t_d^6). The SAME source body has summed D3=D4=D5=0. Also kappa_i=1+O(t_d^3), xi_i=O(t_d^3), so the prefix-kappa changes to the sum begin at order six. This is [the preserved all-order identity](../2026-10-08-cloud-g4-six-orders-0330z/ALL-SIX-ORDER-FULL-RESPONSE-OBSTRUCTION.md), with the same w(t), not an independent adjustable mass.

For the two factors use exact whole-product supports Xhat_P/b and Xhat_R, and exact weights omega_P,omega_R. Then (13) is precisely the pair of EXACT weighted moment equations at powers 5 and 6. Their total mass, however, is

    sum omega_P+sum omega_R
       =-(107777/8)(t_P^5+t_R^5)+O(t_P^6+t_R^6),      (25)

strictly negative for sufficiently small positive T. It is not the ZERO mass of the THIRD-order measure (5). Furthermore Xhat_1/Xhat_2=1/(z1 q2) and Xhat_2/Xhat_3=1/(z2 q3) retain intrinsic positive O(t_d) separations even if the ordinary connectors approach identity faster. Treating (5) as an exact nonlinear source law would erase precisely these clock and mass terms.

Nor is the FULL five-root matrix exactly a sum of omega_i R_(Xhat_i). Equations (22)-(25) determine cap four, while A_P,A_R and the cross term in (12) retain the additional full-shape source corrections. Once both leading blocks collapse, or one scale becomes smaller, those omitted coefficients can have the same order as the surviving signed-moment contribution. The exact remaining three-equation boundary system is (15),(12), or equivalently

    0=L(M7,M9,M10)^T+J(M5,M6)^T
        +(t_P^4/T^3) a_P+(t_R^4/T^3) a_R
        +(t_P^3 t_R^3/T^3) b_PR,                    (26)

where a_P,a_R are the three completed-tree entries of tilde(A_P),A_R and b_PR those of the bracket product in (12). These are bounded analytic functions of their ORIGINAL source parameters; their values at a collapsed limit have not been computed here. The two corrected equations (23) must also hold. Equation (26) is an exact remainder representation, not a free signed-coefficient realization or an asserted solvable asymptotic ansatz.

No defensible sign for (26) at all collapsed placements follows from (7). The required next estimate is the source-derived first nonzero completed-tree jet of A_P and A_R at the collapsed ordinary placements, with their physical intrinsic q spacings, fixed-pad calibration and possible unequal scales retained jointly. A sufficiently strong sign/separator bound for those corrections could exclude this boundary; an actual analytic branch would have to solve all three equations and the corrected cap-four equations with strict positive parameters. Neither conclusion is supplied by the pointwise third jet or by algebraic positivity.

## 7. Original endpoint and attribution

All statements concern this SAME two-block actual 1:6:10 half-coin source family at fixed a,b. They do not exclude other mean ratios, more cells, other coins or original architectures; they do not realize the GIVEN padded conjugator C_epsilon. Even an exact product return would leave the binding equation E(a)^-1 K_P=C_given from the SAME middle word, higher caps, unknown bare/menu completeness and the original fixed-target/full-prefix unknown-size rival requirement. Original G4 and detectable stopping remain OPEN.

Complete rooted-forest quantities are internal source coordinates reconstructed by the inherited authorized private topology tomography. No hidden forest, route or calendar becomes a new observation; root/current-token/shared-parameter and full-copy-menu premises are retained. Source words are strictly positive and all inverses/limits are algebraic proof devices. No Lean theorem has been compiled and no historical novelty claim is made.

Attribution: original source grammar, routing, full forests, quotient and tomography retain their contributors. Dot supplied original accepted source polynomials. The Cloud 1:6:10 diagonal family, actual cap-four two-factor branch and full-five jet are explicit dependencies. The collision-safe repeated-root estimate, unequal-scale active-block collapse and exact corrected boundary accounting are this packet's hand contribution. Classical finite analytic expansion, polynomial separation and compactness are used without rerunning inherited controls.
