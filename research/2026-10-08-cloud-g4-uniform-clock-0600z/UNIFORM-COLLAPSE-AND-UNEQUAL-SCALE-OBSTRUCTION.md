# Fixed trailing pads: a uniform source obstruction through five roots

Contributor: Codex Cloud G4 / CLOUD-G6-SOL-ULTRA-20261007, 8 October 2026, 06:00 UTC. **SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No mathematical program, coefficient harness, symbolic execution, numerical fit, scan, practical solver, compiler, Actions or API ran. The full source derivation below is saved before any possible execution. Metadata preservation and Git publication are separate.

The [accepted uniform response bound](../2026-10-08-cloud-g4-degenerate-response-0441z/PRIMARY-REVIEW-RECEIPT.md) left collisions of the source placements open. The [new fifth operator](../2026-10-08-cloud-g4-fifth-clock-0535z/ACTUAL-FIFTH-OPERATOR-AND-CONFLUENT-OBSTRUCTION.md), still independently pending, excluded finite linear clocks and comparable scales. This note derives a multivariable source estimate and handles arbitrary nonlinear connector collapse and arbitrary relative shrinking cell scales, with FIXED strictly positive trailing pads. It retains every full rooted-forest coordinate through five. It does not assert a uniform obstruction when exterior pads approach the common boundary, for other source architectures, or for general G4.

## 1. Precise family and proposition

Fix a,b in (0,1), and fix u_P in (a,1), u_R in (b,1). Use the SAME original natural private INDEPENDENT current-root half-coin three-cell family with labels A=1,6,10. In a block at cell scale t>0 its two arm pair-survival values are

    1-A*t +/- sqrt(w_A(t))*t^(3/2),
    q_A=b2(B_A)=1-A*t/2.

The positive analytic w(t) is the [accepted actual diagonal family](../2026-10-08-cloud-g4-general-ratios-0318z/GENERAL-RATIO-DIAGONAL-FEASIBILITY-AND-RESPONSE-GAP.md), solving D3=D4=D5=0 EXACTLY and shared across all arities. Its leading values are (393/50,327281/2400,9377/160). The chronological order of the three cells can be any permutation. Put

    K_d=E(zeta_d) B_1 E(z1_d) B_2 E(z2_d) B_3 E(u_d),
    zeta_d=d/(q_1*q_2*q_3*z1_d*z2_d*u_d), d=a or b.    (1)

Each z1_d,z2_d,zeta_d lies strictly between zero and one. Thus (1) has genuine finite positive ordinary durations, genuine positive arms, and fixed actual pair survival d. The connectors may depend on t in ANY way; no analyticity, fixed linear slope, positive limiting gap, or relative-scale promise is imposed on them. Cell scales t_P,t_R may shrink at ANY relative rate. The finite set of chronological permutations may vary as well.

**Candidate proposition.** For these fixed a,b,u_P,u_R there is epsilon>0 such that, for 0<t_P,t_R<epsilon and every source-admissible pair (1),

    K_a K_b != E(ab) on the complete rooted forest law through five roots. (2)

In particular no such pair can realize BOTH E(a)C and C^-1 E(b) for any same prescribed C through cap five. This necessary product obstruction is stronger than the earlier fixed-linear/comparable-scale result within this fixed-tail family. It is not a claim about arbitrary factor words or the original unknown-size/full-prefix endpoint.

Only finite source matrices through five are used. Their orbit laws retain all rooted tree histories and graft opaque older subtrees as ONE current root, as in the [original admitted grammar](../2026-10-01-g4-admitted-testers-0819z/PROOF.md). The complete ten five-root forest classes and delete-one constraints are the [accepted full basis](../2026-10-08-cloud-g4-two-factors-0356z/CAP5-FULL-FOREST-RESIDUAL-COORDINATES.md). No calendar or hidden forest observation is added to the legal experiment.

## 2. Exact corrected weights and a negative centered second moment

For one chronological block write h_j=-log(zj)>=0 and tau_i=-log(q_i). Let r_i=b4(B_i), c_i=C(B_i), kappa_i=r_i/q_i^6, xi_i=c_i/q_i^6. The [accepted exact cap-four atoms](../2026-10-08-cloud-g4-degenerate-response-0441z/UNIFORM-FIVE-RESPONSE-BOUND-AND-COLLAPSE-GATE.md) are

    omega_1=xi_1, omega_2=kappa_1*xi_2,
    omega_3=kappa_1*kappa_2*xi_3,
    H1=h1+h2+tau_2+tau_3, H2=h2+tau_3, H3=0.       (3)

These include the downstream CELL q factors. Ordinary connectors do not change omega. At any order,

    omega_i=gamma_i*t^3+O(t^4),
    gamma_1=-577/150=-p,
    gamma_6=-240881/4800=-s,
    gamma_10=51869/960=p+s,
    Omega=sum omega_i=-(107777/8)*t^5+O(t^6)<0.       (4)

The uniform constants may be chosen over all six permutations. The negative mass in (4) is an exact-source consequence of the diagonal balance, not an assigned signed residual field.

Let the index + be the unique positive cell (label10), and center on its ACTUAL effective log placement H_+. Define

    A0=exp(H_+), delta_i=H_i-H_+,
    beta1=sum omega_i*delta_i,
    beta2=sum omega_i*delta_i^2,
    D=t+h1+h2.                                     (5)

For sufficiently small t the other two weights are strictly negative and the positive cell has delta_+=0. Intrinsic cell hazards are positive. Thus, uniformly over all orders and all nonnegative h1,h2,

    beta2<0,
    c*t^3*D^2 <= -beta2 <= C*t^3*D^2,
    |beta1| <= C*t^3*D, |Omega| <= C*t^5.            (6)

Here (6) is needed locally when D is small. To prove its lower bound, the total placement span H1-H3=h1+h2+tau_2+tau_3 is comparable to D, since each label is one of1,6,10 and tau_i=(A_i/2)t+O(t^2). If the positive cell is at an end, one negative cell is the opposite endpoint. If it is in the middle, the two negative distances have sum equal to the span and sum of squares at least half its square. The two negative magnitudes are uniformly at least c*t^3. No L=0 condition is needed for this sign or bound.

## 3. A full-source uniform expansion at an arbitrary collapse rate

Use the full accepted operators R_X=E(X)R E(1/X) and their THREE completed-five functions f_j(X). Let T_X be the full auxiliary operator from the [fifth source note](../2026-10-08-cloud-g4-fifth-clock-0535z/ACTUAL-FIFTH-OPERATOR-AND-CONFLUENT-OBSTRUCTION.md), with zero diagonals, C(T)=D(T)=1, and zero fresh completed-five coordinates at X=1. It is a signed proof operator, not a new legal source generator. Write

    mathcalD R_X=X*dR_X/dX,
    mathcalD^2 R_X=X*d/dX(X*dR_X/dX).

For the unit-normalized body N_body=E(1/(q1*q2*q3*z1*z2)) times the three-cell/connector word, the following estimate is the new source step:

    N_body-I = Omega*T_A0 + beta1*mathcalD R_A0
                 +(beta2/2)*mathcalD^2 R_A0 + Err,
    ||Err|| <= C*t^3*(t+h1+h2)^3.                  (7)

The norm is on the complete finite source/graft matrices through five, not on a merger-count quotient. The estimate holds on a fixed sufficiently small neighborhood of (t,h1,h2)=(0,0,0), uniformly in their relative sizes. In particular the error is o(t^3*D^2) along every collapsed-connector path. It does NOT follow merely from a nonzero jet along fixed slopes.

Here is the multivariable proof of (7). Original finite half-coin routing is symmetric in the arm difference. Its powers enter as w(t)*t^3, so the full B_i, ordinary matrices and normalized body are analytic in (t,h1,h2). Every bare difference B_i-E(q_i) is divisible by t^3. Hence the body difference, and the difference of both sides of (7), are analytically divisible by t^3.

It remains to identify all total degrees through five. Along h_j=ell_j*t+v_j*t^2 with arbitrary finite nonnegative ell_j, put g1=ell1+ell2+(A2+A3)/2,g2=ell2+A3/2,g3=0. The original full routing calculation in Sections2-4 of the fifth note gives, WITHOUT imposing L=0,

    N_body=I+t^4*L*R'_1
              +t^5*(m0*T+m1*R'_1+(m2/2)*R''_1)+O(t^6),
    L=sum gamma_i*g_i,
    m0=-107777/8, m2=sum gamma_i*g_i^2,
    m1=sum eta_i*g_i+sum gamma_i*j_i,                (8)

where omega_i=gamma_i*t^3+eta_i*t^4+zeta_i*t^5+... and exp(H_i)=1+g_i*t+j_i*t^2+... . The identities sum gamma=sum eta=0,sum zeta=m0 are exact-source identities. The earlier note stated its final theorem on L=0; the following source derivation explains why (8) needs no such restriction.

Its actual bare fourth THREE-merger layer is (A_i*gamma_i/2)*QR. Its bare completed-five fifth vector is -(45/8)*A_i^2*gamma_i*(1/6,1/3,1/2). A normalized insertion has the EXACT direction

    exp[-(tau_i+H_i)Q]*(B_i-E(q_i))*exp[H_i Q].

The intrinsic A_i^2 terms cancel using [e0*Q^2*R]completed=-45*(1/6,1/3,1/2). The remaining completed fifth vector is (m2/2)*f''(1), regardless of L. The fourth vector is L*R'_1, whose fresh completed-five entries vanish because f'_j(1)=0. The corrected cap-four atoms give fourth coefficients5L,6L and fifth coefficients m0+5m1+10m2,m0+6m1+15m2. Exact ordinary diagonals, these complete lower coefficients and the three completed-five coordinates uniquely pin the whole fifth operator by delete-one/graft consistency. This gives (8) on every finite-slope ray, not just its L=0 subfamily. This is the pending fifth note's source calculation reused at its unrestricted intermediate scope.

To check the centered logarithmic expression, write g_+=g at the positive cell. Equations (3)-(5) yield

    Omega=m0*t^5+O(t^6),
    beta1=L*t^4+(m1-m2/2)*t^5+O(t^6),
    beta2=(m2-2*g_+*L)*t^5+O(t^6),
    mathcalD R_A0=R'_1+g_+*t*(R'_1+R''_1)+O(t^2),
    mathcalD^2 R_A0=R'_1+R''_1+O(t).               (9)

The g_+*L terms cancel in (7), leaving exactly (8). In beta1 the term -H_+*Omega begins only at sixth order. Taking v_j=0 already identifies every homogeneous Taylor term through degree five: after division by t^3 each such term is a polynomial in ell1,ell2 on an open positive quadrant. Its vanishing on every finite ray forces each polynomial coefficient to vanish. Analytic multivariable Taylor remainder on a fixed neighborhood is therefore bounded by C*t^3*(t+h1+h2)^3, proving (7). Arbitrarily diverging h_j/t and nonanalytic paths now fall under a single uniform estimate. No pointwise limit has been used as uniform control.

## 4. Fixed trailing pads separate blocks; keep other blocks atomic

Set N_d=E(d)^-1*K_d. Exact calibration gives N_d=E(1/u_d)*N_body*E(u_d). The full product normalization is

    E(ab)^-1*K_a*K_b = E(b)^-1*N_a*E(b)*N_b.        (10)

Thus the whole positive anchors of collapsed blocks are

    Z_P=exp(H_+,P)/(u_P*b),
    Z_R=exp(H_+,R)/u_R.                            (11)

Every whole placement in block P is at least 1/(u_P*b)>chi=1/b. Every placement in block R is below chi: calibration implies exp(H1,R)/u_R<q1,R/b<1/b. Consequently the two positive anchors, and either block's atoms versus the other positive anchor, have a FIXED separation at least

    delta0=1/(u_P*b)-1/b>0.                        (12)

All placements are in a fixed compact positive interval, for instance [1,1/(ab)]. The fixed strict value u_P<1 is essential in (12). Calibration also bounds h1+h2<log(u_d/d). This compactness permits a subsequence analysis of any hypothetical return sequence.

For a block whose limiting connector sum is positive, keep its genuine third-order atomic operator instead of using a collision Taylor approximation:

    N_d-I=t_d^3*sum gamma_i*R_Xi+O(t_d^4),          (13)

where its ordinary positions before whole-product transport are exp(h1+h2)/u_d,exp(h2)/u_d,1/u_d. Cell q placement corrections are O(t) and are included in the uniform error. Equation (13) is the original finite source expansion, uniformly over calibrated compact connectors. The signed atomic mass is zero, with one positive and two negative cells. Let its positive anchor be its ordinary positive-cell position; apply the P/b transport in (10).

For a collapsed block put S_d=t_d^3*(t_d+h1_d+h2_d)^2. For a block with positive limiting connector sum put S_d=t_d^3. Then the individual source errors are o(S_d). Its operator norm is O(t_d^3*(t_d+h1_d+h2_d)) in the collapsed case and O(t_d^3) in the other case, since Omega=O(t^5) and (6),(7) hold. Cross products in (10) are o(S_P+S_R) at EVERY relative scale. In the two-collapsed case, writing D_d=t_d+h1_d+h2_d,

    t_P^3*D_P*t_R^3*D_R
       <= (t_P*t_R)^(3/2)*(S_P+S_R)/2.             (14)

In a mixed case divide the cross bound by the noncollapsed S; the remaining collapsed factor is O(t^3 D)->0. With neither collapsed, t_P^3*t_R^3=o(t_P^3+t_R^3). Thus factor-specific higher terms and the exact order of the product are controlled even if one cell scale is arbitrarily smaller than the other. No comparable-scale assumption is smuggled into the remainder.

## 5. The three FULL residuals and the hybrid separator

Suppose for contradiction a sequence of exact complete cap-five returns has t_P,t_R->0. Pass to a subsequence with fixed chronological orders and each connector pair convergent. Classify each block as collapsed or noncollapsed as above and put S=S_P+S_R>0.

For a polynomial F define the actual-source coefficient functional

    nu(F)=sum_collapsed[(7/5)*Omega_d*F(Z_d)
                  +beta1_d*mathcalD F(Z_d)
                  +(beta2_d/2)*mathcalD^2 F(Z_d)]
             +sum_noncollapsed t_d^3*sum_i gamma_i*F(X_di),
    N_k=nu(x^k), mathcalD F=x*F',
    mathcalD^2 F=x*F'+x^2*F''.                    (15)

Its atoms, derivatives and T terms are bookkeeping for the SOURCE expansions (7),(13); they are not legal signed source populations or independent adjustable coordinates. Whole-product anchors/atoms in (15) retain the transports in (10).

Since C(R_X)=X^5,D(R_X)=X^6 and C(T_X)=X^5,D(T_X)=X^6, exact cap-four return, with the controlled o(S) source remainder, implies

    N5=(2/5)*sum_collapsed Omega_d*Z_d^5+o(S),
    N6=(2/5)*sum_collapsed Omega_d*Z_d^6+o(S),
    N0=(7/5)*sum_collapsed Omega_d.                (16)

This includes the logarithmic second derivative coefficients25 and36 in the two cap-four equations. They are not the linear-coordinate coefficients20 and30.

The actual T transport has completed entries t_j=(7/5)f_j+h_j, where

    h7=X^6/4-3X^5/10+1/20,
    h8=X^6/2-3X^5/5+1/10,
    h9=-3X^6/4+3X^5/5+3/20.

The accepted f_j contain powers0,5,6,7,9,10. Their low powers cancel these h_j terms exactly under (16). Hence the THREE actual completed-five residuals, after normalization by the fixed (ab)^10, are

    Lmat*(N7,N9,N10)^T+o(S),
    Lmat=[15/28 -5/2 15/8;
           -10/7  5/2 -5/4;
            5/14   0  -5/8], det=375/448.          (17)

Full return therefore forces N7=N9=N10=o(S). This uses the entire ten-class forest basis and its three completed-tree coordinates, not only no-merger diagonals or merger counts.

At the TWO positive block anchors u,v from (11) or (13), choose

    F(x)=x^5*(x-u)^2*(x-v)^2*(x+c),
    c=(u^2+4*u*v+v^2)/(2*(u+v))>0.               (18)

There is no x^8 term. The polynomial belongs to span{x^5,x^6,x^7,x^9,x^10}, has uniformly bounded coefficients on the compact placement interval, and is nonnegative. Its value and first derivative vanish at both anchors. The anchors are separated by delta0. Thus F''(u),F''(v) are uniformly positive. Every collapsed block contributes

    (beta2_d/2)*Z_d^2*F''(Z_d) <= -c*S_d.          (19)

For a noncollapsed block its positive atomic term is zero. Every negative atomic term is nonpositive. At least one negative atom stays a positive distance from its own positive anchor: the block's ordinary placement span has a positive subsequential limit, and the two negative cells surround the positive cell or include the opposite endpoint. The other block's positive anchor is also at least delta0 away. Hence its total atomic contribution is at most -c*t_d^3=-c*S_d. Together,

    nu(F) <= -c*S                                (20)

for a fixed subsequential c>0, without any factor-scale comparability.

Let p0,p1 be the coefficients of x^5,x^6 in (18):

    p0=c*u^2*v^2>0,
    p1=-u*v*(u^2+3*u*v+v^2)<0,
    p0/(-p1)<min(u,v).                           (21)

The last strict inequality is the direct positive-polynomial identity from the fifth note. Equations (16),(17) express the SAME quantity differently:

    nu(F)=(2/5)*sum_collapsed Omega_d*Z_d^5*(p0+p1*Z_d)+o(S)
          >= -o(S).                              (22)

Each main summand is nonnegative, since Omega_d<0 and p0+p1*Z_d<0. If there are no collapsed blocks the sum is zero. Equations (20),(22) contradict each other for sufficiently small t_P,t_R. This handles all four subsequential collapse/noncollapse combinations and proves (2): otherwise a sequence with max(t_P,t_R)->0 would give the contradiction just established.

## 6. Scope and exact remaining dependency

The candidate excludes every nonlinear internal-clock collapse regime, every unequal shrinking cell-scale regime and all chronological orders of these two actual diagonal-calibrated 1:6:10 blocks at fixed a,b AND fixed strict u_P,u_R. The earlier genuine positive cap-four inverse branch is unchanged; it cannot be upgraded to a full five-root return in this fixed-tail family. The source error estimate, exact negative weights, fixed anchor gap and hybrid treatment are all needed. Merely knowing a pointwise fifth coefficient is nonzero would not prove this result.

The estimate is NOT uniform if the trailing pads vary toward the common block boundary. In that case (12) can vanish, the constants in (19),(20) can vanish, and the o(S) remainders need not be smaller than the separator cost. The next unclosed system must retain those factor-specific errors with a separator cost proportional to the squared gap between positive block anchors, and also retain the negative O(t^5) mass. A pointwise strict sign is insufficient to resolve that moving-boundary regime. No actual exact return there has been constructed or ruled out by this packet.

Other arm ratios, other coin/source cells, additional cells, different actual word architectures, higher arities and GIVEN conjugator binding remain separate. The original single-fixed-target/full-legal-prefix/unknown-size/effective-stopping G4 endpoint remains OPEN. Nothing here is a full-prefix rival or an all-rival forcing/stopping theorem.

Review provenance: the diagonal family, full forest jets, deletion basis and prior uniform/fourth-clock packets have canonical scoped HAND acceptances. The fifth T source layer85a0 is independently pending; this proof reuses it while explicitly deriving its unrestricted intermediate form (8). This new uniform theorem is independently pending as well. Existing helper reactivation failed with 'agent thread limit reached'; no new helper source verdict is claimed. Informal declaration targets are not checked Lean declarations. The existing sole-owner same179 input is untouched; this packet is outside that compiler input.
