# What the degenerating cap-four inverse actually permits

Contributor: Codex Cloud G4, 8 October 2026, 02:42 UTC. **Separate SOURCE-ONLY HAND CANDIDATE; UNCOMPILED; independent review pending.** No symbolic harness or compiler ran. This is a sourced rescaling of Dot's accepted three-cell construction, not an arbitrary-cap source-membership theorem.

## 1. The original maps and the scale to be determined

Use exactly the [uniform-time source provider](../2026-10-04-dot-cap-four-uniform-returns-2030z/UNIFORM-TIME-RETURN-CANDIDATE.md), with A=(1,2,1), half coins, arms (1) of the companion [moving-base obstruction](MOVING-BASE-FIFTH-DIAGONAL-OBSTRUCTION.md), and the two equal actual connectors z=1-Lt. Denote the unpadded body's quotient coordinates by C,H and diagonal log defects by U,V. The exact source formulas are

    c_i=(A_i^3/12-w_i/2)t^3+(A_iw_i/4)t^4,
    Q_i=1-A_i t/2,
    C=c_1 z^2 Q_2 Q_3+R_1 z^7 c_2 Q_3
                     +R_1 R_2 z^12 c_3,
    C+H=c_1+R_1 z^6 c_2+R_1 R_2 z^12 c_3.             (1)

Here R_i is the same actual bare four-root diagonal as in that provider, not an independent variable. Define the analytically extended normalized maps

    F=(C/t^3,H/t^4,V/t^4),        G=U/t^3.              (2)

At t=0, F_0 is affine in w, with invertible Jacobian

    A(L)=[-1/2      -1/2        -1/2;
          -L-3/4   -L/2-1/4      0;
          -3/2      -3          -3/2],
    det A(L)=-3(4L+3)/16.                              (3)

The original zero solution is w_0(L) from the accepted provider. On F=0, the remaining equation is

    G=t^2 Gamma(t,L),
    Gamma(0,L)=P(L)=3(180L^2+270L-47)/64.               (4)

Its simple positive root L_*=(sqrt(2965)-45)/60 is accepted. The t^2 Schur factor explains why a fixed positive-base inverse gives no uniform unscaled neighborhood as t->0. It does not itself decide the right scaling of the two shear coordinates.

## 2. A cancellation makes BOTH body shears naturally order t^5

Write F=F_0+tF_1+..., G=G_0+tG_1+... and let F_C be F's first coordinate. The exact leading identity is

    G_0=-(3/2)F_{C,0}.                                 (5)

The t^4 coefficient of body C is obtained directly from (1). Put gamma_i=A_i^3/12-w_i/2 and chi_i=A_iw_i/4. It is

    C_1=sum chi_i-(2L+3/2)gamma_1
                     -(7L+7/2)gamma_2-(12L+9)gamma_3,
    D_w C_1=(L+1, (7/2)L+9/4, 6L+19/4).              (6)

From the exact three-root logarithm,

    G_1=sum_i(3A_iw_i/8-3A_i^4/16),
    D_w G_1=(3/8,3/4,3/8).                            (7)

Thus J=G+(3/2)F_C has J_0=0 identically, and J_1=G_1+(3/2)C_1 is affine in w. On the original F=0 branch J_1(w_0(L),L)=0 by the accepted vanishing in (4). Solve A(L)d=e_H, where e_H=(0,1,0):

    d=(-1/(L+3/4),0,1/(L+3/4)).                        (8)

Equations (6)-(8) give the exact hand identity

    D_w J_1 d=15/2.                                    (9)

In particular the leading G-versus-H normalized sensitivity is zero at t=0 and is (15/2)t at its first order. Dividing a generic H/t^4 perturbation by the t^2 Schur factor would miss that additional cancellation.

## 3. The uniform rescaled source inverse

Prescribe actual BODY shears

    C=t^5 c,        H=t^5 h,        U=V=0.             (10)

For fixed small c,h solve, by the first joint analytic IFT,

    F(t,w,L)=(t^2 c,t h,0).                            (11)

The solution w(t,L,c,h) exists jointly near t=0,L=L_*,c=h=0, has w(0,L,c,h)=w_0(L), and remains positive. Its order-t coefficient differs from the zero-target branch by h A(L)^-1 e_H. The order-t^2 change from c enters F_C directly.

Substitute in J. Because J_0 is identically zero and J_1(w_0(L),L)=0, the substituted J, and hence G, is divisible by t^2 as a joint analytic function. Since J_1 is affine, no h^2 term enters that order. Equations (5),(9) and the accepted zero-target coefficient (4) give

    G(t,w(t,L,c,h),L)=t^2 Gamma(t,L,c,h),
    Gamma(0,L,c,h)=P(L)-(3/2)c+(15/2)h.                (12)

The derivative with respect to L at (0,L_*,0,0) is P'(L_*)>0. A second joint analytic IFT therefore supplies L(t,c,h) with Gamma=0 for |t|,|c|,|h| sufficiently small. For positive t, it gives STRICT actual arms and connectors, and solves ALL FOUR body equations (10) exactly. Negative t belongs only to the analytic extension and is never an admitted source.

This is a legitimate cap-four source realization, not merely a linear condition. For arbitrary, even nonanalytic prescribed shear paths, substitution of c(t),h(t) into the uniform chart is valid whenever both remain in its open domain. In particular body shear size

    alpha(t)=max(|C|,|H|)=o(t^5)                       (13)

keeps c,h->0 and gives parameters approaching the original normalized base. Small constant multiples of t^5 also lie in the chart, with a nearby shifted limiting L satisfying (12). The chart does not cover every larger shear path; no necessity claim about (13) is made.

## 4. Genuine positive padding to the SAME fixed pair survival

Fix a in (0,1). Use a trailing ordinary survival u=1-t and set the leading survival

    zeta=a/[q_body(t,w,L)u].                           (14)

Here q_body=Q_1Q_2Q_3(1-Lt)^2->1, so for sufficiently small positive t, zeta belongs to (0,1), tends to a, and gives pair survival exactly a. All padding is an original positive source edge.

The original [four-root quotient composition](../2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md) gives, for E(zeta)Body E(u),

    C_full=zeta^6 u C_body,
    H_full=zeta^6[H_body+(1-u)C_body].                 (15)

To prescribe FULL shears C_full=t^5 c_f,H_full=t^5 h_f, the exact body targets in the first IFT are

    c=c_f/(zeta^6 u),
    h=h_f/zeta^6-(1-u)c.                              (16)

The quantities zeta depend analytically on (t,L) through q_body, which is independent of w. Therefore equations (11),(16) still form a joint analytic IFT, with the same w-Jacobian at t=0. Their limiting targets are c_f/a^6,h_f/a^6, and the second equation's limiting coefficient is

    P(L)-(3/2)c_f/a^6+(15/2)h_f/a^6.                 (17)

It again has a simple root near L_* for sufficiently small c_f,h_f. Thus the SAME fixed a admits a uniform cap-four rescaled source chart with full shear scale t^5.

For the required padded conjugator factors, their exact unit-diagonal conjugator has cap-four coordinates C=u_epsilon,H=v_epsilon. Source-group composition gives

    C_P=a^6 u_epsilon,    H_P=a^6 v_epsilon,
    C_R=-a u_epsilon,     H_R=-v_epsilon-(1-a)u_epsilon. (18)

These follow from the same quotient product, including C_inverse=-u_epsilon,H_inverse=-v_epsilon. Hence both have shear size O(alpha_epsilon), where alpha_epsilon=max(|u_epsilon|,|v_epsilon|)->0. The choice alpha_epsilon=o(t_*(epsilon)^5) is sufficient to place both in the small rescaled cap-four charts (their physical parameters need not agree). No order alpha_epsilon=epsilon^k is assumed or inferred from the weak-diagonal source provider. One may, for example, choose a positive t_* tending to zero more slowly than alpha_epsilon^(1/5), using the actual shear value.

## 5. Why this does not supply either higher-cap membership

Every source in these charts retains A=(1,2,1), positive half-route arms and exact U=V=0. The companion [moving-base diagonal proof](MOVING-BASE-FIFTH-DIAGONAL-OBSTRUCTION.md) therefore forces D_5=t^5/16+O(t^6)>0 regardless of c,h or their relative rate. Both required factors instead have D_5=0 exactly. Improving conditioning, taking alpha_epsilon much smaller, or choosing a slower-moving base supplies a cap-four lift but cannot extend that SAME physical lift to cap five.

The exact remaining membership question requires a different source direction: another limiting mean-ratio family, more cells, other coins or another original admitted architecture, with the new fifth diagonal and the complete higher-grade response solved by the SAME strict parameters. There is no statement here about all positive source words, the closure of their image, arbitrary-core/menu completeness, full-prefix rivals or detectable stopping. Original G4 remains OPEN.
