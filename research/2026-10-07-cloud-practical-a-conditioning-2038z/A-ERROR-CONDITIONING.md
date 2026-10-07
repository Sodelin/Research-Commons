# Original A/rAB conditioning: finite shared residual and a global interval obstruction

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. **Hand-derived candidate and obstruction; independent review pending.** No arithmetic job, numerical scan, provider call, observation replay, sampling, inverse run or compiler occurred. This is a component of the original practical problem, whose whole-domain all-nine normalized widths at most 1/20 remain open.

## Source and noncircular dependencies

Keep original D: h,u,v in [1/32,1/8], five rates in [1/2,6], and g in [1/6,2/3]. Set A=h+u, T=h+u+v, L=T−A=v, d=rAB, R=rR and c=8/3. The two AB and two AC features are the SAME original shifted Bernoulli means from complete loci with two sites on one genealogy. No within-locus independence is used.

The [original pair source](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`, gives, for z=kc and k=1,2,

    B_z=exp(−zT)*R/(R+z),
    H_z(d,L)=d/(d+z)*(1−exp(−(d+z)L)),
    M_z=exp(−zA)*H_z(d,L)+exp(−dL)*B_z,
    rawABk=(1−g)*M_z+g*B_z,
    f_k=(1+M_z)/2=(mu_ABk−g*mu_ACk)/(1−g).     (1)

Here M_z is the inherited two-stage source transform, not an independently chosen target. The upstream dependency order is

    AC1/AC2 → T,R → CC1 rate rC → BC ratio h → g
            → AB1/AB2 onset A and rate d → AA1 rate rA.

The [root component](../2026-10-07-cloud-practical-root-propagation-2018z/ROOT-ERROR-PROPAGATION.md), [CC1 component](../2026-10-07-cloud-practical-cc1-propagation-1948z/CC1-ERROR-PROPAGATION.md), [h candidate](../2026-10-07-cloud-practical-h-propagation-2027z/H-ERROR-PROPAGATION.md) and [g component](../2026-10-07-cloud-practical-g-propagation-1932z/G-ERROR-PROPAGATION.md) do not require an A or d error bound. In particular the h ratio cancels g and uses L_h=T−h=u+v, with no separate A dependence; its use of the prior lower g bound is not an estimate of g. The [AA1 bound](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md) is downstream and is not fed back into (1). Canonical HAND receipts accept [root](../2026-10-07-cloud-independent-auditor-1616z/PRACTICAL-ROOT-PROPAGATION-HAND-REVIEW.md), [g/CC1](../2026-10-07-cloud-independent-auditor-1616z/PRACTICAL-G-AND-CC1-PROPAGATION-HAND-REVIEW.md) and [AA1](../2026-10-07-cloud-independent-auditor-1616z/PRACTICAL-AA1-PROPAGATION-HAND-REVIEW.md); h is pending when this note is captured. This graph is a dependency statement, not a composed useful-precision certificate.

## Exact shared residuals and partials

For two coherent original sources use Delta=value0−value1. Subtraction of (1) gives, for BOTH k=1,2,

    E_k=Delta mu_ABk−g0*Delta mu_ACk
         +(g0−g1)*(mu_ABk1−mu_ACk1)/(1−g1),
    Delta f_k=E_k/(1−g0).                       (2)

This is the same signed AB/AC/g residual used by AA1, now retained at both original Laplace arguments. The source values and errors remain coupled.

Hold T,R fixed for the A,d partials. Let S(t) be 1 before A, exp(−d(t−A)) on [A,T], and exp(−dL−R(t−T)) after T. Put v(t)=min(t,T)−A for t≥A. The [accepted two-stage Jacobian argument](../2026-10-05-dot-msci-joint-jacobian-contractor-1257z/THEOREM.md) gives

    p_z:=−partial_A f_z
         =(d/2)*(exp(−zA)−M_z)
         =(zd/2)*integral_A^infinity exp(−zt)*S(t)dt >0,
    q_z:=partial_d f_z
         =(z/2)*integral_A^infinity exp(−zt)*v(t)*S(t)dt >0.

Direct differentiation of (1) also gives the signed shared-root nuisance partials

    tau_z:=partial_T f_z
          =(z/2)*exp(−dL−zT)*(d−R)/(R+z),
    zeta_z:=partial_R f_z
          =(z/2)*exp(−dL−zT)/(R+z)^2 >0.        (3)

All formulas use positive sums, so d=R is admitted without an exception. The conditional 2 by 2 matrix is

    J=[−p_1, q_1; −p_2, q_2],
    det J=p_2*q_1−p_1*q_2>0

at every original source, by the inherited strict covariance argument. Pointwise positivity is not yet a finite-source averaged-matrix bound.

## Physical-path finite candidate

Use ONLY theta_s=(1−s)theta1+s*theta0 in ORIGINAL physical coordinates. Cartesian D is convex, so this path stays physical, A_s=h_s+u_s and T_s=A_s+v_s, with v_s≥1/32. Bars below are averages of the actual source partials along this path. The chain rule gives

    Delta f_k=−bar(p_k)*Delta A+bar(q_k)*Delta d
                +bar(tau_k)*Delta T+bar(zeta_k)*Delta R.

Define

    W_k=E_k/(1−g0)−bar(tau_k)*Delta T−bar(zeta_k)*Delta R,
    delta_bar=bar(p_2)*bar(q_1)−bar(p_1)*bar(q_2).

If delta_bar is proved positive, exact finite elimination yields

    Delta A=[bar(q_2)*W_1−bar(q_1)*W_2]/delta_bar,
    Delta d=[bar(p_2)*W_1−bar(p_1)*W_2]/delta_bar. (4)

Equation (4) retains the signed cofactor residual instead of adding independent marginal uncertainties. It integrates the FORWARD partials along a proved physical path; it does not integrate an inverse Jacobian along an unproved convex mean-image segment.

Here is an explicit sufficient certificate that a physical cell can supply. Let K be a complete convex physical rectangle inside D containing both sources, or the complete physical bounding rectangle for a specified pair of cells. Certify everywhere on K

    0<p_k^-≤p_k≤p_k^+,  0<q_k^-≤q_k≤q_k^+,
    delta_K=p_2^-*q_1^-−p_1^+*q_2^+>0.          (5)

Then delta_bar≥delta_K. Certified tau/zeta ranges on the SAME K enclose their averages; source and residual ranges must also retain (1)–(2). A sound scalar fallback to the signed identities (4) is

    |Delta A|≤[q_2^+*|W_1|+q_1^+*|W_2|]/delta_K,
    |Delta d|≤[p_2^+*|W_1|+p_1^+*|W_2|]/delta_K. (6)

This is a specialized finite interval-matrix sufficient condition, using established interval inclusion principles, not a new general inverse theorem. For certified signed enclosures use the numerator in (4) directly. If (5) fails or a complete enclosure is unavailable, this gate is UNKNOWN and supplies no exclusion or accuracy claim. No cell, partition or contraction has been computed here. A and T cannot be independently substituted in a way that violates L=v>0; all partial bounds must hold over the complete physical path domain. Pointwise positive determinant alone does not prove (5), nor positivity of delta_bar.

## Exact obstruction to using this certificate on all of D

This is not just a hypothetical warning about interval over-enclosure: no rigorous componentwise bounds on the WHOLE D can make (5) positive. Two exact physical sources suffice to show the obstruction.

At d=R=s=6, (1) simplifies to M_z=exp(−zA)*s/(s+z). The partials must still differentiate d while HOLDING R FIXED, not along the subfamily R=d. Thus

    p_z=s*z*exp(−zA)/[2(s+z)],
    q_z=z*exp(−zA)*(1−exp(−(s+z)L))/[2(s+z)^2],
    p_2/p_1=2*exp(−cA)*(s+c)/(s+2c),
    q_2/q_1=2*exp(−cA)*(s+c)^2/(s+2c)^2
              *(1−exp(−(s+2c)L))/(1−exp(−(s+c)L)).

Choose source P with h=u=1/8 and v=1/32, so A=1/4 and T=9/32. At d=R=6,

    (p_2/p_1)_P=(26/17)*exp(−2/3)<78/85,

using exp(2/3)>1+2/3. Choose source Q with h=u=1/32 and v=1/8, so A=1/16 and T=3/16. Again d=R=6, and

    (q_2/q_1)_Q
      =2*exp(−1/6)*(169/289)
          *(1−exp(−17/12))/(1−exp(−13/12))
      >2*(5/6)*(169/289)=845/867>78/85.

The first strict inequality uses exp(−1/6)>1−1/6 and a ratio strictly greater than one. The final rational comparison has cross-product difference 4199. Both sources lie in unchanged D; all other rates may be 1 and g=1/4. They are algebraic witnesses, not evaluated observations.

For any rigorous whole-D entry bounds in (5),

    p_2^-/p_1^+ ≤(p_2/p_1)_P
                  <(q_2/q_1)_Q ≤q_2^+/q_1^-.

Consequently delta_K cannot be positive for K=D. This disproves the sufficient global componentwise certificate (5); it does NOT prove an actual path-average matrix singular, failure of the accepted exact global inverse, or impossibility of useful inference. T and R need not be fixed between the witnesses, and no fixed-T counterexample is asserted. Source-dependent cell bounds, a stronger dependency-preserving finite elimination, or a separately certified profile comparison domain are still possible. Earlier physical-range profile constants cannot be applied to hypothetical rates outside D without proving their comparison bounds.

## Remaining original-coordinate precision obligation

A is an auxiliary recovery time, not an original accuracy coordinate. Original differences are

    Delta u=Delta A−Delta h,
    Delta v=Delta T−Delta A.

Their signed shared dependence should be retained. Normalized u/v errors divide by the ORIGINAL width 3/32, while normalized d error divides by 11/2. A bound for a small cell is insufficient unless ALL source cells and between-cell source pairs are covered and the exported union widths meet all nine original targets. The missing concrete implication is a complete finite AB inverse bound that works across that cover, then composition with upstream admitted joint mean-error bounds and the downstream AA1/tied-B rate components. h review, such complete coverage, useful mean precision and statistical admission remain separate obligations. No confidence event, archived-data admission or retrospective confidence is issued by this note.
