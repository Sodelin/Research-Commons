# Finite root-rate and root-time bounds from the original AC means

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. The root Codex lane proposed the divided-difference identity; this lane checks it against the original formulas and derives the bounds below. **Hand-derived component, independent review pending.** No numerical scan, arithmetic job, provider call, observation replay, sampling, inverse run or compiler occurred.

Keep the original nine-parameter D and source. Here c=8/3 is the FIXED Laplace unit, R=rR in [1/2,6], and T=h+u+v in [3/32,3/8]. The original [AC formulas and root inversion](../2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md) give raw moments

    a=AC1=exp(−cT)*R/(R+c),
    b=AC2=exp(−2cT)*R/(R+2c),
    rho=b/a^2=1+c^2/D,  D=R*(R+2c).

The corresponding shifted Bernoulli means are mu1=(1+a)/2 and mu2=(1+b)/2. These are the original one- and two-site features on one genealogy, with no within-locus independence assumption. The root inversion itself and its Durden–Sullivant predecessor retain the attribution in the inherited theorem; no new inverse principle is claimed.

## Exact finite rate comparison

For ANY two coherent original sources, subscripts 0 and 1 identify values, and Delta=value0−value1. Define the signed residual

    E=Delta b−rho1*(a0+a1)*Delta a,
    E_mu=Delta mu2−rho1*(a0+a1)*Delta mu1,  E=2E_mu.

Direct finite subtraction, without derivatives on an observed-image path, gives

    E=a0^2*(rho0−rho1),
    rho0−rho1=−c^2*(R0−R1)*(R0+R1+2c)/(D0*D1),
    Delta R=−K*E,
    K=D0*D1/[c^2*(R0+R1+2c)*a0^2] >0.           (1)

Use the ACTUAL shared source relation for a0 before bounding K:

    K=exp(2cT0)*[R1*(R1+2c)/c^2]*H_R1(R0),
    H_y(x)=(x+c)^2*(x+2c)/[x*(x+y+2c)].          (2)

This retains T0/R0 dependence. Bounding the inverse-rho sensitivity and a0 independently would lose it. The residual likewise remains a signed AC2/AC1 contrast rather than an independently fitted pair of marginal means. Equations (1)–(2) remain well-defined at equal root rates.

## Explicit source and cell coefficients

For fixed x>0, `y*(y+2c)/(x+y+2c)` increases in y: its derivative numerator is `y^2+2xy+4cy+2cx+4c^2>0`. For fixed y>0, polynomial division gives

    H_y(x)=x+2c−y
       +[2c^3/(y+2c)]/x
       +[y*(y+c)^2/(y+2c)]/(x+y+2c).

Both reciprocal coefficients are positive, so H_y is convex in x>0. Therefore, for sources whose physical root-coordinate bounds are

    R0 in [l0,u0], R1 in [l1,u1], T0 ≤ t0_upper,

with all bounds inside original D, a finite two-cell bound is

    K ≤ K_cells
      =exp(2c*t0_upper)*u1*(u1+2c)/c^2
         *max(H_u1(l0), H_u1(u0)).               (3)

The exact sourcewise coefficient (2) and cell formula (3) can be much smaller than the global fallback. They apply to the complete specified physical sets, including between-cell pairs. No mean-image convexity or inverse-Jacobian integration is used. A numerical implementation would still need rigorously enclosed exponentials and certified physical cell bounds; no cell evaluation or contraction is performed here.

For the WHOLE original D, take y=6 and x in [1/2,6]. The endpoint values are

    H_6(1/2)=12635/1278 > H_6(6)=221/27,
    K ≤ exp(2)*214795/2272 <1933155/2272 <851.

The first comparison has positive cross-product difference 58707; the last integer comparison has positive difference 317. The middle bound uses exp(2)<9 from e<3. Thus a concrete global component bound is

    |Delta R| ≤851*|E|=1702*|E_mu|.              (4)

Normalized root-rate error is at most 2/11 times the right side because the ORIGINAL rate-domain width is 11/2. This bound does not guarantee that an actual admitted confidence set controls E_mu at a useful precision; that statistical binding is still missing.

## Root time through its actual logarithm

Set `v_i=a_i*(1+c/R_i)=exp(−cT_i)`. The exact logarithm identity is

    c*(T0−T1)=log(v1/v0)
      =log[a1*R0*(R1+c)/(a0*R1*(R0+c))].

All arguments are positive for original sources. Exact subtraction and (1) give a second signed residual

    J=v0−v1
      =(1+c/R0)*Delta a−a1*c*Delta R/(R0*R1)
      =(1+c/R0)*Delta a+a1*c*K*E/(R0*R1).        (5)

Applying the elementary log bound on the POSITIVE scalar interval between v0 and v1 yields

    |Delta T| ≤ |J|/[c*min(v0,v1)]
      =exp(c*max(T0,T1))*|J|/c <(9/8)*|J|.      (6)

This scalar logarithm comparison is justified directly by its positive arguments; it does not integrate the inverse root Jacobian along a possibly unrealized mean-image segment. Formula (5) keeps the cancellation between the two AC errors and root-rate adjustment. For cells, replace max(T0,T1) in (6) by their proved time upper bound and K in the exact expression by a rigorous enclosure when forming a signed interval.

If a scalar fallback is needed, `1+c/R0≤19/3` and `a1*c/(R0*R1)≤32/19` follow from the actual source relation for a1. Together with (4), they give

    |Delta T| ≤(9/8)*[(19/3)*|Delta a|
                         +(32/19)*851*|E|].      (7)

This deliberately coarse fallback may be unsuitable for practical precision. Equations (2), (3), (5) and (6) preserve the useful conditioning and dependencies; one must enclose the combined signed residual before taking its magnitude.

## Remaining original-source obligations

The T bound feeds the [accepted C-rate component](../2026-10-07-cloud-practical-cc1-propagation-1948z/CC1-ERROR-PROPAGATION.md); rC then feeds the [accepted g component](../2026-10-07-cloud-practical-g-propagation-1932z/G-ERROR-PROPAGATION.md) and the [AA1 component](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md). h/g cross-nuisance recovery and A=h+u onset/rate recovery remain hard gates. A usable prospectively admitted joint mean-error set and complete noninflating source cover, including all cells and exported union widths, remain separate. No source was fitted or discarded, no confidence event was added, and no whole-D all-nine normalized 1/20 success is claimed.
