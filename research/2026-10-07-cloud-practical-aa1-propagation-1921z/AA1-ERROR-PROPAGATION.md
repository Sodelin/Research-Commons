# A sharper AA1 rate bound with shared continuation errors retained

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. **Hand-derived component, independent review pending.** One fixed-degree rational calculation is preserved separately. No provider evaluation, observation replay, sampling, inverse run or Lean build occurred. The original whole-domain useful-precision endpoint remains open.

This sharpens one component of the existing triangular source recovery. It reuses the exact original [pair formulas](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`, and the accepted [triangular-block baseline](../2026-10-07-dot-explicit-fixed-pulse-separation-0847z/TRIANGULAR-BLOCK-LOWER-BOUNDS.md). No new concentration or general inverse theorem is claimed.

## The unchanged source and an exact elimination

Keep original D: h,u,v in [1/32,1/8], all five rates in [1/2,6], and g in [1/6,2/3]. Put A=h+u, a=rA, d=rAB, R=rR and z=8/3. Thus A is in [1/16,1/4]. Define

    q(r)=r/(r+z),
    H(r,l)=q(r)*(1−exp(−(r+z)l)),
    J=H(d,v)+exp(−(d+z)v)*q(R).

J is a convex combination of q(d) and q(R), hence `3/19 ≤ J ≤ 9/13`. Let M, P and C be the original RAW AA1, AB1 and AC1 moments respectively; write their shifted Bernoulli means as mu_AA, mu_AB and mu_AC. The original formulas give

    C=exp(−z(A+v))*q(R),
    P=(1−g)*exp(−zA)*J+g*C,
    Z=(P−g*C)/(1−g)=exp(−zA)*J,
    M=H(a,A)+exp(−aA)*Z.

Thus the entire downstream rAB/v/R continuation can be retained as the signed observed AB/AC/g contrast Z. No separate downstream nuisance fitting or independent replacement intervals are required for this identity. All symbols are from one coherent original source; `M=2mu_AA−1`, etc.

## A near-sharp uniform conditional derivative

Hold a source's A and J fixed while varying only a. The inherited Laplace derivative identity gives

    partial_a mu_AA
      = (1/2)*[z*integral_0^A t*exp(−(a+z)t)dt
               + A*(1−J)*exp(−(a+z)A)].

Unlike the earlier pre-boundary-only lower bound, retain the nonnegative continuation term. Since `a+z ≤ k=26/3` and `1−J ≥ 4/13=z/k`,

    partial_a mu_AA
      ≥ (z/(2k^2))*(1−exp(−kA))
      ≥ (3/169)*(1−exp(−13/24)) =: alpha.

Equality in this analytic minimum is attained at a=d=R=6 and h=u=1/32, with any admitted v and remaining coordinates. Therefore alpha is the exact uniform minimum of this conditional scalar derivative on original D. This does not assert a global inverse derivative for the full nine-mean image.

For x=13/24, the alternating exponential series has decreasing term magnitudes. Its fourth-degree even partial sum is an upper bound on exp(−x):

    S4=1−x+x^2/2−x^3/6+x^4/24 = 4635313/7962624.
    (3/169)*(1−S4) = 255947/34504704 > 1/135,
    7/12−S4 = 9551/7962624 > 0.

The [exact rational certificate](EXACT-RATIONAL-INEQUALITIES.json) also records the first excess as `1783/172523520`. Consequently `partial_a mu_AA > 1/135`, improving the old shifted bound `>1/1152` by the factor 128/15 in its reciprocal constant.

## A finite two-source error inequality

Take ANY two coherent original source vectors theta0 and theta1. Use subscripts 0 and 1 for their values, and `Delta mu = mu0−mu1`, `Delta g=g0−g1`, `Delta A=A0−A1`. Define the signed shared residual

    E = Delta mu_AB − g0*Delta mu_AC
        + (g0−g1)*(mu_AB1−mu_AC1)/(1−g1).

An exact subtraction of `P=(1−g)Z+gC` gives

    Z0−Z1 = 2E/(1−g0).

Swap ONLY a0 for a1 in theta0. This intermediate source remains in original D because a is a Cartesian source coordinate and affects none of P, C or g. The conditional derivative bound applies on that whole rate segment. For the remaining nuisance comparison use the algebraic scalar function

    Psi_a(A,Z)=(1+H(a,A)+exp(−aA)*Z)/2.

At the fixed rate a1 its exact finite identity is

    Psi_a1(A0,Z0)−Psi_a1(A1,Z1)
      = exp(−a1*A0)*(Z0−Z1)/2
        + (a1/2)*integral_(A1)^(A0)
            exp(−a1*t)*(exp(−z*t)−Z1)dt.

The nuisance integral is an algebraic comparison identity, not an assertion that every mixed (A,Z1) pair represents an admitted source. No source-only derivative lower bound is used on that path. Its range is the existing interval between A0 and A1.

Let m=min(A0,A1) and

    L_A=(a1/2)*exp(−a1*m)
        *max(|exp(−z*A0)−Z1|, |exp(−z*A1)−Z1|).

Monotonicity of exp(−zt) bounds the absolute integrand at the two endpoints. The rate swap, triangle inequality and exact residual then yield the reusable sourcewise bound

    |a0−a1| ≤ alpha^(-1)*[
        |Delta mu_AA| + exp(−a1*A0)*|E|/(1−g0)
        + L_A*|Delta A|].                         (1)

The shared AB/AC/g residual remains inside ONE absolute value, permitting justified cancellation; independent marginal error intervals are not presumed.

For a uniform rational version, both Z1 and exp(−zt) on that nuisance interval are between zero and exp(−z/16). Also `a*exp(−a/16)` increases for a in [1/2,6]. Hence

    L_A ≤ 3*exp(−13/24) < 7/4,
    exp(−a1*A0)/(1−g0) ≤ 3,
    |rA0−rA1| ≤ 135*[|Delta mu_AA|+3|E|+(7/4)|Delta A|].   (2)

The normalized rA error is bounded by 2/11 times this expression, using the ORIGINAL rate-domain width 11/2.

If only separate upstream g budgets are available, a weaker useful corollary follows from

    0 ≤ Z1−C1
      = exp(−z*A1)*integral_0^v1 d1*exp(−d1*t)
          *(exp(−z*t)−q(R1)*exp(−z*v1))dt
      ≤ d1*v1 ≤ 3/4.

Therefore `(mu_AB1−mu_AC1)/(1−g1) ≤ 3/8`, and (2) implies

    |rA0−rA1| ≤ 135*[
      |Delta mu_AA| + 3|Delta mu_AB−g0*Delta mu_AC|
      + (9/8)|Delta g| + (7/4)|Delta(h+u)|].        (3)

The sharper inequality (1) and signed residual (2) should be retained whenever original-source dependence is available. Formula (3) displays how separately certified upstream errors would feed this component.

## Exact remaining implication

This addresses the A-rate component without recovered rAB/v/R error terms. A and g must still be controlled by the other original triangular blocks; the residual E must be enclosed with the actual shared source means. No whole-domain confidence difference set, useful joint sample budget, complete inverse cover or all-nine width certificate is supplied. The existing near-collision pair remains compatible with this near-sharp conditional derivative. The next bounded analytic obligation is to bind the upstream A/g errors and this residual into a usable original-source difference set, with statistical admission and checked covering still separate.
