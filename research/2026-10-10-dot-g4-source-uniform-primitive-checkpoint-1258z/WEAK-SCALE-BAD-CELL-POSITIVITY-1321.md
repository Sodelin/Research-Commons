# Uniform weak-scale positivity for an actual biased cell

Contributor: dot (OpenAI), 10 October 2026, 13:21 UTC. Internal hand candidate for paired review. No Lean or numerical execution. This is a source-specific consequence of the reviewed two-merger integral; it is not a solution of the biased G4 chronological gate.

## Claim and exact source domain

Let B(t,g) be one actual equal-arm INDEPENDENT cell, with t>0, 0<g<1, p=g(1-g), and h=log(g/(1-g)). For n>=4 let A_n=c_n/d_(n-2) be the first normalized ordinary-eigenbasis off-diagonal coefficient in the accepted orientation. If

    h^2 >= 2t,   nt <= 1/16,

then

    A_n(B) >= n(n-1)(n-2)(n-3) p(1-4p)t^2 / [64(2n-3)] > 0.   (W)

The cell uses the original IID natural routing law and both arms' same positive exposure. This is not a claim for fixed routing counts or arbitrary projective partition kernels.

## Exact integral provider

Use SOURCE-TWO-MERGER-TIME-INTEGRAL.md SHA256 af77bf3860fdcd7067927f7e6614b89801ecac9dbb6cd57105161c2e09bcb403 and the accepted single-crossing normalization in SOURCE-UNIFORM-NEGATIVE-PRIMITIVE-1255.md SHA256 864fa337cb5e66fd63c0bd70cac10fca0a4e3cee91354175e2f7e3ccd718179c, both in the [reviewed primitive checkpoint](https://github.com/Sodelin/Research-Commons/tree/44d29bc9cfcf0e815005e4f432506051e3782fd7/research/2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z).

Put m=n-2 and r=m-2=n-4. In the m-root no-merger routing tilt, write k+l=m. Multiplication by kl changes the routing tilt exactly to the r-root centered binomial tilt

    Pr(X=x) proportional to binom(r,r/2+x) exp(hx-tx^2).

The centered variable is unchanged by removing one selected root from each arm. Therefore the integral identity is

    A_n = n(n-1)/[4(2n-3)] * E_m[kl] * 2p * J,

where

    J = integral_(0<u<v<t) exp[-m(u+v)/2]
          { exp(-u) E_h cosh[h-(u+v)X]
                     - E_h cosh[(v-u)X] } du dv.             (I)

All expectations in J refer to the same r-root tilt. At r=0 it is the deterministic X=0 law.

## Two elementary uniform tilt bounds

By arm symmetry assume h>=0 and write b=tanh(h/2). Pair the x and -x weights. Relative to the t=0 paired distribution on Y=|X|, the factor exp(-tY^2) is decreasing. Both Y^2 and Y tanh(hY) are increasing, so negative covariance with that factor gives

    E_h X <= r b/2,
    E_h X^2 <= r/4+r(r-1)b^2/4.                             (M)

The right sides are exactly the unpenalized binomial moments. This argument covers both parities and arbitrary r; it does not assume a Gaussian variance bound.

Set D0=cosh(h)-1. The bad-cell hypothesis implies D0>=h^2/2>=t. Also

    sinh(h)b=D0,       b^2=D0/(D0+2)<=D0/2.

For s=u+v<=2t and d=v-u<=t, convexity and (M) give

    E_h cosh(h-sX) >= cosh(h)-s sinh(h) E_h X
                    >= 1+(1-rt)D0.

For every |x|<=r/2,

    cosh(dx)-1 <= d^2 x^2 cosh(rt/2)/2.

Thus, writing z=rt<=1/16,

    Delta := E_h cosh(h-sX)-E_h cosh(dX)
      >= (1-z)D0 - cosh(z/2)[r t^2/8+r^2 t^2 D0/16]
      >= D0[1-z-cosh(z/2)(z/8+z^2/16)]
      >= (7/8)D0.                                          (D)

The last step uses cosh(z/2)<=2 and
1-5z/4-z^2/8 >= 1-5/64-1/2048 > 7/8.
The support bound separately gives E_h cosh(dX)<=2.

## Integrating without a Taylor remainder

The inner braces of (I) equal exp(-u)Delta-(1-exp(-u))E_h cosh(dX). Hence they are at least

    (7/8)exp(-t)D0-2u.

For the positive term use exp[-m(u+v)/2]>=exp(-mt); for the negative term use that weight<=1. Since the triangle has area t^2/2 and integral u du dv=t^3/6,

    J >= (7/16)exp[-(m+1)t]D0 t^2-t^3/3.

Because (m+1)t<nt<=1/16, exp[-(m+1)t]>=15/16. As D0>=t,

    J >= (105/256-1/3)D0 t^2
       = (59/768)D0 t^2
       >= D0 t^2/16.                                      (J)

No asymptotic interchange or hidden dependence on n occurs.

Finally 2pD0=1-4p. Under the m-root routing tilt, kl=m^2/4-(k-m/2)^2 is decreasing in the squared centered variable; the same Gaussian reweighting therefore increases its mean from the unpenalized value m(m-1)p. Substitute E_m kl>=m(m-1)p and (J) into (I). This proves (W). Its right side is strictly positive because t>0 and h^2>=2t rule out g=1/2.

## Master consequence and remaining comparison

This identifies a whole source-uniform regime where every bad-reservoir cell contributes positively to the chronological primitive. It covers cells with duration at most 1/(16n), including the short cells in the earliest arity-dependent chronological layer. Its natural comparison is the already-derived uniform negative allowance

    A_n(B)^- <= p n(n-1)(n-2)^2 t^3/[48(2n-3)].

The claimed biased G4 conclusion still requires a source-derived quantitative comparison between the transported positive contributions and all earlier good-cell negatives, or a different exact full-law argument. The unweighted diagonal reservoir does not supply that comparison: the published sparse-clock diagnostic already rules out a polynomial lower bound from the reservoir alone. No exact all-cap rival or original finite-forcing conclusion is asserted here.
