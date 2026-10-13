# Uniform all-arity positivity for sufficiently small bad cells

Contributor: Codex chronology subagent, 13 October 2026. Status: hand-proof candidate awaiting independent review. The compact-uniform parabolic limit was obtained independently in this lane and the fixed-target-negative review lane; its detailed proof is supplied by the latter. No Lean verification, numerical certificate of the universal quantifier, or general G4 closure is claimed.

## Master obligation and precise advance

The unresolved calibrated private BOTH compactification can have a countable persistent skeleton with no first cell and a represented ordinary prefix c smaller than the finite target's prefix a. The inherited diagonal identity forces an infinite such skeleton to carry a superlogarithmic negative diagonal reservoir among cells satisfying h^2>2t. The previously accepted primitive positivity theorem only covered nt<=1/16.

Here is a uniform strengthening in the actual small-cell corner:

**Candidate theorem.** There exists delta>0 such that, for every actual equal-arm INDEPENDENT cell B(t,g), if

    0<t<delta,   0<|h|<delta,   h=log(g/(1-g)),   h^2>=2t,

then its inherited first primitive satisfies

    A_n(B(t,g))>0 for EVERY integer n>=4.                (1)

The parameters are those of one cell, shared across all arities. The conclusion is uniform in n; it is not a choice of different parameters at each n. Delta is established semantically by contradiction, without an explicit computable value in this note.

For an endpoint-equal source-derived countable carrier, the inherited budgets sum t_i<infinity and sum log cosh(h_i/2)<infinity imply that all but finitely many bad cells satisfy (1). Thus any still possible initial mixed tail has uniformly positive primitive contributions from all sufficiently small bad cells, at every arity. The remaining negative contributions can come from interlaced good cells h_i^2<2t_i. Controlling that signed chronological cancellation is still open. The theorem alone does not force a finite skeleton, supply a legal general observer bridge or construct exact fixed-target rivals.

## Inherited decomposition, with a positive term retained

Use the exact October 10 two-merger integral and hyperbolic inequality. Put m=n-2, r=n-4, p=g(1-g), D=cosh(h)-1. Under the r-root centered binomial tilt proportional to

    binom(r,r/2+X) exp(hX-tX^2),

write, for 0<u<v<t,

    s=u+v, d=v-u,
    Delta(u,v)=E cosh(h-sX)-E cosh(dX).

The reviewed inequality with s+d=2v<=2t gives Delta>=0. The actual primitive therefore decomposes as A_n=P_n-N_n, where

    P_n=C_n E_m^*[kl] 2p integral_(0<u<v<t)
                 exp(-m(u+v)/2) exp(-u) Delta(u,v) du dv >=0,
    C_n=n(n-1)/[4(2n-3)],

and N_n is the same expression with exp(-u)Delta replaced by (1-exp(-u))E cosh(dX). The proof of the inherited source-uniform negative bound establishes specifically

    0<=N_n<=1/20.                                      (2)

It is essential to reuse this positive/negative integral decomposition, rather than infer a bound on a truncated integral merely from A_n>=-1/20.

The inherited tilt estimates, valid for every t>=0, are

    E X <= r tanh(h/2)/2,
    E X^2 <= r/4+r(r-1)tanh(h/2)^2/4,
    E_m^*[kl] >= m(m-1)p.

Arm exchange permits h>=0. The last inequality comes from decreasing quadratic Gaussian reweighting of the centered unpenalized binomial; it preserves the actual source's coin.

## A large-nD lower bound

Fix epsilon=1/32. Suppose n>=6, nt>=epsilon, p>=1/8 and nD>=1. On the smaller triangle 0<u<v<epsilon/n, convexity of cosh gives

    E cosh(h-sX) >= cosh h-s sinh h E X
                  >=1+(1-epsilon)D,

using sinh(h)tanh(h/2)=D. Also |X|<=r/2, d<=epsilon/n, and cosh(epsilon/2)<=2, so

    E cosh(dX)-1
      <= (d^2/2) E X^2 cosh(epsilon/2)
      <= epsilon^2/(4n)+epsilon^2 D/8.

Consequently

    Delta >=(1-epsilon-epsilon^2/8)D-epsilon^2/(4n)
           >=D/2.                                    (3)

Every factor in P_n is nonnegative, so the rest of its integration region can be discarded. On this triangle,

    exp(-m(u+v)/2-u)>=1/2,
    C_n>=n/8,
    E_m^*[kl]>=n^2 p/4,
    triangle area=1/(2048 n^2).

Equations (2)-(3), p>=1/8, and direct multiplication give the deliberately loose bound

    A_n >= 2^(-24) nD -1/20.                           (4)

In particular, along any source sequence with h->0, nD->infinity and nt>=1/32, the primitive is eventually strictly positive. This does not require nt bounded or a separate fixed-cell asymptotic.

## Compact moving-scale input

For actual cells t_n=x_n/n and h_n=y_n/sqrt(n), with x_n in a compact subset of (0,infinity) and y_n in a compact real interval, the exact integral and tilted-binomial central limit theorem give, uniformly on those compact sets,

    A_n(B(t_n,g_n)) -> F(x,y),

    F(x,y)=[x^2 y^2-2x^2+8-2(x+2)^2 exp(-x)]
                                    /[64(x+2)^2].      (5)

The exact physical coin is g_n=logistic(h_n). This is an asymptotic proof device, not an admitted infinite source. A complete proof is in [the independent compact-uniform review-lane note](../fixed-target-negative/FIRST-PRIMITIVE-REVIEW-AND-PARABOLIC-LIMIT.md); here is the normalization check. With u=a/n,v=b/n and Z=X/sqrt(n), the tilted limit is normal with

    mean y/(4+2x), variance 1/(4+2x).

The surviving integrand is

    (1/64) exp(-(a+b)/2)
      [-a+y^2/2-y(a+b)EZ+2ab EZ^2],  0<a<b<x.

Its elementary integral is (5). Polynomial-times-exponential binomial moment bounds control the Taylor remainders and justify compact uniformity.

On y^2>=2x, F is strictly positive. A short check writes its numerator lower bound as twice

    G(x)=x^3-x^2+4-(x+2)^2 exp(-x).

Here G(0)=0 and

    G'(x)=x[3x-2+(x+2)exp(-x)].

The bracket vanishes at zero and has derivative 3-(x+1)exp(-x)>=2; hence G(x)>0 for x>0. In fact y^2>=(2/3)x already suffices, by the same argument with derivative x[x-2+(x+2)exp(-x)]. The stronger boundary is not needed below.

## Proof of the uniform small-cell theorem

Suppose (1) were false for every delta. Choose t_j->0 and h_j->0, with h_j^2>=2t_j and integers n_j>=4, such that A_(n_j)(B(t_j,g_j))<=0. Exchange the two arms to make h_j>0.

The inherited weak-scale theorem excludes n_j t_j<=1/16. Pass to a subsequence with n_j t_j>1/16. Necessarily n_j->infinity.

If n_j D_j is unbounded, pass to a subsequence tending to infinity. Eventually p_j>=1/8, n_j>=6, and n_j t_j>=1/32. Bound (4) contradicts A_(n_j)<=0.

Otherwise n_j D_j is bounded. Since D_j/h_j^2->1/2, y_j^2=n_j h_j^2 is bounded. The bad-cell premise and the exclusion above give

    1/16<x_j=n_j t_j<=y_j^2/2.

Pass to a subsequence with x_j->x>0 and y_j->y, where y^2>=2x. The compact-uniform limit (5) gives A_(n_j)->F(x,y)>0, again a contradiction. These alternatives exhaust every countersequence and prove existence of delta.

## Countable-carrier consequence and exact remaining cancellation

For any fixed countable carrier satisfying the two inherited budgets, only finitely many persistent cells have t_i>=delta or |h_i|>=delta. Every other bad cell satisfies (1). If there is no first persistent cell, each of the finitely many exceptions starts at a strictly positive source position. An initial common-clock interval can therefore be chosen with no exceptions. On that interval all bad-cell primitive terms are nonnegative at every arity; their actual prefix transport factors are positive.

This does NOT permit discarding earlier good-cell negative terms. Their total transported negative part is bounded by the inherited constant, but that bound does not compare exponential attenuation rates. The supplied finite target has exponentially attenuated primitive, whereas an initial positive reservoir can be very small after chronological transport. A source-sensitive comparison with the good-cell contribution, or a stronger full-forest argument, remains necessary.

## Verification boundary

This note uses the reviewed October 10 source formulas, the independently derived compact-uniform Gaussian limit, elementary inequalities, and a sequential compactness contradiction. No finite numeric screen certifies the universal sign, no Lean theorem is supplied, and original full-core transfer remains separate. The stronger conjecture A_4>=0 => A_n>=0 for every actual strict cell is not assumed and remains unproved.
