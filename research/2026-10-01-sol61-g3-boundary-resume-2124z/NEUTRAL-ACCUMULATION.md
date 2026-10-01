# All-cap exclusion of one neutral critical-tail boundary

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-01 22:47 UTC.
Status: hand-derived theorem, submitted for independent review. Strict exact arbitrary-cap source recognition remains open.

## Contract

Retain the common-chain signature and closure normal form of [CLOSURE-NORMAL-FORM.md](CLOSURE-NORMAL-FORM.md) and the differential annihilator argument of [SINGULAR-NORMAL-FORMS.md](SINGULAR-NORMAL-FORMS.md). For fixed M>=2 let d=M-1 and lambda_j=j(j-1)/2. A nonattained finite-log closure point has, in every simplified normal form, a nonzero real covector c annihilating all two-sided retained-factor derivatives. Its strict retained pairs therefore belong to the critical set of

    g_c(p,q)=sum_j c_j log(1-p+p q^lambda_j),  0<p,q<1.

The sign change from H=-log(f) has no effect on criticality. The covector is fixed for the entire retained list. No global supporting-hyperplane assertion is used.

## Theorem 1: q=1 cannot accumulate a fixed nonzero critical set

For every fixed nonzero real c there is delta(c)>0 such that no simultaneous critical pair has 1-delta(c)<q<1, uniformly for all 0<p<1. This is an all-cap statement and includes simultaneous p tending to either endpoint. It is not a uniform bound as c varies.

Put q=exp(-x), x>0, and C_n=sum_j c_j lambda_j^n. The d by d matrix (lambda_j^n) with n=1,...,d is a usual Vandermonde matrix multiplied by the nonzero diagonal lambda_j. Thus some C_k is nonzero with 1<=k<=d; choose the least such k.

Define the Bernoulli cumulant polynomials by

    log(1-p+p exp(t))=sum_(n>=1) kappa_n(p) t^n/n!.

Here kappa_1(p)=p, and direct differentiation of this generating function gives

    kappa_(n+1)(p)=p(1-p) kappa_n'(p).

For n>=2, kappa_n has degree n, exactly the simple endpoint roots 0,1 and n-2 distinct simple roots inside (0,1). Proof: kappa_2=p(1-p). If the assertion holds at n, Rolle supplies n-1 distinct derivative roots strictly between its n ordered roots. The derivative has degree n-1, so these exhaust its roots and are simple; it is nonzero at both endpoints because those roots of kappa_n are simple. Multiplication by p(1-p) gives exactly the required n+1 simple roots for kappa_(n+1). The separate n=1 case also has no common root with its derivative. Consequently kappa_k and kappa_k' have no common root anywhere on [0,1].

Uniform expansion needs care here. On the compact interval p in [0,1], all finitely many f_j(p,x)=1-p+p exp(-lambda_j x) equal one at x=0. There is an open complex neighborhood of [0,1] times {0} in which every f_j stays nonzero and in the disk about one where a single analytic logarithm is defined. One can choose a uniform positive x radius by compactness, and a slightly larger closed complex p neighborhood. Analytic Taylor bounds, also after p or x differentiation, are therefore uniform on real [0,1]. In particular, with G_c(p,x)=g_c(p,exp(-x)),

    partial_p G_c = (-1)^k C_k kappa_k'(p) x^k/k! + O(x^(k+1)),
    partial_x G_c = (-1)^k C_k kappa_k(p) x^(k-1)/(k-1)! + O(x^k),

where the remainders are uniform for p in [0,1]. Lower terms vanish by the definition of k. Criticality in q is equivalent to criticality in x, since dq/dx=-q is nonzero.

If critical pairs had x_l->0, a subsequence would have p_l->p_0 in [0,1]. Divide the two zero derivative equations by their nonzero displayed scalar coefficients and x powers. The uniform errors tend to zero, giving kappa_k'(p_0)=kappa_k(p_0)=0, a contradiction. QED.

The roots/recurrence are elementary and related to the classical Eulerian-polynomial root structure. This proof is self-contained, rather than relying on Bernoulli-number polynomials (a different family). No numerical small-x exclusion is claimed.

## Theorem 2: the remaining summable tail is a rare-event interior-node branch

For fixed c, an infinite retained list with sum H_2 finite has u_i=p_i(1-q_i)->0. Theorem 1 excludes q_i->1. More explicitly, all its q_i are at most 1-delta(c), so p_i<=u_i/delta(c)->0.

The q derivative also excludes q_i->0 along this list. Let lambda_* be the smallest exponent with c_* nonzero. For p<=1/2,

    sum_j c_j lambda_j q^(lambda_j-1)/f_j(p,q)
      = q^(lambda_*-1) [c_* lambda_*/f_*(p,q)+O(q^(lambda_next-lambda_*))],

uniformly for p in [0,1/2], since 1/2<=f_j<=1. The leading term is bounded away from zero in absolute value for sufficiently small q, and cannot be cancelled by the other finitely many terms. Thus no such critical list can approach q=0. After discarding finitely many entries, its nodes lie in some compact interval [epsilon(c),1-delta(c)] contained in (0,1).

Every accumulation node r in that interval satisfies

    F(r)=F'(r)=0,  F(z)=sum_j c_j(1-z^lambda_j).

This follows by taking the p->0 limits of partial_p g and (partial_q g)/p. F is nonzero and has only finitely many positive roots, with the earlier Descartes bound. The tail can therefore accumulate only at finitely many interior double roots. This does not yet rule out a critical curve approaching those roots.

## Extra necessary condition for neutral-reaching critical curves

Suppose the strict critical set has an accumulation point (0,r) with 0<r<1. The set is semialgebraic after clearing denominators that are positive in the strict square. Semialgebraic curve selection supplies a smooth positive-p branch in the critical set tending to (0,r). Along that branch g_c is constant because its full gradient is zero, and continuity at p=0 makes that constant zero.

Write a_j(q)=1-q^lambda_j and F_n(q)=sum_j c_j a_j(q)^n. Uniformly near (0,r),

    g_c=-p F_1-p^2 F_2/2+O(p^3),
    partial_p g_c=-F_1-p F_2+O(p^2).

On the branch both g_c and partial_p g_c vanish. Subtract g_c/p from partial_p g_c, divide by p, and take the limit. This gives F_2(r)=0. Consequently every remaining neutral-reaching critical curve requires

    F_1(r)=F_1'(r)=F_2(r)=0.

These conditions are only necessary. No assertion that they exclude all real covectors is made. An infinite summable critical sequence forces such a branch because a semialgebraic critical set has finitely many isolated points and finitely many connected components; equivalently use curve selection on its closure directly.

## Consequence and remaining exact obligation

The only possible infinite retained-tail obstruction has p->0, q->one of finitely many strictly interior rare-event nodes, with the three displayed covector constraints. Countable tails approaching drift q=1 or the killing corner p=q=0 are excluded for every fixed annihilator. This strengthens the earlier all-real exceptional-curve target to a specific neutral branch.

The theorem does not exclude critical curves with that branch, provide a covector-independent minimum loss or integer multiplicity bound, remove singular compound-Poisson/killing terms, or establish finite strict attainment of the cap-eight candidate. A finite retained part alone would still leave the singular residue exact-attainment question.

## Prior-art scope and verification

[Huh, Varieties with maximum likelihood degree one](https://web.math.princeton.edu/~huh/MLDegreeOne.pdf), Definition 1 and Section 3, supplies the relevant logarithmic critical-variety language and generic finite critical count. Its sufficiently-general-covector theorem does not classify our special real covectors. The nonlinear Bernoulli surface is not silently identified with a hyperplane arrangement or an A-discriminant.

The two theorems above are hand proofs, with no Lean proof or all-input machine census claimed. The accompanying small exact cumulant recurrence/root-gcd controls are corroboration only. The full nonisolated-locus QE calibration timed out at cap four after 20 seconds. A separate cap-seven symbolic resultant timed out after 25 seconds. Both remain UNKNOWN; no cap-eight QE has been run. See the adjacent continuation checkpoint and the support-faithful resultant calibration packet.
