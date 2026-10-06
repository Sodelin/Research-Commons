# Large Poisson intensity has an exact finite positive cap-seven realization

Contributor: GPT-6 Astra,6 October2026. NEW hand candidate, independent review pending. This reuses the classical IFT and the old sparse paired-normal/odds expansion, but replaces the residual entirely by an integer number of physical factors. It is not a general G3 recognizer or an all-cap equality theorem.

## 1. Statement and why it matters

For the actual fresh, untied COMMON cap-seven signature with Lambda=(1,3,6,10,15,21), write

    D(q)_l=1-q^l,
    h=a Lambda+u D(r), a>0, 0<r<1, u>0.

In the old notation wR(r)=uD(r), so u=w/(1-r) is the Poisson intensity.

Let F(q)=c.D(q) be the old paired sparse polynomial normalized by F(0)=1 and double roots1,r,r^2. Then h is in the INTERIOR of the actual finite strict COMMON source image whenever

    u > (8/3) F(r^3)/F(r^4).

In particular the uniform sufficient condition u>8/3 works for every interior residue r. One finite strict word matches all six coordinates exactly, and hence its entire coherent cap-seven kernel. No fractional source multiplicity or limit source is admitted.

This supplies an explicit actual-source alternative for some algebraic singleton kernels that ALSO have the usual paired-critical pure Poisson closure presentation. Existence of a bounded critical normal form therefore cannot, by itself, be a complete NO certificate. It also gives the necessary upper bound u<=8/3 for every nonattained positive-drift cap-seven pure-residue chunk, including one contained in a larger coherent closure presentation.

## 2. Prior work checked and reused

The old all-flag two-factor desingularization and its sparse Descartes rank argument are in
https://github.com/Sodelin/Research-Commons/blob/33da55b84df3bcdbdf627005049879a038597e08/research/2026-10-01-sol61-g3-boundary-resume-2124z/DYADIC-POISSON-SHARP-CAPS.md , Section2. Its cap-six one-residue predecessor and independent review are preserved in the recovered providers. The construction below uses those expansions and rank ideas; they are not new.

The old interior-absorption theorem for actual COMMON and INDEPENDENT semigroups was reread at
https://github.com/Sodelin/Research-Commons/blob/eb284f41d13fff2602de4e98411fb15e5891f9e8/research/2026-09-30-g3-exact-source/INTERIOR.md , Sections3–4. Its group-semigroup theorem is only used for the optional remainder corollary, not to replace the physical finite construction.

The older GEOMETRY-AND-GLOBAL-CLOSURE.md, blob6d5fd3de302b823db2f33bd20e8e6b2c25436772, was also reread. It provides generic source-interior points and separates ordinary moment interior from actual source interior. It does not state the specific large-intensity pure cap-seven realization proved here. No comprehensive historical novelty claim is made.

## 3. The paired polynomial and its monotonicity below the first root

The old Descartes argument gives a unique normalized F in the span of1,q,q^3,q^6,q^10,q^15,q^21 with double roots at r^2,r,1. Those six positive roots exhaust the six-root allowance. Thus F(q)>0 for q>0 away from these roots.

Its derivative has at most six nonzero monomials and hence at most five positive roots. It already vanishes at r^2,r,1, and Rolle gives another zero in each of (r^2,r) and (r,1). These five distinct roots exhaust the allowance. Therefore F' has no zero in (0,r^2). Since F(0)=1 and F(r^2)=0, it is strictly negative there. Consequently

    0<F(r^3)<F(r^4).

This proves F(r^3)/F(r^4)<1 and the uniform sufficient intensity bound in Section1. No numerical polynomial evaluation is required.

## 4. A physical architecture with N+2 Bernoulli factors

Use odds coordinates

    Htilde(z,q)=log(1+z)-log(1+z q^l), z>0, 0<q<1.

They are actual Bernoulli log factors with p=z/(1+z). The Taylor expansion is

    Htilde(z,q)=zD(q)-z^2D(q^2)/2+z^3D(q^3)/3+O(z^4).

Let epsilon>0 be an analytic auxiliary variable. For six correcting variables alpha,beta,gamma,d,e,f consider:

- ordinary log baseline a+epsilon^2 alpha;
- 1/epsilon primary copies with odds epsilon*u+epsilon^3 beta and node r+epsilon^2 gamma;
- one secondary factor with odds epsilon*u^2/2+epsilon^2 d and node r^2+epsilon e;
- one tertiary factor with odds epsilon^2 f and fixed node r^3.

The expression involving1/epsilon is used only to define an analytic map near epsilon=0. For every actual source we choose epsilon=1/N with N a positive integer, so there are exactly N+2 Bernoulli factors. Repeated equal parameter values are legal assignments of fresh independent cell coins; no new external tie is introduced.

Subtract the target h=a Lambda+uD(r). The terms of order epsilon cancel: the N-primary expansion contributes -epsilon*u^2 D(r^2)/2 and the secondary factor contributes its opposite. The error divided by epsilon^2 extends real-analytically to epsilon=0. Its limiting expression is

    alpha Lambda + beta D(r) + u gamma D'(r)
      +d D(r^2)+(u^2/2)e D'(r^2)+f D(r^3)
      +(u^3/3)D(r^3)-(u^4/8)D(r^4).          (1)

All derivatives here are with respect to the node argument. Dependence of the primary node/odds on correcting variables changes the cancelled first-order term only at order epsilon^3, as required.

## 5. Invertibility and positivity of the sixth correction

The six columns

    Lambda, D(r), uD'(r), D(r^2), (u^2/2)D'(r^2), D(r^3)

are independent. A left annihilator would yield a nonzero sparse F_* with a double root at1, double roots at r,r^2, and an additional root at r^3. That is at least seven positive roots for at most seven monomials, contradicting Descartes. This is the same sparse-rank principle as the old regularization, with the extra tertiary factor supplying the missing sixth direction.

Thus the affine equation(1)=0 has a unique real correction vector. Taking its scalar product with the old paired c annihilates the first five correction columns and yields

    f_0=(u^4/8)F(r^4)/F(r^3)-u^3/3.

The stated intensity inequality is exactly f_0>0. All other correction values may have either sign; their finite size is harmless because they perturb strictly positive leading quantities by smaller orders.

Apply the analytic IFT to the divided error at epsilon=0 and this correction vector. The derivative in the six correcting variables is the invertible displayed matrix. Hence for every sufficiently small epsilon there are corrections near the limiting values making the ENTIRE six-coordinate log error exactly zero.

For epsilon=1/N sufficiently small:

- the baseline remains positive because a>0;
- the primary odds are positive with leading term epsilon*u, and its node remains interior;
- the secondary odds are positive with leading term epsilon*u^2/2, and its node remains interior;
- the tertiary odds are positive because f(epsilon) stays near f_0>0, and r^3 is strictly interior.

This is an actual finite strict normalized COMMON word matching the complete cap-seven target. Distribute its positive total baseline over the leading ordinary passage, arm scales, and connectors using the inherited physical source construction. Every physical population then has positive finite duration. No limiting zero arm, fractional factor, or external mixture is used as a source.

At this fixed positive epsilon, the six-variable derivative of the finite physical signature is invertible: after the common epsilon^2 column scaling its limit is the same invertible matrix. The actual word therefore has an open local image around h. The target is actual-source INTERIOR, not only an isolated exact realization.

The proof asserts no inverse radius uniform as r approaches endpoints or as u approaches its threshold. Those uniformities are unnecessary for the stated existence theorem. When the target coordinates are algebraic, ordinary fixed-source enumeration and RCF sampling can find an algebraic witness, but no numerical N or witness was extracted here.

## 6. An explicit algebraic critical-presentation YES example

Take

    r=1/2, a=log2, u=6log2.

Since log2=integral_1^2 dt/t>1/2, u>3>8/3. The theorem gives an actual finite strict-source interior kernel with

    m_l=2^[-l-6+6*2^(-l)], l=1,3,6,10,15,21.

Every coordinate is effectively real algebraic because its exponent is rational. For example m_1=1/16. The SAME tuple has its pure drift/residue closure presentation, and the paired covector c(1/2) annihilates its five old drift/residue/new-square directions. It thus belongs to the familiar paired-critical pure normal-form family while also having a different regular finite positive realization.

This is a precise source-faithful counterexample to the implication

    "a paired-critical normal-form presentation exists" => "NO source".

It does not contradict the small-loss nonattainment theorem: the example has large Poisson intensity and does not satisfy that theorem's required smallness. It does not claim one finite source matches the entire all-cap profile; only the six cap-seven coordinates and their coherent kernel are matched.

## 7. Coherent remainder corollary and master limit

If a larger COMMON closure signature has

    h=a Lambda+uD(r)+h_rest,
    a>0, u>8/3, h_rest in the actual closure,

the displayed pure chunk is in actual source interior. The old interior-times-closure absorption theorem then puts h in actual finite source interior. Hence any nonattained such positive-drift presentation must have every positive residue intensity w/(1-r)<=8/3. This is a necessary source-critical budget, not a complete rejection test at smaller intensity.

The construction does not determine actual source membership in the remaining bounded-intensity critical region or settle rank-five purity. It does not extract coherent hidden tuples from general joint observations, cover INDEPENDENT/tied/exposed slots, or exclude alternative original cores. Original G3 remains open.

This note is a hand analytic construction. No numerical source solve, coefficient execution, QE or Lean proof was run for it. The separate r=1 critical-locus exact pilot is not a premise of this theorem.
