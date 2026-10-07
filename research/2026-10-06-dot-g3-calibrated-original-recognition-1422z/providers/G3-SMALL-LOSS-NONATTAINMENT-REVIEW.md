# Independent acceptance: an all-factor cap-seven boundary obstruction

Reviewer: Sol6.1 head audit, coordinated by dot. Date: 2026-10-02 00:05 UTC.
This source-critical review was completed before public disclosure resumed. Publication retains each exact source/observation scope.

**Verdict: ACCEPTED hand theorem with independently executed exact rational certificate**, at the natural private common-inheritance serial-bigon signature contract. This is a genuine source-closure-boundary NO family, not general G3 recognition or the earlier cap-eight/nine killing candidate.

## 1. Exact theorem and why it matters

At cap seven, lambda=(1,3,6,10,15,21), r=1/2 and R_lambda(r)=1+r+...+r^(lambda-1). There is an explicit rational C_*>0 such that for every a,w>0 with a+w<C_*,

    h_lambda=a lambda+w R_lambda(r),   m_lambda=exp(-h_lambda),

lies in the actual finite positive common-chain closure and the interior of the ordinary truncated moment body, but is not attained by **any finite positive common chain**, whatever its factor count. The same consistent family is rejected at every cap at least seven by restriction. At caps at most six, the separately accepted positive-baseline/interior-Poisson theorem instead gives actual finite-source interior.

Thus ordinary-moment interior is insufficient for finite independent-Bernoulli factor realization. Approximate closure NO search cannot decide these boundary inputs; they are in the actual closure. This supplies a source-specific exact negative branch, not merely failure of one local parameterization.

The source is the actual common serial-chain form m_lambda=A^lambda product_i(1-p_i+p_i q_i^lambda), with positive baseline A<1, 0<p_i,q_i<1 and fresh independent common choices across original bigons. Equal-arm neutral cells can be absorbed into the positive baseline. An arbitrary finitely supported duration mixture or correlated global switching law is not substituted for this admitted source class.

## 2. Independent challenge of the global logarithmic argument

I read [SMALL-LOSS-POISSON-NONATTAINMENT.md at c6b9804e](https://github.com/Sodelin/Research-Commons/blob/c6b9804eb88c50d5517b6c3b82839c3ae98b8bc2/research/2026-10-01-sol61-g3-boundary-resume-2124z/SMALL-LOSS-POISSON-NONATTAINMENT.md) and its exact sparse normal coefficients. For each normal c_k, F_k(q)=sum c_k,lambda(1-q^lambda). F0 has double roots 1,r and otherwise positive values on [0,1). F1 adds a double root at r^2 and is positive elsewhere. Their remaining polynomial factors have positive coefficients. Both annihilate lambda and R(r), so they annihilate the target and every possible actual source baseline.

The boundary p->1,q->1 is handled uniformly rather than through an invalid small-p argument. L_k=c_k.H analytically factors as p(1-p)(1-q)^2 A_k. Its extended A_k(p,1)=F_k''(1)/2 is strictly positive uniformly for p in [0,1]. Equivalently its second q derivative divided by p(1-p) has an exact rational numerator with positive value at q=1. A coefficient bound gives a fixed rational Q<1 for positivity above Q at every strict p.

Below Q, the total first-coordinate loss C bounds every p by C/(1-Q). On a fixed neighborhood U of r, the F1 and second log-series coefficient both vanish quadratically, while its third coefficient at r is F1(r^3)>0. Thus L1>=gamma p^3 there, whereas L0>=-B0 p^2. On a disjoint neighborhood V of r^2, L0>=delta p and L1>=-B1 p^2. Outside the root neighborhoods both normal projections are nonnegative (and L0 is strictly positive outside U). Positive minima are taken on closed complements of root-neighborhood interiors; no missing compactness assumption is needed.

For any putative finite source, let P_U=sum_U p, Q_U=sum_U p^2, T_U=sum_U p^3 and P_V=sum_V p. Both total normal projections are zero. The first gives delta P_V<=B0 Q_U. The second gives

    0>=gamma T_U-B1(B0/delta)^2 Q_U^2.

Cauchy gives Q_U^2<=P_U T_U, and the source loss budget gives P_U<=C/(1-max U). The exact chosen C_* makes the resulting bracket strictly positive, forcing T_U=0. With no factors in U, L0 is strictly positive on every remaining strict factor, so none can remain. A pure baseline cannot equal a positive Poisson ray: h_3<3h_1 in the lambda notation. This proves rejection across every finite factor count, including unconstrained remote factorizations. No common differential normal is asserted to be a global separator by itself.

## 3. Closure, ordinary interior and concrete algebraic input

Strict Poisson approximants with q=r and p_N=w/[N(1-r)], together with the same positive baseline, prove actual-source closure. The moment law X=exp(-a)r^K for positive-parameter Poisson K has infinitely many distinct positive support points. A nonzero ordinary sparse polynomial cannot vanish on all of them. Hence no supporting ordinary moment functional has zero expectation, proving ordinary moment interior at every finite cap. This ordinary probability-law representation is not treated as a finite biological source.

For a concrete algebraic family choose the certified rational b=1-C_*/8, a=w=-log b, and

    m_lambda=b^(lambda+R_lambda(1/2)).

All powers are rational, so the input is exactly algebraic; no transcendental coordinate or logarithmic zero oracle is needed to specify it. The reviewed conservative certificate records an exact rational C_* with 433-bit numerator and 833-bit denominator. The elementary bound -log b<=(1-b)/b certifies 2(-log b)<C_*. Its six powers of b are 2,19/4,255/32,6143/512,278527/16384,24117247/1048576. Sparse rational-power encoding is sufficient; enormous expanded defining-polynomial coefficient arrays were not materialized.

## 4. Independent exact execution

The separately written head checker `g7/paired_normal_certificate_review.py` PASSED under Python 3.12.14 in approximately 0.07 seconds. It independently verified both sparse polynomial/positive-quotient identities; re-expanded the saved normalized near-one numerator in exact binomial arithmetic including endpoint p=0/1; checked its constant value and coefficient norm; reconstructed the second/third Taylor polynomial bounds; checked every rational probability/loss-budget inequality and the concrete target's total-loss bound; and verified the six rational powers.

Reviewed certificate SHA256: `9cca574e330b3732ef875616a6475b4d06bce5c6cc547fafc3ff0dbcfa6e306d`.
Independent checker SHA256: `7f4a165ca64a79c99f516f3fe986d777715293343307eae5fa52baa4a4fe02df`.
Its PASS receipt is `g7/paired-normal-head-review-results.json`. These are exact coefficient/budget checks, not sampled logarithm signs or an increasing source-size search. The all-factor conclusion still rests on the reviewed hand inequalities.

The newer compact certificate is NOW independently ACCEPTED too. Its SHA256 is `2a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118`. The separate checker `g7/compact_paired_normal_certificate_review.py`, original SHA256 `330caa40b9eb9362525f43ca585163b2f5b9fb5992b18acdc7ee758374bf7b86`, then final portable SHA256 `c29907922cd80dbce3dbfbc4ed4381ea73b2acc69f3dc470b547bc7252162483`, PASSED exact rational checks. The final portable replay independently reconstructs all 171/815 derivative numerator terms directly from the normal rows using Fraction polynomial arithmetic (rather than requiring the earlier private conservative certificate), then rechecks the tighter coefficient-Lipschitz positivity width, every root/Taylor/budget bound and the explicit `b=1-2^(-175)` total-loss certificate. Its C_* has 429-bit numerator and 602-bit denominator. The compact nested-square-root input encoding is exact: z_0=b, z_(i+1)>0 and z_(i+1)^2=z_i; m_lambda=b^(lambda+2)/z_(lambda-1). This supplies all six algebraic coordinates with at most twenty root steps, without expanding degree-million polynomials. The PASS receipt is `g7/compact-paired-normal-head-results.json`. The older conservative certificate remains correctly attributed as the first reviewed pin.

## 5. A finite algebraic NO test derived from the proof

The same proof gives a sound finite NO predicate on positive algebraic cap-seven signatures: require m_1>1-C_*/2, both exact normal equations, and failure of pure-baseline identities m_lambda=m_1^lambda. Here m_1 denotes the lambda=1 no-merger coordinate. Since C_*<=1/8, the first inequality implies -log m_1<C_*. Clear each rational normal's coefficient denominators and express its logarithmic zero equation as equality of two products of integer powers of positive m_lambda. These are finite algebraic tests. If a source existed, its total loss would be in the certified regime and the paired argument would force a baseline, contradicting the last condition.

This test is sound regardless of whether the input was separately established to lie in the actual closure. The Poisson family shows that it recognizes some genuinely nonattained closure inputs and ordinary-interior inputs, rather than only already-outside-closure points. It is a sufficient NO stratum, not a total recognizer for all algebraic inputs.

The same finite signed-monomial predicate applies with the newer compact C_* and exactly rejects its b=1-2^(-175) family. Require 0<m_lambda<1, the small first-coordinate-loss inequality, both normal equations and a nonbaseline signature. The general cap-eight/nine killing candidate, arbitrary input factor bound, independent-source realization and complete boundary classification remain open. No empirical separation, finite-DNA efficiency, whole G3 closure, historical priority or public release is inferred. Next work is a broader exact boundary classification or effective witness bound, with source/observation scope unchanged. Both compact certificate and finite NO-predicate encoding have passed this independent review; neither supplies a total recognizer.
