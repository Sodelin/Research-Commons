> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Rational-power preprocessing and the polylogarithm height condition

22 October 2026. Authored HAND deduction, self-audited, UNREVIEWED/UNCOMPILED.
No mathematical program, source producer, solver or proof assistant was run.
Historical novelty is unassessed. Original all-input G3 remains OPEN.

The candidate use is arithmetic: preserve a homogeneous polynomial equality
in actual logarithms while raising the supplied algebraic numbers to rational
powers. For the old degree-eight Phi, common q!=0 gives Phi(qL)=q^8 Phi(L).
This does not require a physical source power/root construction.

## Provider and precise delta from the prior screen

Use Kawashima, *Linear independence of periods related to polylogarithms*,
[arXiv2605.17756v1](https://arxiv.org/html/2605.17756v1), Section2, normalized
places/heights and equation(1), Theorem2.2 and Corollary2.3. These are the
already inspected primary results. The old G3 admission screen correctly
leaves V_v(alpha,beta)>0 unacquired and warns that roots change fields/heights.
It supplies no universal root or power normalization.

The added statement here is an explicit failure theorem for ALL nonzero
rational-power choices on prime-power logarithms, allowing ANY containing
number field, common denominator and matching Archimedean place. This is a
criterion-applicability result, not a zero test or a negative source verdict.
The separate physical integer-power/root-descent notes retain their own scope.

The closest retained admission is G3-PRIOR-SOLUTION-AUDIT-HISTORY-20261022-R4.md,
23137B/SHA256aeb691e42268b95fa22fb4996b3b6bc77a56d1271fbcc8adada4a65a95b09116,
and its current successor G3-PRIOR-SOLUTION-AUDIT.md. The relevant actual
admission passages and the primary definitions were read. A bounded search
of the own notes and selected Commons research/handoff Markdown found no
stronger supplied preprocessing result; that search is not absence/novelty
evidence. No old provider is rederived as a new result.

## 1. A bound independent of denominator choices

Use positive integers m,R and write

    M=(m+1)^R-1,
    C=M log2 + R(R+1)log(m+1)/2 + R + RM.

In the provider's notation put

    b=h_v(beta), a=h_v(alpha),
    rho=max_i |alpha_i/beta|_v,  0<rho<1.

Its exact height quantity is

    V=(M+1)b-a-M[h(beta)+mean_i h(alpha_i)+h(alpha)]-C.

All global heights are nonnegative, h(beta)>=b and h(alpha)>=a. Hence

    V <= b-(M+1)a-C <= b-a-C <= -log(rho)-C.          (1)

For the last inequality let t=log|beta|_v and u=log(rho)<0. The local-height
definitions give b=max(0,t) and a=max(0,t+u), so b-a<=-u. This also handles
|beta|_v<=1; no extra magnitude assumption was inserted.

Thus representing the same ratios by another common denominator or larger
field cannot evade the necessary upper bound (1).

## 2. Normalized local degree for a rational prime power

Let p>=2 be a rational prime, q=A/B!=0 in lowest terms, B>=1, and let the
chosen Archimedean embedding identify t=p^q with its POSITIVE real value.
Suppose t belongs to a number field K of degree d. Put kappa=d_v/d.

Then

    kappa <= 1/B.                                   (2)

Indeed Bezout gives integers u,w with uA+wB=1, so t^u p^w=p^(1/B).
Consequently Q(t)=Q(p^(1/B)), whose degree is B by Eisenstein for X^B-p.
At a real place d_v=1 and d>=B. At a complex place the chosen embedded K
contains this real degree-B field but is not contained in R. Its extension
over that field has degree at least two, so d>=2B and d_v=2 gives (2) again.
This covers additional algebraic parameters and nonreal denominator choices.

## 3. Real closeness is offset by (2)

For every integer B>=1,

    1-2^(-1/B) >= 2^(-B).                           (3)

To prove this, 2^B>=2B and Bernoulli give
(1-2^(-B))^B>=1-B*2^(-B)>=1/2. Take the positive B-th root.

If A<0, 0<t<=2^(-1/B), so |1-t|>=2^(-B) by (3).
If A>0, t>=2^(1/B)>=1/(1-2^(-B)), hence again |1-t|>=2^(-B).

For any admissible ratio z=1-t with |z|<1, (2) therefore implies

    -log|z|_v = -kappa log|1-t| <= kappa B log2 <= log2.       (4)

When |z|>=1 the required series/convergence inequality already fails.

## 4. Failure theorem for the exact log interface

Suppose even ONE of the supplied log arguments has the form t=p^q above,
and it is represented at the matching place as

    alpha_j/beta = 1-t,
    Li_1(alpha_j/beta) = -log(t).

Keep every prerequisite of the provider. Then rho>=|1-t|_v; (1) and (4)
give

    V_v(alpha,beta) <= log2-C < 0.                   (5)

The strict last inequality holds for ALL positive m,R, since M>=1 and all
the other terms in C are positive. Thus Theorem2.2/Corollary2.3 cannot be
admitted at this real-log use-site. This conclusion allows arbitrary
common-denominator scaling, additional containing number fields and arbitrary
nonzero rational powers; these choices do not supply V>0.

In particular, if B_i=p_i^(q_i) with q_i nonzero rational and p_i prime,
then B_i^s remains of that form for every nonzero rational s. Fractional
powers can make the real arguments close to one, but the associated degree
must be included in the normalized place. Treating that degree as fixed is
the erroneous step this theorem prevents. Consistent individual rational
rescalings of polynomial variables have the same criterion obstruction.

## 5. This occurs on a nonempty full-promised rank-five G3 domain

Use the ORIGINAL full promise, lambda in {3,6,10,15,21},

    V_lambda(r)=lambda-sum_(h=0)^(lambda-1)r^h,
    ell=log B in cone{V(r):r in J_6}, ell!=0,
    J_6=[1/6,5/6].

There are effectively selectable distinct rational r_1,...,r_5 in J_6
whose column matrix A=(V(r_1),...,V(r_5)) is invertible. The five polynomial
coordinates have distinct degrees and nonzero leading terms, hence are
linearly independent on the interval. Their value vectors therefore span
R^5; density gives a rational selection. Enumerating rational nodes and
testing the rational determinant terminates.

Put ell*=A(1,1,1,1,1), an interior point of this simplicial cone. Fix distinct
primes (2,3,5,7,11). Choose positive rationals q_i so that

    ell_i=q_i log(p_i)

is sufficiently close to ell_i* that every component of A^(-1)ell is positive.
This can be done effectively by rational approximation and certified strict
log interval bounds. Openness proves termination; no logarithmic equality
decision is used. Let B_i=p_i^(q_i), with their usual positive algebraic codes.

These B_i satisfy the FULL five-coordinate promise. Their multiplicative
rank is five: clear the rational q_i denominators in any integer product
relation and use unique factorization of distinct primes. Nonetheless (5)
precludes the proposed height admission after every nonzero common rational
power, for any denominator and any matching Archimedean field/place.

This is an effective existence construction, not an executed tuple or new
original source experiment. It shows the failure is not confined to the
already decided rank-one subcase. The inherited source-faithful promise
reduction remains unchanged; no extra observation is added.

## 6. Limits and next original obligation

This excludes this rational-power/denominator acquisition strategy for the
specified primary criterion. It does not exclude other arithmetic theorems,
other legitimate representations, or all preprocessing. V<=0 has no source
NO meaning. No algebraic/transcendental-residue pure input is exhibited and
no Schanuel equivalence, undecidability result or full G3 endpoint is claimed.

The necessary actual Phi zero test and the all-input source/whole-fibre
termination obligation remain open. The constructive positive search and
the already proved source/certificate components retain their scopes.
