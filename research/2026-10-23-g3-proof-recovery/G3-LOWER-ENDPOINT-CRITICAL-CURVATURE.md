> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Lower-endpoint curvature of paired-critical COMMON cells

22 October 2026 UTC. Existing G3 source owner. NEW RELATIVE HAND CANDIDATE;
self-audited, UNREVIEWED and UNCOMPILED. No mathematical program, solver,
old producer, source compiler, model/native job or peer task was run.

This is a supporting structural result, not a replacement for G3's total
all-input exact recognition/terminating-NO goal. It supplies no general
one-witness H, no exact logarithmic-zero test and no INDEPENDENT/BOTH theorem.

## 1. Exact claim, inherited suppliers and prior comparison

Let Lambda=(1,3,6,10,15,21). For 0<r<1 use the SAME uniquely normalized normal

    sum c_lambda=1, sum lambda*c_lambda=0,
    F_r(r)=F'_r(r)=F_r(r^2)=F'_r(r^2)=0,
    F_r(x)=sum c_lambda(r)*(1-x^lambda).

Set

    H_lambda(p,q)=-log(1-p+p*q^lambda),
    L_r(p,q)=sum c_lambda(r)*H_lambda(p,q).

Critical means BOTH L_p=L_q=0, with r and c(r) FIXED and 0<p,q<1.

**Relative hand claim.** Using the lower-endpoint supplier below, there is
a rational R>0 such that EVERY real strict critical cell with 0<r<R obeys

    L_pp(r,p,q)<0.                                      (1)

Thus none of those critical Hessians is positive semidefinite. The claim is
uniform over all real p,q; no algebraic-parameter premise, finite grid,
nondegenerate-critical-point promise or lower bound on 1-p is added.

All immutable source paths below are at Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6.

* Closest original provider: research/2026-10-02-codex-g3-parametric-critical-0330z/
  ALL-RESIDUE-CRITICAL-FINITENESS.md. Its complete body was read. It supplies
  the rational normal and finite critical set, not Hessian signs.
* Closest endpoint increment: handoffs/2026-10-16-codex-g3-lower-endpoint-hand-increment-003/
  LOWER-ENDPOINT-CRITICAL-LOSS-05.md. Its complete body was read. Its HAND
  theorem says that some R0,eta>0 give p(1-q)>=eta on every critical cell
  with r<R0. This is REUSED, not rederived or silently promoted to independent
  acceptance. The present claim is RELATIVE to that unreviewed supplier.
  Its exact coefficient asymptotics, double-root estimates and uniform
  q-near-one exclusion are also reused below.
* Later full query: research/2026-10-16-g3-critical-psd-reduction-1950z/
  REDUCTION.md. Its complete body was read. It leaves the all-r predicate
  open and mentions L_pp<0 as an unproved sufficient statement.
* Later endpoint successor: handoffs/2026-10-16-codex-g3-upper-endpoint-hand-increment-004/
  UPPER-ENDPOINT-CRITICAL-CLASSIFICATION-06.md. The complete body was read,
  including its unbalanced and probability-boundary sections. Its weak
  r->1 saddle/complementary loss floor is REUSED at HAND scope. It does not
  classify every strong cell near r=0 or solve all-r Q13.

The new implication compared with those bodies is the SIGN on all sufficiently
small-r critical cells, including the strong p->1,q->0 corner. Their existing
count finiteness, endpoint loss bounds and upper weak saddle are not new here.
This is a bounded predecessor/successor comparison, not a historical novelty
or whole-corpus absence claim.

Exact source identities verified by both raw SHA256 and Git blob, without
executing any retained producer:

| Source key | Bytes | SHA256 | Git blob |
| --- | --- | --- | --- |
| normal | 13664 | f108eb49332179e4ff34f791c36eee28d33adcf4ce24db9094cc029c567ebc95 | 8faa5ae863ae4518414582dd5d3f714d9ca3896b |
| lower05 | 14737 | 1e4b8624c42bdaf12abd9a7ecf364a619e75010f9b9e9cf637e36059a99ee4a8 | 3cf857ae6250042fbb54857c7626aa1bd6754107 |
| reduction | 9147 | 34918d1bb4e12854dd5b18539585dda3341e91de16afa872256c279156adeecb | e2eec5a41528f11759330929faf6fa80fe51eaf7 |
| upper06 | 22030 | 9320dbc6129184c0137ae6bb77c971507dcfaa2511ffed1aabecd87cc69c3154 | 357362b9fc574960dde500c7ebc78ecb54641403 |

## 2. Exact critical equations in odds coordinates

Put z=p/(1-p), u_lambda=z*q^lambda/(1+z*q^lambda), and A=log z. Exactly,

    L=log(1+z)-sum c_lambda*log(1+z*q^lambda),
    L_z=1/(1+z)-sum c_lambda*q^lambda/(1+z*q^lambda).

At a critical cell the two equations are

    sum c_lambda*u_lambda=p,
    sum lambda*c_lambda*u_lambda=0.                    (2)

The second follows by multiplying L_q by -q. At such a cell,

    L_AA=-p^2+sum c_lambda*u_lambda^2.                  (3)

Indeed L_A=p-sum c*u and d u/dA=u(1-u). Also

    L_AA=[p(1-p)]^2*L_pp

when L_p=0. Thus a negative quantity in (3) proves (1), with no change in
the fixed-normal differentiation convention.

Another exact form of (2), with f_lambda=1-p+p*q^lambda, is

    sum c_lambda/f_lambda=1,
    sum lambda*c_lambda/f_lambda=0.                   (4)

For the second identity use sum lambda*c_lambda=0. No denominator in these
identities vanishes in the strict domain.

## 3. Inherited small-r data and the contradiction setup

Write nu=(2,6,9,13,13,13) in Lambda order. The exact scaled linear system in
note05 gives

    c_lambda(r)=k_lambda*r^(-nu_lambda)*(1+o(1)),
    k=(3/2,-1/2,7/8,-3/8,11/16,-5/16).               (5)

The coefficients are rational functions and the scaled coefficients are
analytic at r=0. The following limits, including derivatives on compact
positive t or v intervals, are inherited from that exact system:

    F_r(r^2*t) -> P2(t)=(t-1)^2*(t+2)/2,
    r^3*F_r(r*v) -> P1(v)=v^3*(4-7v^3+3v^7)/8.

Both displayed positive-variable functions vanish only at 1. The roots at
r^2 and r of the exact F_r are DOUBLE for every r. In particular, near v=1,

    F_r(r*v)=r^-3*O((v-1)^2),
    F'_r(r*v)=r^-4*(v-1)*(21/2+o(1)).                 (6)

The paired-normal Descartes argument also gives F_r(x)>=0 on (0,1).
This is an exact sign, not an unsigned-coefficient estimate.

If (1) fails arbitrarily close to r=0, the rational critical equations and
the rational inequality L_pp>=0 give a semialgebraic curve of counterexamples
with r->0. Curve selection and Puiseux parametrization may therefore be used.
Along this curve write limits p0,q0 in [0,1]. Note05 gives p(1-q)>=eta.
Consequently p0>0 and q0<1. Its separately established q-near-one exclusion
also applies. We now exhaust q0>0 and q0=0.

All curve-selection arguments concern this auxiliary derivative predicate,
not hidden parameter extraction from an original algebraic input.

## 4. A positive limiting q forces negative p curvature

Suppose q0 is in (0,1). Multiply L and its p derivatives by r^13. The limit is

    J(p,q)=(-6*H_10+11*H_15-5*H_21)/16.              (7)

If p->1, the limit of r^13 L_p is

    [-6*q0^-10+11*q0^-15-5*q0^-21]/16 < 0,

by strict convexity of x->q0^-x and 15=(6*10+5*21)/11. It cannot be critical.
The inherited loss floor excludes p->0. Hence p0 is strict.

For fixed strict q, J_p is a positive denominator times a LINEAR numerator
in p: the degree-two coefficient cancels because -6+11-5=0. Its numerator
is positive at p=0 and negative at p=1, again by strict convexity of
x->q^x and x->q^-x. The linear numerator therefore has negative slope.
At every zero of J_p, J_pp<0. Criticality of the actual curve passes to
J_p(p0,q0)=0, so r^13 L_pp tends to a strictly negative value. This
contradicts L_pp>=0.

This uses a three-term limiting identity; no assertion that signed c is
a probability measure or that the full six-term function is concave is made.

## 5. A vanishing q with p bounded away from both endpoints is impossible

Suppose q->0 and p->p0 in (0,1), so z->z0 in (0,infinity). Write
q=Q*r^a*(1+o(1)), Q,a>0. Note05's coefficient table has Newton orders

    min(0,a-2,3a-6,6a-9,10a-13,15a-13,21a-13).

For 0<a<2, the first critical equation can survive only at a=1,Q=1;
the a=2 case must be retained separately. Higher q powers in the rational
denominators have strictly higher order than the divergent leading term.
For a>2, L_z->1/(1+z0)>0.

At a=2 the q equation, after multiplying by r^2, forces P2'(Q)=0,
hence Q=1. The z equation then tends to -z0/(1+z0), which is nonzero.

At a=1 write q=r(1+h), h->0. The exact double roots give

    L_q/z=F'_r(q)-z*q*F'_r(q^2)+O(1),
    F'_r(q)=r^-4*h*(21/2+o(1)),
    q*F'_r(q^2)=O(r^-1*|h|).

The remainder is uniformly O(1) for bounded positive z; this follows by
summing the six absolute terms of order q^(3lambda-1). Thus h=O(r^4).
Using the exact roots again,

    L_z -> 1/(1+z0)-1+z0 = z0^2/(1+z0)>0.

There is no critical curve in this regime. A p0=0 limit was already
excluded by the inherited loss floor.

## 6. The strong corner: necessary exponent balances

It remains to treat p->1 and q->0. Along the selected semialgebraic curve,

    z=Z*r^-b*(1+o(1)), q=Q*r^a*(1+o(1)),
    Z,Q,a,b>0.                                         (8)

First, (4) forces b<10a. To see this, the orders of c_lambda/f_lambda are

    nu_lambda+min(b,a*lambda).

For 10a<=b<15a the largest terms are the upper three or the upper two.
At b=10a their mass coefficient is

    (6Z/16)*(1-1/(1+Z*Q^10))>0;

for 10a<b<15a it is 6Z/16>0. At b=15a only the 15 and 21 terms are
largest; two distinct nonzero terms cannot cancel both mass and lambda
moment in (4). For 15a<b and at or beyond 21a the 21 term is uniquely
largest. Thus every b>=10a is excluded. Lower coefficients have strictly
smaller orders in all these comparisons.

For b<10a use (2) instead. The orders of c_lambda*u_lambda are

    E_lambda=nu_lambda-max(a*lambda-b,0).               (9)

The 15 and 21 entries are strictly below the 10 entry, so only
lambda=1,3,6,10 can maximize (9).

A simultaneous leading cancellation in (2) needs at least THREE maximal
terms whenever the maximum order is positive. Two distinct nonzero terms
cannot cancel both their mass and lambda moment. The remaining possibility
of a nonpositive maximum gives no critical curve: it requires b<a and a>2,
where the lambda=1 term is uniquely largest and cannot satisfy the zero
lambda moment.

Here is the exhaustive finite comparison of the four affine orders. Boundary
equalities may occur in both adjacent rows; that harmless overlap is retained.

| Range | Three maximal entries can occur only as |
| --- | --- |
| 0<b<=a | a=1, entries 3,6,10, with 0<b<=1 |
| a<=b<=3a | a=1, entries 3,6,10, with 1<=b<=3 |
| 3a<=b<=6a | a=1,b=3, entries 3,6,10 |
| 6a<=b<10a | none |

For example, when the last three entries are unsaturated their mutual
equalities force a=1. If the 1 entry is saturated its order is 2, whereas
their common order at a=1 is 3+b>2. If the 3 entry is saturated, equality
of the 6 and 10 entries still forces a=1, then equality with the 3 entry
forces b=3. In the last range at least two saturated entries of any triple
have unequal orders. In the first range the 1--3 edge has slope 2 and
the 3--6--10 edges have slope 1, so no triple containing 1 is possible.

Therefore a=1 and 0<b<=3. If b<3, the two leading equations, after dividing
by the common nonzero factor, are

    -4Q^3+7Q^6-3Q^10=0,
    -12Q^3+42Q^6-30Q^10=0.

Subtracting three times the first gives Q^4=1, hence Q=1.
If b=3 the first terms become -4Q^3/(1+ZQ^3) and
-12Q^3/(1+ZQ^3), respectively. The same subtraction forces Q=1, but
the first equation then gives 4-4/(1+Z)=0, impossible for Z>0.

Every possible strong-corner critical curve consequently has

    q/r ->1,  z=Z*r^-b*(1+o(1)), 0<b<3.               (10)

The order analysis uses BOTH exact equations. It does not set the leading
mass to zero when its order is nonpositive, or infer a critical point from
a Newton diagram.

## 7. Finish all corner subregimes

### 7.1 0<b<1 is not critical

Here z*q->0. Expanding one exact denominator, with a finite six-term
absolute remainder, gives

    L_z=1/(1+z)-1+F_r(q)+z*(1-F_r(q^2))
           +O(z^2*sum |c_lambda|*q^(3lambda)).

For q/r->1, the sum in the remainder is O(r), F_r(q^2)->0 and F_r(q)>=0.
Since z*r->0,

    L_z >= z*(1-o(1))-1 >0.

This excludes criticality. No estimate of how quickly q/r approaches 1
is needed here.

### 7.2 b=1 forces Z=2 and negative curvature

Put h=q/r-1. From the exact q equation,

    0=L_q/z=F'_r(q)
             +z*sum lambda*c_lambda*q^(2lambda-1)/(1+z*q^lambda).

The second term is O(r^-2). Equation (6) thus gives h=O(r^2), and
F_r(q)=O(r). An exact rearrangement of the first equation is

    L_z=1/(1+z)-1+F_r(q)
             +z*sum c_lambda*q^(2lambda)/(1+z*q^lambda).

Multiplying by r and taking the limit yields

    0=Z*(3/[2(1+Z)]-1/2).

Thus Z=2. In (3), multiplication by r^2 now gives

    r^2*L_AA -> (3/2)*(Z/(1+Z))^2-Z^2/2
               = -4/3 <0.

Only the 1 and 3 entries survive this last limit; every other entry has
strictly higher order. Therefore L_pp<0 along the curve.

### 7.3 1<b<3 has a single negative leading square term

Now u_1->1 and u_3~Z*r^(3-b). In (3),

    r^(2b)*L_AA -> -Z^2/2 <0.

Indeed the positive 1 entry contributes O(r^(2b-2))->0, the 3 entry
gives the displayed negative limit, and entries 6,10,15,21 are smaller
by positive powers, beginning with r^3 and r^7. Again L_pp<0.

Sections 4--7 exhaust a selected counterexample curve. None can have
L_pp>=0, proving the relative claim (1).

## 8. Effective and original-source scope

Because c(r) is rational and its denominator is nonzero on (0,1), the
predicate "strict critical and L_pp>=0" is a rational semialgebraic
predicate after retaining denominators or clearing by positive squares.
Enumerating dyadic R and deciding its universal emptiness by RCF would
therefore terminate, IF this relative hand proof and its inherited note05
supplier are correct. No such elimination, search or certificate was run.
The argument supplies no numerical R and does not relabel a prepared query
as an executed UNSAT result.

The accepted negative-inertia source theorem could then bound retained
multiplicity by three on this LOWER-ENDPOINT branch, but only with its
actual positive drift/residue, zero killing, rank-five, untied COMMON
variation and nonattainment hypotheses. That count sharpening is optional:
the retained all-real fixed-input critical count is already solved.
Neither bound decides the at-most-one zero-head logarithmic equality.

The middle-r global Q13 predicate, possible strong upper-endpoint cells,
the full original shared-menu/caller problem and all-input H/complete NO
remain OPEN. No new original observation, independent row fit, physical
inverse, natural parameter endpoint or refreshed COMMON bit is admitted.

