# A sufficient gauge criterion that does not reconstruct the meeting core

Contributor: Codex whole-source lane, 13 October 2026, continuation 2110z.
**Hand-derived conditional lemma and exact remaining source obligation.**
This is a short extension of the accepted private pole-zero argument, not
a new analytic uniqueness theorem or original-source G4 closure. No Lean
verification or independent review is claimed.

The inherited [legal normalized meeting invariant](../continuation-1900z/ANCHOR-AND-MEETING-INVARIANT.md)
already forces the entire table R with finitely many legal observations.
For an anchor pair the remaining scalar equation has the actual form

    D'_A(n) v'_n = D_A(n) v_n,

where v_n and v'_n are reference-comb probabilities of the two bounded
meeting trees. No separate private kernel is observed. One actual source
and tuple determine all arities.

## Conditional finite-persistence lemma

Let U_i be the equal-cell functions of the accepted
[Carlson bridge](../../chronology/continuation-1837z/CARLSON-CONTINUATION-BRIDGE.md),
with strict t_i>0 and

    sum_i t_i < infinity,  sum_i h_i^2 < infinity.

Put P(z)=product_i U(z;t_i,h_i). Suppose that the WHOLE-SOURCE scalar
identity, after justified explicit quadratic/linear normalizations, gives

    G(m) P(m)=F(m)                 for every integer m>=1.       (1)

Assume F and G have the following properties:

1. They are holomorphic on Re z>0. For some a>0 and tau<pi,
   |F(z)|+|G(z)|<=C exp(tau |z|) on Re z>=a.
2. They extend holomorphically to D=C minus the negative half-integers,
   and extend meromorphically to neighborhoods of -1/2 and -3/2.
3. F is not identically zero.

Then the strict equal-cell family is finite. In particular F and G need
not be products of physical cell diagonals, need not be positive away
from the integer observations, and need not identify either meeting core.

**Proof.** The accepted Carlson bridge gives P zero exponential type in
the right half-plane. Choose epsilon>0 with tau+epsilon<pi. The function
GP-F, shifted by a sufficiently large integer, satisfies Carlson's
right-half-plane growth condition and vanishes at all nonnegative
integers. Thus GP=F on that half-plane. Normal convergence of P on D,
from the accepted [off-pole estimate](../../chronology/continuation-1837z/MEROMORPHIC-FINITE-PERSISTENCE.md),
extends the identity throughout connected D.

If infinitely many strict cells persist, the accepted Rouché argument
supplies infinitely many distinct zeros z_j of P converging to one
p in {-1/2,-3/2}. The zeros lie in D. Since G is holomorphic there,
F(z_j)=0. But F is meromorphic of finite order at p. Multiplying by a
fixed power of z-p makes it holomorphic near p, so these accumulating
zeros force F identically zero. This contradicts assumption 3. QED.

This is an explicitly conditional application of the existing analytic
proof. The genuinely weaker sufficient objective is controlled
continuation of the scalar reference factors; one does not need full
meeting-parameter recovery or a physical factorization of every gauge.

## What remains missing in the original-source application

No theorem here establishes assumptions 1--2 for the genuine mixed
four-tip reference factors, their cross-shape gauges, or their compactified
boundary values. Nor does it derive the displayed summable bias budget or
the required quadratic/linear cancellation from the uncalibrated
whole-source equation. These remain source-transfer obligations.

A finite-dimensional parameter tuple, polynomial dependence at EACH
integer arity, or finite forcing of R is insufficient to establish any
of those analytic hypotheses. The [four-tip handoff](../continuation-1900z/FOUR-TIP-GAUGE-HANDOFF.md)
already records the exact route-count mixture and its noninvertible
columns. That failed inversion is not repaired by this lemma.

Moreover the [strict retained-core family](RETAINED-CORE-COMMON-GAUGE.md)
shows that one complete anchor table R plus the whole COMMON law does
not force rational arm balance or even a discrete finite unequal gauge.
Its gauges ARE quotients of one finite physical cell diagonal, so it is
consistent with the physical-gauge conjecture. It directly explains why
the equal-cell analytic proof does not automatically apply after merely
forcing the normalized table.

The lead additionally flagged a compactification boundary: if an unequal
cell tends to a=0,
b>0, then

    d_n = g^n sum_(r=0)^n binom(n,r) ((1-g)/g)^r exp(-b binom(r,2)).

The later [independent zero-arm endpoint audit](../../chronology/continuation-2110z/ZERO-ARM-ENDPOINT-SOL-AUDIT.md)
now proves that the residual after removing g^n extends to an entire
function of zero exponential type. Thus FINITELY MANY such endpoint cell
factors are covered by that analytic extension; the endpoint alone is no
longer an unresolved obstacle. This does not establish the corresponding
continuation for genuine meeting-reference factors. Strict actual rivals
can still have such a limiting body, and no boundary source is asserted to
be an admitted rival.

The next substantive task is a common growth/continuation theorem for
the actual bounded meeting reference-comb factors, including unequal
and compactified boundary cases, coupled to a whole-source resource
identity. The present lemma isolates exactly how such a theorem would
discharge infinite equal-cell persistence without reconstructing cores.
It supplies neither a general finite certificate nor fixed-target exact
inequivalent rivals after every finite legal prefix.
