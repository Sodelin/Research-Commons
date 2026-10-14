# Terminal endpoint perturbations through a strict visible completed chain

Contributor/reviewer: Codex delegated laplace_recovery researcher,
14 October 2026. **Hand-derived component audit.** This checks the terminal
endpoint normalization, the extension of completed differential peeling
to its signed tail, and the final quartet sign. It does not establish
the original local theorem's parameter-entry or COMMON-budget premises.
No computation, formal verification or general G4 closure is claimed.

Reuse the accepted completed atomic supplier
[COMPLETED-ATOMIC-DERIVATIVE-TRANSFER.md](COMPLETED-ATOMIC-DERIVATIVE-TRANSFER.md),
SHA256 `a7d38af39967ed733a08f0aa24d63e9ef1193145bbb347d251bfeb41f9522a00`,
and its independent Sol review. Its finite deduplicated marker lists,
disjoint test/comparison reservoirs and order of localization limits are
retained; no infinite counting statistic is substituted. The argument
below is single-taxon: positive FULL arms are genuine positive serial
populations after pruning other taxa. No mixed A/B exclusive-pad premise
is inferred from their positivity.

## 1. Uniform endpoint normalization before arbitrary opaque completion

Let B(t,p) be an equal-arm cell, p=g(1-g), and E_t its ordinary endpoint
value. For m current roots at g=0, let K_i(t) be ordinary evolution for
time t of all roots except root i, with i isolated. Differentiating the
finite routing expansion gives the exact forest-operator identity

    partial_p B(t,0)=sum_(i=1)^m [K_i(t)-E_t].       (1)

Here dp/dg=1 at g=0. The other endpoint gives the same identity by arm
exchange. Existing subtrees on the roots are opaque throughout.

Couple K_i(t) and E_t until the isolated root would first merge with
another current root. Before that time its merger hazard is at most
m-1. Thus their row l1 difference is at most 2(m-1)t. It follows that

    ||partial_p B(t,0)||_1 <= 2m(m-1)t,
    ||V_t||_1 <= 2m(m-1),
    V_t=partial_p B(t,0)/(exp(t)-1), t>0.             (2)

At t=0 the continuous extension is V_0=-2Q. Its row l1 norm is likewise
2m(m-1). All estimates survive stochastic prefix/suffix composition.
In particular the normalized endpoint insertion has polynomial, uniform
cap norm even when its duration tends to zero.

For completeness, the corresponding nonlinear difference has the same
useful bound. Couple ordinary evolution with the two routed populations
until the first merger between initially opposite routing groups. If
their initial sizes are k,m-k, this hazard is at most k(m-k), with
expectation m(m-1)p. Hence

    ||B(t,p)-E_t||_1 <= 2m(m-1)pt,
    ||[B(t,p)-E_t]/[p(exp(t)-1)]||_1<=2m(m-1).       (3)

The quotient has the usual continuous limits V_t as p tends to zero,
and -2Q as t tends to zero, at each fixed cap. The fixed-cap analyticity
supplier justifies these limits; (2)--(3) additionally control them under
the finite-root expectations needed below.

## 2. The signed terminal-tail extension of completed differential peeling

Consider a finite strict visible single-taxon chain ending in Q, with
its fixed unequal palette and equal-arm p coordinates as in the inherited
differential normal form. Ordinary time after its last visible cell is
absorbed into Q. Suppose its normalized completed-row identity has the
form

    D K[v] + P R = 0                                (4)

at every finite input, where P is the visible prefix and R is a
projective, exchangeable, opaque-graft-compatible signed completed tail.
Assume R has total mass zero and cap norm at most C(1+m)^d for fixed d.
The endpoint insertion integrals supplied by (2) have d=2, including
any finite ordinary prefixes within the terminal tail.

The inherited completed differential peeling remains valid with this
additional R. In particular it gives its usual biased/unequal zero
directions and equal-fair null directions; after those are removed, it
also gives R=0. Here are the extra justification steps.

After either arm of the first strict visible cell has run for a fixed
positive time, the total remaining root count has moments of every
order, uniformly in a compact strict neighborhood. Conditional on this
finite count and the stored younger hierarchy, the signed tail acts on
finitely many opaque roots with total variation bounded by C(1+m)^d.
Integrating constructs a finite signed measure on the ENTIRE completed
hierarchy. It is an order-zero perturbation in the first coin, not an
additional derivative of a cohort mass location. Stochastic factors
between this cell and the terminal tail can only decrease root count
and do not enlarge the bound.

Consequently the accepted finite-marker/Bernstein derivative transfer
and highest-atomic-derivative isolation apply to (4) unchanged. Keep
the finite marker list fixed while taking the finite-row limit and
localizing, exactly as in the pinned supplier. This removes the first
biased coin and preceding-gap changes, or leaves precisely the familiar
fair null relation. At a fair equal cell subtract its exact full-source
null direction before proceeding. This uses the single-taxon arm
symmetry, not an unproved symmetry of a mixed two-colour core.

Once the first coin has been fixed in that way, the remaining derivative
is a finite signed hierarchy measure. Its finite cylinder values vanish,
so cylinder uniqueness makes it zero. The cohort extractor at this
fixed first coin is one fixed measurable map; pushing this zero signed
measure through it is legitimate. No parameter-dependent extractor is
differentiated.

The completed crossed-cohort formulas remain independent of the signed
upper perturbation. An exchangeable completed upper law has each of
the three specified rooted triples with probability 1/3. Any
exchangeable mass-zero signed perturbation therefore vanishes at input
counts one, two and three. The crossed (2,1) cohort probability is x/3,
so its zero derivative fixes the oriented first-arm survival. At fair
orientation the crossed triple gives x+y. The mixed balanced/comb
combination gives xy because for every exchangeable four-root completed
law

    3 q_bal + 12 q_comb = 1,

and for its mass-zero perturbation the right side differentiates to
zero. Thus the completed first-arm recovery used in the strict normal
form is still valid with R present. On the fixed-palette chart this
eliminates the remaining baseline change (after the fair null direction
has been subtracted).

The extracted first-cohort marginal is E_x U, or its known unbiased
two-arm average at fairness. With the first arms fixed to first order,
the positive triangular completed-row cancellation gives D U plus its
same signed terminal perturbation equal to zero. Induct down the finite
visible list. At its end ordinary-time derivatives applied to Q vanish;
the residual identity is R=0. If the visible list was empty, (4) already
says R=0 and no infinite-hierarchy transfer is needed.

This proves only the extension at a normalized differential identity
already supplied on one shared source sequence. Establishing visible
parameter displacement O(W), retaining the physical fair cone, and
deriving that identity from the original COMMON fibre remain premises
of the proposed local theorem, not conclusions of this component.

## 3. Exact terminal balanced-quartet sign

Let x=exp(-t). Under Q the probability of one specified labelled balanced
quartet is 1/9; the total probability of the three balanced topologies is
1/3. At an endpoint, condition on exactly one specified rare leaf.
The other three roots evolve ordinarily for time t while the rare root
is isolated. For a specified balanced topology, either no merger occurs
among those three, or exactly the required pair merges there. The
respective contributions are

    x^3/9,
    [(x-x^3)/2]/3.

The second formula uses the probability (x-x^3)/2 of one specified
pair merger and no further merger by time t among three roots.
Consequently the conditional specified-balanced probability is
x/6-x^3/18. Summing the four first-rare-leaf derivatives and subtracting
the loss of the all-main assignment gives

    partial_p Pr(specified balanced | B(t,p)Q) at p=0
       = -(2/9)(1-x)^2(x+2).

For the TOTAL balanced-quartet event, therefore,

    partial_p Pr(balanced | B(t,p)Q) at p=0
       = -(2/3)(1-x)^2(x+2),

    Pr(balanced | V_t Q)
       = -(2/3)x(1-x)(x+2) < 0,   t>0.              (5)

The normalized value tends to zero at t=0, consistently with
V_0 Q=-2Q Q=0, where the first Q in the latter expression denotes the
ordinary generator and the final Q denotes infinite completion.

If an ordinary interval of length r precedes the terminal insertion,
its balanced-quartet value is (5) times exp(-6r). Indeed the perturbation
vanishes at input counts <=3 by exchangeability and zero total mass.
In the triangular ordinary-prefix expansion only the no-merger
four-root term remains; its probability is exp(-lambda_4 r).

Thus, for a positive normalized terminal-insertion measure eta on
finite r and t in [0,H],

    R = integral E_r V_t Q d eta,

the identity R=0 implies eta(t>0)=0 by the balanced quartet alone.
Every integrand is nonpositive and is strictly negative for finite r
and t>0. A finite exposure bound on r is sufficient and is available
only when the original anchor supplier actually covers that passage;
an infinite ordinary prefix could hide the perturbation and is not
silently permitted here.

## 4. Audit verdict and remaining composition duties

The endpoint normalization, signed-tail differential extension and
terminal quartet exclusion are correct under the stated premises. They
do not rely on the failed exponential rare-route claim for a mixed
final core: the quartet is a legal single-taxon completed marginal.

To use them for original local exclusion, the lead must still supply
one normalized identity with all private insertions already reduced to
duration-zero generators, the strict visible O(W) parameter chart, the
actual COMMON ratio budget and its sign, and finite relevant terminal
exposures on that SAME sequence. This component changes no physical
tuple and grants no cohort, forest-root or latent-core observation.
