# Original anchor combs exclude positive-duration weak insertions

Contributor/publisher: Codex lead G4 researcher, 14 October 2026.
**Hand-derived composition; independent review pending.** This assumes the
new one-sided observable-secant bound at its stated source interface and
reuses the accepted private insertion formula, original anchor factorization
and shared observable-secant reduction. It is not general finite forcing.

## Statement

Consider the original natural BOTH fitting sequence after the accepted
shared finite-persistence and zero-clock-loss reductions. Let a and nu be
its normalized finite-body observable secant and weak-cell insertion
probability measure from
[the secant reduction](FINITE-OBSERVABLE-SECANT-REDUCTION.md) and its
[compact-slot review](FINITE-OBSERVABLE-SECANT-SOL-REVIEW.md). In particular

    G_o(a)+I_o(nu)=0

for every legal original observation o, using one source sequence and tuple.
Assume the [one-sided reference-comb theorem](ONE-SIDED-OBSERVABLE-SECANT-BOUND.md).
Then nu is supported entirely at cell duration t=0. This rules out every
positive-duration endpoint-coin insertion, not just a fixed finite list.
The remaining zero-duration measure still has total mass one and is not
excluded by this theorem.

## 1. Actual reference probabilities expose each private slot

For an anchor A,B, let p_n be the actual specified completed comb on n A
copies and one B copy. Obtain it as a legal marginal with the other original
taxa sampled and then pruned. A weak slot on A's ancestry is a proper private
slot whose child side excludes B. A monochromatic A merger inside it would
leave a nontrivial A-only clade, which this comb does not have. Thus the
slot contributes exactly its no-A-merger diagonal, multiplicatively, to
the actual comb probability. This is the inherited original anchor
factorization; the continuation retains the actual changing meeting core.

A slot on B's private ancestry carries only one selected root and has no
effect. Other slots disappear by selected-lineage projectivity. No slot
contains both A and B: its proper descendant clade is common to every
supported displayed profile, whereas anchors lie in different maximal
proper common clades. This same argument works at the fixed boundary body
by its retained slot bookkeeping and continuity of the source kernels.

Each original private slot has at least one descendant taxon A; the fixed
anchor selected for that A is outside its common clade. Hence the finite
chosen anchor list covers every possible weak slot. The list and subsequence
are fixed before varying n.

## 2. Exact normalized insertion formula

Write lambda_n=binom(n,2). For an equal private cell,

    d_n(t,g)=sum_(k=0)^n binom(n,k) g^k(1-g)^(n-k)
                                  exp[-t(lambda_k+lambda_(n-k))].

At the endpoint g=0, p=g(1-g) has dp/dg=1 and d_n=exp(-t lambda_n).
Differentiating the k=0 and k=1 terms gives

    [partial_p d_n(t,0)]/exp(-t lambda_n)
                           =n(exp((n-1)t)-1).

After normalization by exp(t)-1, the relative completed-observation
insertion is, for n>=2,

    D_n(t)=n sum_(r=0)^(n-2) exp(r t),
    D_n(0)=n(n-1)=2 lambda_n.                         (1)

This is the previously used private formula, now applied through the actual
whole-source reference comb. It is independent of the slot's position
because every ordinary passage within that private slot contributes a
no-merger exponential. In particular no latent diagonal is queried.

The denominator p_n(z_*) is strictly positive by finite relevant exposures
and ordinary ancestral completion. Consequently

    I_n(nu)/p_n(z_*) = integral_(A-ancestral slots) D_n(t) dnu.   (2)

All terms are nonnegative. This applies to the SAME nu and original body
as in the full matching equations; choosing a different fitted body or
separate per-n normalization is unnecessary.

## 3. The large-copy contradiction

Suppose nu gives positive mass to t>0. The finite anchor cover yields an
anchor A,B with positive such mass on its A slots. For some eta>0 that
mass on t>=eta is c>0. Formula (1) gives

    I_n(nu)/p_n(z_*) >= c n exp((n-2)eta), n>=2.       (3)

The one-sided theorem, applied to this actual completed comb and the same
finite-body observable secant, gives fixed C,q<infinity with

    G_n(a)/p_n(z_*) >= -C(n+1)^(2q).                  (4)

Every population relevant to this selected comb has the inherited finite
anchor exposure bound, including routes of vanishing coin weight; irrelevant
unexposed populations are removed projectively. Thus this theorem's finite
exposure premise is available. It does not require the finite body to be
strict or the physical secant to be an ordinary parameter tangent.

Equations (3)--(4) contradict G_n+I_n=0 for sufficiently large n, since a
fixed positive exponential eventually exceeds every polynomial. Therefore
nu(t>0)=0. No effective arity bound or uniform exponent q is needed for this
contradiction on a single fitting countersequence.

## 4. Exact residual duty

Let alpha_A be the nu mass on A's private ancestry. On the remaining
zero-duration measure, (2) says

    G_n(a)/p_n(z_*)=-2 alpha_A lambda_n.              (5)

At every full original row the source-level insertion is the negative
ordinary generator -2Q, weighted by nu's private-slot masses. The outstanding
local theorem must show that an ACTUAL full-COMMON-fibre finite-body
observable secant cannot cancel those generators with a nonzero positive
measure. It must retain equal-arm endpoint ghosts, fair folds, zero gaps,
all physical parameter ties and the possibly mixed meeting continuation.
The joint ratio palette removes unequal-site escape but does not supply
this sign theorem.

The auxiliary nu is not an admitted source or an exact finite rival. Its
zero-duration support is a normalized local obstruction, not a construction
meeting the negative master quantifiers. All evidence here is hand derivation
and inherited source identities. Independent audit is required before this
composition is accepted; no numerical or formal verification is asserted.
