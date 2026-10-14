# Physical pair-clock tangent: attributed control-adapter corollary

Contributor: Codex whole-source lane, 14 October 2026.

Status: hand derivation and applicability clarification of an accepted result,
not new source mathematics. The October 4
[weak-factor reconstruction, Sections 1–3](../../../2026-10-04-dot-g3-new-reconstructions-1835z/INDEPENDENT-WEAK-FACTOR-RECONSTRUCTION-R1.md)
already proves the word-uniform estimate and ordinary infinitesimal ray, with
[independent acceptance](../../../2026-10-04-dot-g3-new-reconstructions-1835z/WEAK-AND-SURVIVAL-R1-INDEPENDENT-REVIEW.md).
The earlier [control-method applicability note](../../../2026-10-05-dot-g3-working-archive-0106z/graph-g3-convex-ordinary-20261004-2253z/CONTROL-PRIOR-APPLICABILITY.md)
also explicitly states the tangent-cone consequence. This note makes the
physical pair-hazard normalization and shared-cap adapter implication explicit.

## 1. Source and metric

Fix natural INDEPENDENT routing on an admitted private serial bridge word

    W = E_(a0) B1 E_(a1) ... BL E_(aL).

Here `E_a=exp(a Q)` uses duration notation; every displayed ordinary duration
and both arm durations are positive and finite, and every coin is interior.
The inherited sources sometimes write `E(z)` for survival `z=exp(-a)` instead.
The count L is any finite integer. Unequal arms, arbitrarily biased coins and
arbitrarily many cells are all included. Current roots retain their entire
already formed genealogies and are freshly routed at each cell.

At copy cap m, let `d_m` be the maximum total variation distance between the
complete labelled unranked forest rows over entering arities `k<=m`. Grafting
opaque input subtrees does not change the bound. Stochastic forest convolution
is nonexpansive in each factor in this metric, by conditioning on the complete
intermediate forest and then applying a stochastic grafting map.

Put `b_i=b_2(B_i)`, `q_i=1-b_i`, and

    h=h(W)=-log b_2(W)=sum_j a_j + sum_i [-log(1-q_i)].             (1)

This is the actual pair-survival hazard, not calendar time or the sum of all
arm durations. It is additive for this serial source. One source tuple defines
all rows and all caps, and h is the same scalar in each of them.

The inherited G6 estimate is

    d_m(B_i,E_(-log b_i)) <= D_m q_i^(3/2),
    D_m=2 binom(m,2)[(3/2)binom(m,3)+27binom(m,4)].                (2)

It is a full-forest bound uniform over all strict arm lengths and coins, not
only a diagonal estimate. See the preserved
[G6 source-critical review, Section 3.3](../../../2026-10-07-dot-g3-closed-source-envelopes-0021z/providers/G6-INDEPENDENT-REVIEW.md).

## 2. Count-independent chronological telescoping

Replace each B_i by its pair-matched ordinary factor in its original position.
Two-sided stochastic contraction and (2) give

    d_m(K_m(W),E_h) <= D_m sum_i q_i^(3/2).                       (3)

Only after all replacements are ordinary do their durations combine to h.
No nonordinary factors were commuted. Since

    sum_i q_i <= sum_i [-log(1-q_i)] <= h,
    max_i q_i <= 1-exp(-h) <= h,

we obtain the requested bounds, and the slightly sharper inherited one:

    d_m(K_m(W),E_h)
       <= D_m h sqrt(max_i q_i)
       <= D_m h sqrt(1-exp(-h))
       <= D_m h^(3/2).                                           (4)

If `h<=H`, the first bound in (4) is at most
`D_m H sqrt(max_i q_i)`. When there are no cells, set the maximum to zero;
the comparison is then exact. At m=2, `D_2=0` and the complete pair row is
indeed determined by its no-merger probability.

There is no hidden count bound, no lower bound on a coin, and no requirement
that the arms themselves tend to zero. A very long rare arm is still covered
by (2). The bound solely in h also passes to stochastic limits with positive
pair survival by continuity; no finite h is assigned to the zero-survival
boundary. Bounds involving individual q_i retain their presented-word scope.

## 3. Precise first-order control implication

Suppose `W_epsilon` is an actual finite strict word for each `epsilon>0`, with
its count, arms, coins and gaps allowed to vary arbitrarily with epsilon, and
suppose `h_epsilon=O(epsilon)` as epsilon decreases to zero. At each fixed cap,
the finite-dimensional ordinary Taylor expansion and (4) imply

    K_m(W_epsilon)
       = I + h_epsilon Q_m + O_m(h_epsilon^(3/2)+h_epsilon^2).

Hence, if `h_epsilon/epsilon -> c`,

    [K_m(W_epsilon)-I]/epsilon -> c Q_m,     c>=0.                 (5)

If the kernel derivative exists without a supplied limit for the clock ratio,
its pair coordinate gives that limit: `b_2=exp(-h_epsilon)` forces
`h_epsilon/epsilon -> -X_pair`, where X_pair is the derivative of the pair
no-merger coordinate. Thus the derivative is still `c Q_m`. In fact, existence
of any finite derivative at identity already implies `h_epsilon=O(epsilon)`
from that coordinate. Conversely ordinary edges realize every ray `c Q_m`,
including c=0 by positive durations of smaller order than epsilon.

If the same physical words are considered at every cap, c is common to all
of them. This conclusion does not use separately fitted cap-dependent words
to define a purported all-copy vector field.

Accordingly an identity-based, faithful actual-source control adapter with
time-linear pair-hazard cost has no nonordinary first-order input direction.
A singular observation map or an auxiliary control time not comparable to h
does not satisfy that premise merely by being smooth in its own coordinates.

## 4. Limits of the conclusion

The conclusion is first-order at identity. It does not preclude higher-order
bracket effects, full-dimensional source patches arbitrarily close to identity,
or exact returns at a finite positive target. Retuning parameters inside an
already positive body is not an identity-based prefix with zero clock, and its
additional directions are not excluded. Nor does (4) turn approximate equality
into exact equality or bound the total number of weak cells.

The full finite-INDEPENDENT master remains separate. No new legal observer,
nonordinary flow, physical negative time, numerical control implementation,
source-size bound or G4 closure follows from this corollary.

Verification: inherited proof and acceptance reads plus the displayed hand
telescoping and Taylor argument. No primary literature reread, numerical test,
symbolic program, Lean execution or Git operation was performed.

Provider SHA256 pins checked in this pass:

- Weak-factor reconstruction: `1e28fad1d68014acba9c9bcd6f50ad5032273b0aa1418eb111414dad4bb309ec`.
- Its acceptance review: `c42d23e4473eff9f540f8ac41115f2539794a95bf6fab8d64a1d9a6b03474e29`.
- G6 source-critical review: `58d346f1a5b21ad4229333dc3ca82b67a5ae397eb8f6e3b8bff57cd788763b48`.
