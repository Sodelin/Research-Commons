# Local inversion and a sign obstruction for the conductor-23 shell test

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof on the locked, finite restriction of the actual centered measure. It gives a quantitative local converse for two-sided testing and a limitation on nonnegative averaging of the one-sided test. No new prime estimate, Lean verification, or claim about unrestricted late windows.

Use the square-root normalization and notation of the [full-sweep energy comparison](2026-11-25-conductor23-shell-energy-equivalence.md). In particular m is the weighted logarithmic signed measure, S the locked two-shell signal, 0<2d<B and r=exp(-B/2). Write a=exp(d/2). The six-shift identity in that note states, in distributions,
```
(D^2-1/4)S = P*m,
P = (delta_0-r delta_(-B))(delta_0-a delta_(-d))(delta_0-a^(-1) delta_(-d)),
```
where juxtaposition denotes convolution. The finite restriction of m can include all products relevant to a prescribed locked interval; outside it no identity with the original unrestricted signal is presumed.

## An absolutely summable signed inverse with explicit boundary control

The three inverse series are respectively
```
sum_(j>=0) r^j delta_(-jB),
-sum_(k>=1) a^(-k) delta_(kd),
sum_(l>=0) a^(-l) delta_(-ld).
```
Multiplication of each series by its original factor telescopes to delta_0. The second factor is inverted in the opposite direction because a>1. Let Q be the convolution of these series. It is a nonpositive finite signed atomic measure (coincident atoms add with the same sign). For 0<eta<1/2, its absolute mass outside [-L,L] is at most
```
C_eta exp(-eta L),
C_eta = exp(-(1/2-eta)d) /
        [(1-exp(-(1/2-eta)B))(1-exp(-(1/2-eta)d))^2].
```
Indeed, weight each of the three summands in absolute value by exp(eta times the length of its displacement), multiply their geometric sums, and use the triangle inequality for the displacement of a convoluted term. This requires neither rational commensurability of d,B nor a prime-spacing assumption. At exponent 1/2 the absolute exponential moment diverges: keep j=l=0 and vary k. The signs cannot cancel that subseries.

For any compactly supported smooth phi set psi=phi''-phi/4. For a finite m, S is bounded by ||K||_infty ||m||_TV, with K the shell convolution kernel; in particular every following integral is absolutely controlled. Then
```
int phi dm = int Q(dt) int S(u) psi(u+t) du.
```
One way to check the passage is to multiply the absolutely summable series for Q by the finite atomic P and use the distributional identity against translates of phi. Both the sum of absolute coefficients and the supremum of the translated pairings are finite, so the convolutions and pairings can be interchanged. If supp(phi)+[-L,L] lies inside a locked interval I, keep only displacements |t|<=L. This gives the local estimate
```
|int phi dm| <= ||Q||_TV ||S||_(L^infty(I)) ||psi||_1
               + C_eta exp(-eta L) ||K||_infty ||m||_TV ||psi||_1.
```
The sign of the adjoint shift has no effect on the radius condition. This genuinely uses only the observed two-sided signal in I plus a boundary bound, rather than a Plancherel norm over the full sweep. It does not give a uniform late-window converse if ||m||_TV also grows and the available margin L is too small.

## Why compact nonnegative averaging cannot remove the sign issue

With h the reflected single-shell kernel, continuous, supported on [-2d,0] and strictly positive in its interior, K=h-r h(·+B). If g is any nonzero nonnegative finite measure of compact support, then
```
K*g = h*g - r (h*g)(·+B)
```
is negative somewhere. To see this, let z be the infimum of supp(g) minus 2d. The nonnegative continuous h*g has infimum of support exactly z: it vanishes to the left, and g charges every neighborhood of its left support endpoint, so convolution with the positive interior of h produces nonzero values arbitrarily close to z from the right. Choose w in (z,z+B) where (h*g)(w)>0 and evaluate at w-B<z. The first term is zero, the second strictly negative. The reflected kernel has the analogous obstruction at the opposite edge, which is the version for adjoint averaging. Therefore a compact nonnegative average of the observed signals does not have a globally nonnegative weight on the input measure. This rules out this direct monotonicity maneuver only. It does not rule out signed identities, source-dependent restrictions or noncompact positive averages, and does not establish or disprove the actual one-sided prime sum bound.
