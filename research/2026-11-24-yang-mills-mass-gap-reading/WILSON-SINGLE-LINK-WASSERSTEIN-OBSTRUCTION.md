# Weak-coupling single-link Wasserstein obstruction for the SU(2) Wilson action

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof; no new Lean verification. This complements the [single-link total-variation result](WILSON-SINGLE-LINK-TV-WEAK-COUPLING-OBSTRUCTION.md). Neither result rules out multiscale, averaged, or differently parametrized estimates, or decides the physical mass gap.

Use the [Wilson plaquette measure](https://doi.org/10.1103/PhysRevD.10.2445) on a four-dimensional periodic lattice of side at least five, with density proportional to exp(beta times the sum of normalized real plaquette traces). Give SU(2), the unit quaternions, either its Euclidean chord metric or the unit-sphere geodesic metric. For links e and f, define c(e,f) as the worst ratio of the Wasserstein-1 distance between the two conditional laws at e to the distance between the two exterior values at f, when only f is changed. Both metrics are bi-invariant, and agree to first order on a differentiable curve. We prove
```
c(e,f) >= beta/4
```
for each of the 18 links f sharing a plaquette with e. The lower bound is witnessed by a one-Lipschitz gauge-invariant plaquette statistic. Even infinitesimally around the all-identity exterior, the corresponding single-neighbor coefficients for the link law tend from below (as a lower bound) to 1/6 in the weak-coupling limit. Thus merely discarding nearly cancelling exterior fields does not repair this *unblocked, entrywise absolute* argument at the aligned exterior.

## Vanishing staple field

Write the conditional density at e as exp(beta Re(U S)) divided by its Haar integral, where S is the sum of six oriented staples. These six three-link products are link-disjoint. Assign them the values 1,-1,i,-i,1,-1 in any order with the staple containing f assigned the first 1. Such an assignment is possible by taking two links in each staple equal to the identity and using the remaining link to produce its assigned value, picking f for the changed staple. Pick at the latter the orientation of a one-parameter perturbation so that its product becomes exp(i epsilon); all other staples remain fixed. The input distance is |epsilon|+o(|epsilon|), and S=exp(i epsilon)-1. Initially the conditional law is Haar.

Set F(U)=Re(U i), the normalized trace of the unchanged plaquette with staple i. This is 1-Lipschitz for both metrics: it is a unit linear functional on the quaternionic ambient Euclidean space. It is also the trace of the same plaquette in both exterior assignments. Differentiation at zero of the expectation of F under the perturbed conditional yields
```
d/d epsilon E_epsilon[F] at 0 = beta Var_Haar(F) = beta/4.
```
The first equality is the derivative of the normalized exponential tilt, justified by compactness; the second uses Haar on the unit 3-sphere and isotropy of its four squared coordinates. Applying the Lipschitz bound for any coupling and taking epsilon to zero proves the claim. At fixed nonzero perturbation, the conditional expectation and distance ratio in this test vary continuously in the other links, so the lower bound also survives taking an essential supremum over exteriors.

For any positive deterministic link weights w, at a link of minimum w the weighted row sum of the conditional influence matrix is at least 18 beta/4. Hence these same-metric single-link weighted Wasserstein coefficients cannot establish the strict less-than-one row criterion for beta >= 2/9. This is an obstruction to that sufficient criterion only, not a bound on the actual onset of any physical phenomenon.

## Aligned exterior

With all exterior links equal to the identity, make just one staple exp(i epsilon), so S=5+exp(i epsilon). For S nonzero, rotation invariance on the 3-sphere gives the conditional quaternionic mean as m(beta |S|) conjugate(S)/|S|, where m(t) is the mean real coordinate under the density proportional to exp(t Re U). In particular m(6 beta) tends to 1 as beta tends to infinity by concentration near the unique maximizer U=1. Since |5+exp(i epsilon)| has zero derivative at zero, the derivative of the imaginary coordinate of this conditional mean at zero has absolute value m(6 beta)/6. An imaginary coordinate is 1-Lipschitz in either metric, so a common-background, aligned lower-bound coefficient m(6 beta)/6 applies to every neighboring link. All such lower bounds can be measured at the same all-identity exterior, even though they use different one-neighbor perturbations. Their corresponding unweighted row sum tends to at least 3, and the minimum-weight argument gives the same bound for the supremal weighted row sum. This second test is for link laws, not a gauge-invariant distance on configurations.

A successful weak-coupling comparison must instead exploit a different metric or grouping, averaging, or correlated response across links. Nothing here supplies the continuum reconstruction or the [diagonal physical-time estimate](DIAGONAL-PHYSICAL-TIME-GAP-CRITERION.md).
