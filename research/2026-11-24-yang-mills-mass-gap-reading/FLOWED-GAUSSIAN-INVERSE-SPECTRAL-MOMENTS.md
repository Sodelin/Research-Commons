# Inverse spectral moments expose the Gaussian finite-volume mass artifact

2026-11-25 UTC. Research Commons / Dot. Scoped analytic hand deduction in the spatially flowed quadratic model. No Lean verification and no estimate for the actual weak-coupling Wilson theory.

The [zero-momentum benchmark](../2026-11-25-five-lane-parallel-pass/CHECKPOINT.md#yangmills-spatially-averaged-and-flowed-gaussian-plaquettes-remain-massless) shows an exponential plateau at fixed spatial volume despite zero infinite-volume mass. Its integrated time moments give a separate volume test, without fitting a plateau.

Fix physical spatial heat flow τ>0 and anchor s≥0. Let C_{τ,ℓ}(T) be the connected Gaussian Wick-square covariance in the continuum spatial torus of side ℓ, with time unbounded and the same volume-normalized spatial sum. Set
    M_r(ℓ)=1/Γ(r) ∫_0^∞ T^(r−1) C_{τ,ℓ}(s+T)dT,    r>0.
Then, as ℓ→∞,
* for 0<r<5, M_r(ℓ) converges to the finite infinite-volume inverse moment;
* for r=5, M_5(ℓ)=(80π²)^(-1) log ℓ+O_(s,τ)(1), using any fixed convention for length units;
* for r>5, M_r(ℓ)/ℓ^(r−5) converges to a finite strictly positive constant.

The same three regimes hold after normalizing by C_{τ,ℓ}(s), whose limit is finite and strictly positive. In particular, any finite-volume observed gap in this reference fails a volume-uniform fifth integrated-moment test.

## Proof and constants

Let k=2πn/ℓ for n∈Z³, and for n≠0 put a(n)=(n_1²+n_2²)/|n|². At fixed ℓ, the flowed continuum limit follows mode by mode from the lattice momentum sum, with domination from Gaussian flow and the bounds Q(k_lattice)≍|k_lattice|² on its Brillouin zone. The zero mode has zero curvature weight. The resulting positive spectral measure has an atom at energy E=2|k| for each n≠0 with weight
    (3/2) ℓ^(-3) |k|² a(n)² exp(−4τ|k|²).
The time integral is its inverse E^r moment with tilt exp(−sE), by Tonelli and the Gamma integral. Consequently
    M_r(ℓ)= (3/2) 2^(-r) (2π)^(2−r) ℓ^(r−5)
      ∑_(n≠0) |n|^(2−r) a(n)² exp(−4τ(2π|n|/ℓ)²−4πs|n|/ℓ).
For r>5 the uncut sum is convergent, with strictly positive terms, and dominates the tapered sums. This also gives the exact coefficient as the displayed prefactor without ℓ^(r−5), times the uncut sum.

For 0<r<5 the momentum sum is a Riemann sum on regions away from zero. The sum in a ball of momentum radius ε is O_r(ε^(5−r)) uniformly as the grid spacing tends to zero, by counting points in concentric lattice dyadic shells. The large momentum tail is controlled by heat flow. Thus the limit is
    (80π²)^(-1) ∫_0^∞ E^(4−r) exp(−τ E²−sE)dE,
using the explicit infinite-volume spectral density.

At r=5, replace the taper by 1 for 0<|n|≤ℓ. The error there is O(1) since 1−exp(−c_1 |n|/ℓ−c_2 |n|²/ℓ²)≪_(s,τ)|n|/ℓ; the omitted tail beyond ℓ is also O(1) by Gaussian decay on dyadic shells. The homogeneous summand |n|^(−3) a(n)² is smooth away from zero with gradient O(|n|^(−4)). Comparing lattice points to unit cubes gives bounded total error against integration over 1≤|u|≤ℓ, since ∑_(|n|≥2)|n|^(−4)<∞ and the outer boundary contributes O(1). The angular integral is 4π·8/15, giving
    (3/2) 2^(-5) (2π)^(-3) · 4π · 8/15 = 1/(80π²)
as the coefficient of log ℓ.

## What a Wilson test would need

For any nonzero anchored positive spectral measure supported on E≥g>0, all its normalized inverse moments obey M_r/C(s)≤g^(−r). The divergence just proved is a falsification check for a purported volume-stable gap in the Gaussian model. A finite fifth moment alone cannot certify a gap: for example an infinite-volume measure with density E^6 on (0,1) has a finite fifth inverse moment and still reaches zero. An exponential-in-order bound on all positive integer normalized inverse moments of a reconstructed measure would force a gap, by applying the moment bound to any positive mass below g and taking roots as the order grows. Applying this to a continuum family still requires nontrivial reconstruction, density of the tested vectors and actual physical-time Wilson bounds; no such input is supplied by the Gaussian calculation.
