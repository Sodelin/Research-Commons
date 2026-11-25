# A gauge-invariant massless diagnostic for Gaussian weak-coupling comparisons

2026-11-25 UTC. Research Commons / Dot. Scoped hand calculation in the quadratic tangent model, and a conditional obstruction to a class of comparison estimates. Not an assertion that the actual four-dimensional SU(2) Wilson model is massless, not a new Lean verification, and not a construction of the continuum theory.

The [single-link influence obstruction](WILSON-SINGLE-LINK-WASSERSTEIN-OBSTRUCTION.md) motivates using a gauge-invariant block observable instead of link-by-link absolute influences. The calculation below tests such an approach: a comparison that remains relatively close to the massless Gaussian reference at arbitrarily long physical times cannot yield a strictly positive gap for a nonzero limit of this observable.

## Exact quadratic reference correlator

Use the quadratic action (1/2) sum over lattice plaquettes of (dA)^2, with spacing one, in four Euclidean dimensions. This is the linearized Wilson action after rescaling the tangent coordinates to absorb the coupling and generator convention. Use three independent real colors for the SU(2) tangent field. One may fix a linear gauge and omit the global zero mode; the curvature dA does not see pure gauge modes. For the spatial plaquette F12 at spatial location zero and integer-time separation t≥1, write its single-color covariance as G(t). Set d_j(k)=exp(i k_j)−1 and Q(k)=sum_(j=1)^3 |d_j(k)|² for spatial momentum k. Then
    E(k)=2 asinh(sqrt(Q(k))/2),
    G(t)=∫_[-π,π]^3 ((|d_1(k)|²+|d_2(k)|²)/(2 sinh E(k))) exp(−t E(k)) dk/(2π)^3.

Indeed spatial curvature is d_1 A_2−d_2 A_1; its coefficient annihilates the gauge direction. Covariances on the transverse subspace have denominator Q(k)+2−2cos(k_0), giving that expression after Fourier integration in k_0. More explicitly, the Fourier coefficients of (Q+2−2 cos(k_0))^(−1) solve the one-dimensional difference equation with unit point source, with the decaying solution exp(−E|t|)/(2 sinh E) and cosh E=1+Q/2. The spatial zero momentum contributes zero to this plaquette. The same calculation on a spatial torus uses its normalized momentum sum with infinite time.

For k near zero, E(k)~|k|, and the integrand is bounded by C |k| exp(−c t |k|) on the full Brillouin zone; here comparability holds by continuity away from zero and the elementary bound on sin(k_j/2). Scale k=z/t and apply dominated convergence:
    t^4 G(t) → ∫_(R³) [(z_1²+z_2²)/(2|z|)] exp(−|z|) dz/(2π)^3 = 1/π².
In the last integral the angular average of (z_1²+z_2²)/|z|² is 2/3 and the radial integral of r³ exp(−r) is 6. Thus G(t) is strictly positive and has an algebraic tail. Even on a spatial torus of side L with L≥C(1+t), its lower bound is of order (1+t)^−4: restrict the positive momentum sum to k_1 in [1/(1+t),2/(1+t)] and the other coordinates of magnitude at most 1/(1+t). The number of grid points in this box is bounded below by a constant times (L/(1+t))³ when C is sufficiently large.

The first nonconstant term of the normalized SU(2) plaquette trace is a multiple of the color-invariant square. In this reference define W=sum_(c=1)^3 (F12^c²−E[F12^c²]). Wick's formula gives
    E[W(t)W(0)]=6 G(t)² ~ (6/π^4)t^−8.
The positivity is not an assumption about the sign of individual gauge-potential covariances. It follows from the spatial-curvature projection and Wick square. Support of the positive Laplace spectral measure reaches zero: the square is a double integral with rates E(k)+E(k'), and every neighborhood of zero contains a positive-weight momentum box for both variables. Taking a gauge-invariant square has not eliminated the soft modes.

## Consequence for relative comparison at long physical times

Using a lattice spacing a, multiply this Gaussian covariance by a^(−8) and set t=ceil(T/a); it converges to (6/π^4)T^−8 at any fixed T>0 in infinite volume. If a nontrivial Wilson continuum candidate for this same centered observable were shown to retain even a fixed positive fraction of that answer at a sequence T_j→∞, then it could not obey a uniform A exp(−m T_j) bound with finite A and m>0. Indeed this would imply m T_j≤8 log T_j+log(A/c) with c>0 independent of j. One can also run the same contradiction along diagonal lattice scales if both the physical-time exponential estimate and the lower comparison have uniform prefactors there and the spatial torus is large enough for the stated momentum lower bound.

The Gegenbauer/character or general block route is not ruled out. What is ruled out is a proof strategy that both preserves a positive Gaussian fraction at unlimited physical times for the same normalized observable and claims a uniform physical mass for it. A fixed physical **short-time** Gaussian approximation, or an absolute-error approximation that becomes larger than the Gaussian tail, incurs no such contradiction. In particular the ordinary weak-coupling expansion at fixed lattice size/interactions does not provide the needed relative lower bound after continuum scaling. Large-time renormalization, nonperturbative change of the spectral support or failure of that comparison are precisely what this diagnostic leaves open. The actual Wilson continuum tightness and physical-time estimate remain unproved.

Context: [Wilson action](https://doi.org/10.1103/PhysRevD.10.2445); [diagonal physical-time criterion](DIAGONAL-PHYSICAL-TIME-GAP-CRITERION.md). The Fourier identity and constants are derived above without extrapolating numerical data.
