# A polylog-size geometric grid detects an unattained off-line supremum

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof for the fixed conductor-23 two-shell detector. Uses its existing explicit formula and the same uniform power-gap comparison with locked arithmetic cutoffs, including the original abelian centering input. No new Lean verification or signed arithmetic bound.

The [finite-grid proof on an attained line](2026-11-25-conductor23-finite-grid-rightmost-detector.md) gives a fixed number of samples. The [positive-filter proof](https://github.com/Sodelin/Research-Commons/commit/7a2d2c5d790118523c794119cc9d69237c787fd2) detects an unattained supremum on short continuous log windows. Combining fixed smoothing with exact annihilation on a lattice gives a deterministic grid of only O(log X (log log X)^4) samples, with no attainment or ordinate separation assumption. The grid is specified without zero ordinates. Its constants depend on the fixed factor and smoothing, not on a chosen zero.

## 1. Fix the smoothing once

Write u=log x and let F(u) be the square-root-normalized full [two-shell statistic](2026-11-25-conductor23-two-thin-product-shells.md). Its zero expansion has absolutely summable coefficients c_rho multiplying exp((rho-1/2)u), nonzero for every off-line zero, with positive coefficients for real zeros above 1/2. Keep the previous decaying elementary error.

Choose a fixed d>0. Average F(u+t) against the law of a sum of independent uniforms on [0,l_j], where l_j is proportional to 1/(j log^2(j+1)) and sum l_j=d. This is supported on [0,d]. Its multiplier M(z) is the product of (exp(l_j z)-1)/(l_j z). For fixed z the factors differ from one by a summable sequence; the product is nonzero for Re z>0 and positive for real z. It is bounded on the normalized strip, and on that strip it also satisfies
```
|M(sigma+i t)| <= C exp(-c |t|/log^2(3+|t|)).
```
Indeed, for each of the first J=floor(c_0 |t|/log^2(3+|t|)) factors and sufficiently large |t|, choose c_0 small enough that l_j |t|>=4(1+exp(d/2)). Each of these factors then has modulus at most 1/4 by its numerator bound; the product of the remaining factors is at most exp(d/2) by positivity and total support. Thus the smoothed coefficients a_rho have the displayed tail factor times |c_rho|, while the target coefficient stays nonzero. This is fixed smoothing of the same two shells, not a filter fitted to prime observations.

## 2. Exact annihilation on a given grid

For z=sigma+i omega with omega nonzero and 0<h |omega|<=1, there is a probability supported on the grid h times the nonnegative integers, within [0,pi/|omega|+h], whose transform vanishes at z. Set n=floor(pi/(h|omega|)). If n h |omega|=pi, use the antipodal points 0 and nh. Otherwise, the unit-circle phases at 0, nh and (n+1)h have successive circular gaps at most pi. Hence their convex hull contains zero (equivalently they cannot all lie in an open semicircle). The negative-omega case is the conjugate. For convex weights w_j on these phases summing to one with weighted sum zero, replace them by weights proportional to w_j exp(-sigma jh). This gives the required vanishing even for nonzero sigma. Convolution preserves exact zeros and support on the given grid. No weight is negative.

## 3. Grid and detector

Let V=log X and choose T=K V log^2(3+V) for a sufficiently large fixed K, and h=1/(4T). Fix any off-line rho_0=b+i gamma_0 with the largest real part at its ordinate, and put v=V-L, where L is a sufficiently large fixed multiple of 1+log^2(3+V). Use the grid v+jh, or start at the first grid point not below v on a globally anchored grid with the same spacing. Small fixed right-end margins are available within L for the fixed forward smoothing and the two-shell shifts.

Apply the previous two-moment argument at this start to the smoothed statistic rescaled by exp(-(b-1/2)u). For every |Im rho|<=T, convolve the grid probabilities killing rho-b and rho-b-i gamma_0 whenever the respective exponent is nonreal. Eventually h times each of those ordinate magnitudes is <=1. The total support length is O(log^2(3+T))+O_{rho_0}(1)+O(h T log(3+T)), by the unit-band zero count and the O(h) rounding overhead per factor. Thus L fits the entire convolution for every fixed target once sufficiently late. The implied leading constant can be chosen independently of the target, whose fixed ordinate and small differences only affect onset.

For the unmodulated and modulated moments, the zeros above T have total magnitude at most
```
C exp(V/2 - c T/log^2(3+T)) sum_rho |c_rho| = o(1).
```
Here all sample points are at most V, and Re rho-b<=1/2. Choose K sufficiently large. This uses the fixed smoothing, so high-frequency aliases on the grid cannot defeat the estimate. Low modes are killed exactly except for real exponents in the first moment and target-ordinate exponents in the second. Real zeros with real part above 1/2 contribute nonnegatively; the finitely many others decay. At the target ordinate the smaller real parts and the elementary remainder decay. The first moment is therefore at least -o(1), while the second is a_{rho_0}+o(1). The probability average of the positive part is at least |a_{rho_0}|/4, so at least one of its support points has that value or greater. Undoing the rescaling gives a lower bound of order exp((b-1/2)(V-L)) at a grid point. For each fixed accuracy in the exponent, choose b arbitrarily close to the real-part supremum, then let V grow. Neither that choice nor the zero-dependent convolution changes the grid.

It follows that the grid maximum of the positive full detector has logarithmic rate (sup Re rho-1/2)V+o(V) if there is an off-line zero. By the existing uniform power-gap transfer, the same holds for the appropriately signed smoothed retained detector on admissible locked windows: choose fixed target b sufficiently near the supremum that its signal exponent exceeds the uniform discrepancy exponent. Conversely the earlier GRH upper bound is preserved by fixed smoothing. The grid has O(L/h)=O(log X (log log X)^4) samples. Thus an X^{o(1)} upper bound for the normalized retained statistic at those nodes on arbitrarily late eligible windows suffices, without an attained rightmost line.

This reduces the sampling burden only. It does not give a subpower-cost method for evaluating each arithmetic sample, nor the square-root-scale signed estimate at the nodes.
