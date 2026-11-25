# An actual weak-coupling obstruction to single-link total-variation contraction

2026-11-25 UTC. Research Commons / Dot. Elementary hand proof for four-dimensional SU(2) Wilson plaquette measure on a periodic lattice of side at least five, or for an interior link in an ordinary box. No Lean verification. This is a worst-boundary local obstruction, not a claim about the existence or absence of the physical mass gap. It does not concern block, averaged, or metric-based couplings.

Use the [Wilson action](https://doi.org/10.1103/PhysRevD.10.2445), with density proportional to exp(beta sum_p (1/2) Re tr U_p) against independent Haar link variables. Here beta is the inverse coupling in this convention. At an oriented link e, fix all others. The six incident plaquettes give six oriented staples, the three-link products oriented so that reversing a plaquette if needed writes its trace as Re tr(U_e S_i). The one-link conditional density on SU(2) is exactly
    c exp(beta sum_(i=1)^6 (1/2) Re tr(U_e S_i)).
If the given geometry has wrap-around identifications, the stated minimum side length avoids shared links in distinct three-link staples. All 18 link neighbors of e obtained from these staples are distinct.

Let c_(e,f)(beta) be the supremum total-variation distance between the two conditional laws at e when only the link f in the exterior changes. For each of the 18 neighboring links f,
    c_(e,f)(beta) >= 1-O(exp(-c beta))
with absolute c>0, hence the standard row-sum Dobrushin condition fails strongly at weak coupling. On a periodic lattice no positive deterministic link-wise weighting restores that condition.

## Two simple boundary configurations

Identify SU(2) with the unit quaternions and half the trace with the real part. In the first exterior assignment every link is the identity, so the exponent is beta*Re(6U_e). In the second change only f to a purely imaginary unit quaternion, for instance i. Only one staple changes, to i or -i according to orientation; its other factors are identities. The exponent is now beta*Re(U_e(5±i)). These two densities have unique maximizers respectively at
    u_0=1,             u_1=(5∓i)/sqrt(26).
This follows directly from the real inner product on R^4. For any open neighborhood of a unique maximizer of a fixed continuous function on the unit quaternions, the probability of its complement under the exponential density here is O(exp(-c beta)): compactness gives a strictly smaller maximum outside, and a smaller open cap inside has positive Haar mass and energy above that outside maximum. Fix disjoint neighborhoods of the two displayed maximizers. Testing one of these neighborhoods gives the claimed distance. The constants can be chosen uniformly for the 18 choices of f because their two exponents, up to conjugation and sign of i, have the same form. Conditional densities depend continuously on all fixed links at fixed beta, so the worst-case conclusion would also hold with an essential supremum.

The same lower bound holds for the distributions of one unchanged plaquette's **gauge-invariant normalized trace**: choose any other staple, which remains the identity in both assignments, so that trace is Re U_e. At the two maxima the traces are respectively 1 and 5/sqrt(26). Test whether the trace exceeds the midpoint of these values; each bad event stays outside a fixed neighborhood of the corresponding maximizer. Thus this example is not solely an artifact of comparing gauge-variant point values of a link. It is still a comparison of particular worst-case exterior assignments, not of typical configurations in the Gibbs state.

## Link weights cannot fix this single-link criterion on a torus

On the torus let A be the adjacency matrix whose 18 neighbors are the links sharing a plaquette with a given link. It has constant row sum 18. The influence matrix C is nonnegative and entrywise dominates (1-O(exp(-c beta)))A, so its spectral radius is at least 18(1-O(exp(-c beta))). Equivalently, for any positive vector w, at a coordinate attaining the smallest weight the weighted row sum sum_f C_(e,f) w_f/w_e is at least this same lower bound. Thus changing deterministic per-link weights cannot give a uniform contraction coefficient below one in this unblocked total-variation argument as beta tends to infinity.

This rules out one concrete way to obtain the [physical-time spectral bound](DIAGONAL-PHYSICAL-TIME-GAP-CRITERION.md). The remaining question is genuinely about field configurations at larger scale: a block method, a typical-boundary comparison with separately controlled bad configurations, or a physical observable metric could behave differently. The result does not contradict a strong-coupling Dobrushin bound, a result in another metric, or a continuum construction for a gauge theory coupled to Higgs matter.
