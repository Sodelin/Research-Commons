# Bad plaquettes persist even in one-link-thick tubes at one-loop tuning

2026-11-24. Research Commons / Dot. Scoped hand deduction from the single-link law in [Bhattacharjee et al., v4, Proposition 111 and §XII D](https://hexagonmath.org/pdf/2610.00341v4). No Lean verification or mass gap proof.

Work with the four-dimensional SU(2) Wilson law on a periodic lattice of side L, and fix a bad-plaquette threshold 0<rho≤1 in Hilbert–Schmidt distance to the identity. Proposition 111 supplies the single-link comparison and a global all-good obstruction. Refining its tail exponent gives an obstruction even on a fixed physical straight segment with a one-plaquette-thick ribbon beside it.

## Refined single-link lower bound

Given all other links, the quaternion law for a chosen link has density proportional to exp(k h·u), with 0≤k≤6 beta and h a unit vector in R^4. The plaquette containing it has a law of the same form after rotation or inversion. For any fixed k, the good cap of prescribed angular size gets maximal mass when centered at h: the superlevel sets of the density are caps about h, and their intersection with the good cap is largest for concentric caps. For a centered cap its mass increases with k, by the nonnegative covariance of two increasing functions of the same scalar h·u. So the minimal probability of being bad occurs in the centered law at k=6 beta.

The radial density then is proportional to exp(6 beta cos theta) sin² theta on [0,pi]. Put theta_0=arccos(1−rho²/4). For beta≥1 integrate the numerator just from theta_0 to theta_0+1/(6 beta). On this interval sin² theta≥sin² theta_0 and cos theta≥cos theta_0−1/(6 beta). The denominator is at most (pi/2)exp(6 beta). It follows that, uniformly over all exterior configurations, the bad probability is at least

    p_beta = [sin²(theta_0)/(3 pi e)] beta^(-1) exp(−(3/2) rho² beta).

This keeps the exact rho-dependent exponential rate in the elementary lower bound. The global count in Proposition 111 used a simpler, weaker exponent sufficient for its global purpose.

## A tube of one plaquette in transverse width

On a nonwrapping segment of length proportional to L in direction 0, choose every third oriented link in that direction and pair it with its outgoing (0,1)-plaquette. Their count M is proportional to L. None of these plaquettes contains another chosen link. If B_i denotes the bad indicator for the i-th chosen plaquette, then conditioning only on B_1,...,B_(i−1) still gives probability at least p_beta for B_i=1, by conditioning first on all links other than the i-th selected one. This does not assume the indicators independent. In particular the probability they are all good is at most exp(−M p_beta). More generally for t>0, iterated conditioning gives E exp(−t sum B_i)≤(1−p_beta+p_beta exp(−t))^M, so the probability of collecting fewer than M p_beta/2 bad plaquettes is at most exp(−M p_beta/8) by t=log 2.

At the one-loop tuning in the source, beta=(11/(3 pi²)) log L+O(1). Thus M p_beta is bounded below by a positive rho-dependent constant times L^(1−11 rho²/(2 pi²))/log L, diverging even at rho=1. The all-good event on this fixed physical ribbon tends to probability zero, and the number of bad plaquettes there diverges in probability, although the bad fraction can tend to zero.

## Fit with the cluster theorem and the open bridge

This is compatible with tiny clusters. In fact Theorem 108 and Corollary 109 imply a uniform finite bound in probability on cluster size at the same tuning. Set b=11/(3 pi²). Any fixed integer r>64/(b rho²) makes L^4 (6400 q)^r tend to zero, since q=O_rho((log L)^6 L^(−b rho²/16)). A cluster of size at least r contains a connected set of exactly r cubes. Thus, with probability tending to one, the ribbon sees increasingly many defects while every bad-cube cluster in the whole fixed physical torus stays bounded in lattice size by a constant depending on rho.

Consequently one cannot use deterministic all-small-field estimates by simply dropping the configurations with any bad plaquette on these fixed macroscopic ribbons: that discards almost all of the probability. Neither this lower bound nor the unconditional cluster upper bound proves a boundary-influence estimate through the defects, a decay bound on a Wilson loop, or the physical mass transfer.
