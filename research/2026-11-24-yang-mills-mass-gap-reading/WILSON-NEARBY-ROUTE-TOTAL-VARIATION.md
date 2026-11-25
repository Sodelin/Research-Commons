# Many nearby bare Wilson routes approximate independent Haar comparisons

2026-11-25 UTC. Research Commons / Dot. Scoped hand theorem for deterministic parallel routes under the actual fine four-dimensional SU(2) Wilson measure. No simulation, Lean verification, claim about the paper's nonlinear chart or router, or continuum mass-gap result.

The [single fixed ribbon result](WILSON-FIXED-RIBBON-HAAR-LIMIT.md) gives weak Haar convergence for the conjugacy class. Strengthening the contraction to all nontrivial representations at once gives convergence in conditional total variation, and leads to a different outcome if one may *select among many nearby routes* after seeing their bare transports.

## Uniform conditional smoothing and contraction

Use the old single-link conditional law and quaternion reduction: up to a fixed unitary translation it is the central tilted Haar law with density f_k(U)=exp(k x)/Z(k), x=Re tr(U)/2, where k is between 0 and 6 beta_W. The Haar density of x is proportional to sqrt(1-x^2) and the interval in t=1-x used in the old proof gives both bounds Z(k) comparable to exp(k)(1+k)^(-3/2). Hence ||f_k||_2²=Z(2k)/Z(k)^2 is O((1+k)^(3/2)). Its first selection supplies a density of L² norm O((1+beta_W)^(3/4)); fixed translations and inversions preserve that norm.

For every irreducible index n>=1, the normalized character is sin((n+1)theta)/((n+1)sin(theta)), with x=cos(theta). There is one absolute c>0 for which 1 minus its absolute value is at least c theta² simultaneously for every n when 0<=theta<=1/4. Write z=(n+1)theta. For z<=1 use sinc(z)<=1-19z²/120 and sinc(theta)>=1-theta²/6 to obtain the gap since n+1>=2. For z>=1, |sinc(z)|<=max(sin(1),2/pi)<0.85: sinc decreases on [1,pi/2], and beyond pi/2 use 1/z. Divide by sinc(theta)>=1-1/96. This gives a fixed gap in this second case. The same t-band [a/(2(1+k)),a/(1+k)] for a small absolute a as in the old proof therefore gives a Fourier operator norm at most 1-c'/(1+beta_W) on each nontrivial irreducible. The bound uses that theta² is comparable to t on the band. Noncentral translations of the conditional law merely multiply its matrix Fourier coefficients by unitaries.

Given a set of nonshared-plaquette links, condition on all exterior links. The selected ones are independent; their staple sums become fixed. Interleave their distributions with any fixed left or right translations along a path. By Peter–Weyl and the preceding uniform matrix bound, each convolution after the first contracts the mean-zero part of the density in L² by 1-c'/(1+beta_W). Total variation is bounded by half its L¹ distance, hence by half its L² distance. For m selected links on a single path this gives

    error <= C(1+beta_W)^(3/4) exp(-c'(m-1)/(1+beta_W)).

The bound is uniform in all exterior values, not only in the average.

## Simultaneous parallel routes

Take a fixed straight base route of m fine links and M deterministic alternatives with the same endpoints. Each goes transversely up to its own straight parallel line, travels m fine links there, then returns transversely to the endpoint. Use nonwrapping parallel lines whose transverse coordinates differ by at least two fine lattice spacings. Select the m longitudinal links on each alternative and none on the base. Two selected links on the same line share no plaquette; two on different selected lines share none by the separation. Transverse connectors are exterior, even if shared by different alternatives. Thus conditional on exterior links, the M alternative transports are independent, and each is close to Haar by the bound above. The base transport is fixed by the conditioning. Left multiplication by its inverse preserves Haar, so the entire tuple of relative transports is within

    C M (1+beta_W)^(3/4) exp(-c'(m-1)/(1+beta_W))

in total variation of the M-fold Haar product. This follows by telescoping product measures and is uniform in the exterior. Averaging retains the same bound. In gauge-invariant terms the corresponding relative traces are therefore jointly close to independent Haar traces. The gauge dependence of the full relative matrices at the common endpoint does not change the conditional estimate because it is uniform.

If m is comparable to L and beta_W=O(log L), the error tends to zero even for polynomial M; the geometry only needs, for example, M=floor(L^a), 0<a<1, among evenly spaced lines on the lattice of side 2L. All transverse detour widths and extra lengths are then O(M/L) in physical units and tend to zero.

## What fixed-path roughness does and does not imply

Let D_min be the minimum Hilbert–Schmidt discrepancy from the base among the M alternatives. In Haar SU(2), theta has density (2/pi)sin²(theta)dtheta and the discrepancy is 2 sqrt(2) sin(theta/2). Hence a Haar ball of small radius r has probability (1/(3 pi sqrt(2))) r³ + O(r⁵). In the regime above with M tending to infinity, the independent-product calculation, applied with the proven total variation error, gives for each fixed t>=0,

    Pr(M^(1/3) D_min > t) -> exp(-t³/(3 pi sqrt(2))).

For a single prescribed alternative the discrepancy does not go to zero, yet allowing the closest of a growing set of deterministically available alternatives makes it tend to zero. Thus the previous Haar result cannot by itself rule out close transport for an adaptive choice among a rich family. This example uses a selector that explicitly minimizes bare transport discrepancy. It does not say the published adaptive router makes such a choice, that a cutoff can be imposed within this conditional independence argument, or that the nonlinear chart transport has the same law.
