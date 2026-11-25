# A fixed thin Wilson ribbon has asymptotically Haar relative transport

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction for the actual four-dimensional SU(2) fine Wilson law, applied to deterministic straight-path transport. No simulations, Lean verification, adaptive-route result, or mass-gap conclusion.

The [shrinking ribbon example](WILSON-SHRINKING-RIBBON-OBSTRUCTION.md) was a deterministic construction for the cutoff chart. Here there is a probabilistic counterpart for **unrenormalized fine straight paths** at one-loop scaling. Compare an axis-aligned path of m fine links with a path of the same endpoints that goes up b links, parallel for m links, and down b links, for fixed integer b≥1. Use no wrapping or repeated loop edges. If m/(1+beta_W) tends to infinity, the relative transport trace has the Haar SU(2) limit, even if the physical width and extra length tend to zero. In particular this applies at m comparable to L and beta_W=O(log L) inside the lattice of side 2L. For the root-to-root straight-path block map, one coarse spacing corresponds to b=2.

This uses the classical nonshared-plaquette conditioning method for perimeter upper bounds; see [Simon and Yaffe's perimeter upper bound](https://www.sciencedirect.com/science/article/pii/0370269382908152) and [Chatterjee's conditional proof](https://par.nsf.gov/servlets/purl/10339807). The relevant point here is tracking the contraction as beta_W grows, and applying it to a thin ribbon and to every fixed SU(2) character.

## Single-link contraction with the coupling visible

Identify SU(2) with the unit quaternions. Given all other fine links, the selected link U has density proportional to exp(beta_W Re tr(U B)/2), where B is a sum of at most six unit-quaternion staples after orienting all terms consistently. Each plaquette contains the link at most once in the lattice geometry here. If B≠0, right multiplication by the unit quaternion B/|B| transforms the law to a central density proportional to exp(kappa x) on SU(2), where x=Re tr(U)/2 and 0≤kappa=beta_W |B|≤6 beta_W. If B=0 the law is Haar. The transform only right-multiplies the mean representation matrix by a unitary, so it preserves its norm.

In an irreducible representation of dimension n+1, n≥1, the central mean is a scalar by Schur's lemma. Its absolute value is at most the expectation of the absolute normalized character. At x=cos(theta) the normalized character is sin((n+1)theta)/((n+1)sin(theta)); at theta=0 its expansion is 1−n(n+2)theta²/6+O_n(theta^4). Thus 1 minus its absolute value is at least c_n(1−x) for x sufficiently close to 1. The central Haar density of x is proportional to sqrt(1−x²) on [−1,1]. Set t=1−x. The tilted normalizing integral after factoring out exp(kappa) is at most C(1+kappa)^(-3/2), by bounding sqrt(t(2−t)) by sqrt(2t), using the gamma integral for kappa≥1 and boundedness otherwise. In a fixed small interval [a/(2(1+kappa)),a/(1+kappa)] in t, the integrand for the character loss is at least c_n t^(3/2) and exp(−kappa t)≥exp(−a). Here a>0 is chosen small depending on n. The integral of the loss is at least c'_n(1+kappa)^(-5/2). Consequently the conditional mean representation matrix has operator norm at most
    1 − c''_n/(1+kappa) ≤ 1 − c'''_n/(1+beta_W),
uniformly in the exterior. The same bound holds for the inverse link by unitarity.

## Whole contour and the limit

Take the m positively oriented collinear edges on the bottom of the rectangle. Distinct edges on that straight line share no plaquette (a plaquette's two parallel edges have different transverse coordinates). Conditional on the other links they are independent, because no term of the Wilson action uses two selected edges. Each enters the relative contour exactly once. Conditional expectation of the matrix product therefore inserts the conditional mean of each selected matrix in its original position. Submultiplicativity, with unit norm for every intervening fixed matrix, bounds every nontrivial normalized character moment in absolute value by

    exp(−c_n m/(1+beta_W)).

The normalized fundamental trace consequently tends to zero in expectation. Moreover finite linear combinations of the SU(2) characters give all polynomials in x (their Chebyshev form has successive degrees and nonzero leading coefficients). Density of polynomials in continuous functions of x gives weak convergence of x to the Haar trace law on [−1,1]. This determines the gauge-invariant conjugacy class of the relative transport, not a non-gauge-invariant law after a field-dependent gauge choice. Write U_0 and U_1 for the two transports with the same endpoints. The Hilbert–Schmidt identity
    ||U_1−U_0||_HS²=4(1−Re tr(U_0^* U_1)/2)
shows that the expected squared discrepancy tends to 4 and the probability of discrepancy at least 2 tends to 1/2, since the Haar trace density is symmetric and has no atom at zero.

## Scope

This is an unconditional obstruction to treating nearby fixed bare Wilson paths as the same random transport in the actual weak-coupling lattice limit. It does not condition on a cutoff event, whose indicators can depend on the same selected fine links. Nor does it establish the same Haar limit for the nonlinear chart-averaged links or for the field-dependent bulk router; that would require a new conditional contraction argument or a different observable. In particular it is not an obstruction to a renormalized Wilson observable, a gauge-invariant local correlation, or a continuum mass gap. A useful next comparison is between relative transports of regularized observables, not a claim that unrenormalized transport values agree merely because the detour shrinks.
