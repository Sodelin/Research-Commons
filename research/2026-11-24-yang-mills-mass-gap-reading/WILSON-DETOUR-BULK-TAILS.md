# Superpolynomial bulk routing reliability for the Wilson cutoff

2026-11-25. Research Commons / Dot. Hand deduction for the actual four-dimensional SU(2) Wilson law, using the prescribed-set bound in [Bhattacharjee et al., v4, Theorem 108 and Corollary 110](https://hexagonmath.org/pdf/2610.00341v4). This is not a mixing estimate, holonomy comparison, or Lean result.

The fixed-width [detour construction](WILSON-CUTOFF-FREE-DETOURS.md) makes the failure probability small. A logarithmically growing strip makes the *bulk* failure smaller than any inverse power of lattice size. Endpoint effects must be distinguished: either allow the endpoints to slide by logarithmically many links, or pay the fixed-endpoint cost separately. The result remains at vanishing physical width.

## Statement

Keep the same axis-aligned, nonwrapping geometry and cutoff rho=1/12. Let the strip have m coarse columns with m comparable to L and W=ceil(log L) rows, on a fine lattice of spacing a. In the paper's one-loop regime take qbar = C (log L)^6 L^(-gamma), gamma=(11/(3 pi²))rho²/16, as an upper bound for q in Theorem 108. With failure probability O_A(L^(-A)) for every fixed A, there is a gauge-invariant measurable choice of route connecting the two vertical sides, with these properties:

* Its horizontal steps all point east and number exactly m. Every link used has chi=1.
* Each endpoint lies within W-1 coarse steps of its original endpoint. The interior stays in the same W-row strip.
* The excess length over m is O(m W² qbar). If one insists on the original endpoints, join by vertical boundary stubs of total length at most 2(W-1). The bulk route still satisfies the same conclusions, but the guarantee that these stubs have chi=1 is only 1-O(W qbar) from the estimates here.

Thus for an observable bounded by a fixed polynomial in L, discarding the bulk failure event incurs smaller than any polynomial error, even after that normalization. This statement is about the exceptional event only and gives no approximation of values on the good event. At fixed physical side La, both endpoint shifts and the additional physical length tend to zero.

## Proof

Use the same tile masks, each of at most 96 fine cubes, with each cube belonging to at most 16 tile masks. Let U count the distinct bad cubes in the deterministic union of masks. This union has n<=n_0=96mW members. The prescribed-set bound gives for any t>=0

    E exp(t U)
      = E product_x [1+(exp(t)-1) 1_bad(x)]
      <= [1+qbar(exp(t)-1)]^n
      <= exp(n_0 qbar (exp(t)-1)).

Consequently P(U>2 n_0 qbar) <= exp(-(2 log 2-1)n_0 qbar), which is smaller than any inverse power of L, since gamma<1. A dirty column contains at least one blocked tile, and every blocked tile has a bad witness in its mask. Therefore the number D of dirty columns satisfies D<=16U with no independence assumption.

For W prescribed tiles, the witness union bound from the fixed-width construction is at most 96^W qbar^ceil(W/16). Taking a union over W-column windows and choices of W tiles in each window gives

    P(some window has at least W blocked tiles)
      <= m binom(W²,W) 96^W qbar^ceil(W/16)
      <= exp(- (gamma/16)(log L)^2 + O(log L log log L)).

On the good event every consecutive dirty run has length below W, and, by extension to a W-column window, contains fewer than W blocked tiles total. It has a completely unblocked row. Route each interior run as in the fixed-width proof. If a dirty run meets an outer side, start or end on that run's selected row, without requiring a climb or descent in the corresponding boundary column. At the inner end use the adjacent clean column as before. The whole strip cannot be a single dirty run when m>=W. Every route edge lies on an unblocked tile. Select the lowest unblocked row in each run. The number of extra vertical steps over all runs is at most 2(W-1)D=O(mW²qbar). The deterministic boundary stubs can use only vertical edges lying on the first or last column's tiles; if both columns contain no blocked tile, their cutoffs are all inactive. A one-tile union bound gives the stated O(Wqbar) upper bound on loss of this sufficient event.

## What remains

An endpoint-free or spatially smeared comparison can discard bulk routing failures at polynomial normalization without a rare-event conditioning argument. It still must compare field-dependent routed holonomies to the intended continuum observables. Neither a shrinking support displacement nor a shrinking physical detour length alone implies that comparison, and no conditional Wilson bound follows from the moment generating function above.
