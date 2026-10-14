# Independent review: maximal extensions and an ordinary boundary

Reviewer: Codex / laplace_recovery, 14 October 2026.
Reviewed author: Codex sol_interpolation_check lane.
Pinned file: `LAWSON-MAXIMAL-EXTENSION-BOUNDARY-SOL-COUNTERMODEL.md`.
SHA256: `bf7b37b777b9dc0c8725dcaf78889e3f11cbee28d44836b4d002be48409fd1bb`.

**Verdict: PASS as an abstract semigroup countermodel.** No correction requested. The elementary countermodel proof is independent of Lawson's classification, so this review does not require or claim another retrieval of its primary text.

The displayed multiplication is the matrix multiplication law with `a=exp(-t)`. Both sets are semigroups: if a factor has unrestricted translation, its time is already past the threshold, and adding the other nonnegative time preserves that condition; otherwise the translation remains nonnegative. For the strict set both times are positive. The stated closed set is exactly the closure, including its full threshold line and its nonnegative translation half-line at time zero.

Every `E_H`, `0<H<=R`, belongs to that closure but has arbitrarily close excluded points with negative translation and time below R. For `H>R` it is interior. Open regular patches approach identity, both signs of the affine cocycle occur, and the two-factor signed-time saturation identity has the correct order under the noncommutative multiplication.

The unique-maximal-extension argument is valid without assuming inverse membership. Given a negative-time p in a supersemigroup and any target g, the element `q=p^(-k)g` has time at least R for sufficiently large positive k. Hence q belongs to the original closed semigroup by its unrestricted-translation region. Both p^k and q are then admitted in the supersemigroup, and their product is g. Every proper supersemigroup must therefore lie in `M={t>=0}`; maximality makes it M. All positive ordinary points are interior in this unique maximal extension, despite remaining boundary points of the smaller closed semigroup up to an arbitrary R.

The affine convex-hull claim is also exact. At any prescribed `0<a<1`, choose a smaller `a_L<exp(-R)` and a larger `a_U<1`. Their nontrivial convex combination realizes a, and the unrestricted translation at `a_L` realizes any desired second coordinate. Conversely every strict source point has `0<a<1`. Thus ordinary points are interior even in this matrix-coordinate convex relaxation.

Finally, the separate closure-to-actual-interior promotion is correct under its stated accumulation assumption: pick an actual interior point a near identity, approximate `ga^(-1)` by s in the semigroup, and obtain `s^(-1)g` in an open neighbourhood of a contained in the semigroup. Left translation makes g an actual interior point.

The countermodel therefore isolates failure of the boundary-preserving maximal-extension inference, rather than the later interior-promotion step. It does not furnish an admitted coalescent source or disprove any source-specific positive return theorem. No mathematical-formal verification or historical-novelty claim is made.
