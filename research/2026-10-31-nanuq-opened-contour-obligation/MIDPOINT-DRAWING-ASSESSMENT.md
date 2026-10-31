# Same-drawing opening: exact candidate construction, not a compiled provider

Source inspected: existing `NanuqActualOpenedHybridTree` / `NanuqActualOpenedIncidence` and original `G1OuterLabelledMultigraphCurves.PlanarCurves`. The admitted opened graph retains the explicit hleaf premise that hybrid children are taxa; this assessment does not silently discharge that source premise for every RootedBinary.

For the actual opened vertex sum, keep each SkeletonVertex at its old point. Place the new HybridParentOccurrence of original edge e at the old arc's parameter 1/2. Keep skeleton arcs unchanged; parameterize each opened incoming edge by the old arc at t/2. The underlying original edge ID is unchanged.

The original PlanarCurves fields provide a direct proof route:
- An old vertex cannot equal an interior midpoint: vertex_incidence reduces it to an old endpoint, and arc injectivity excludes parameter1/2=0or1.
- Distinct new tips cannot coincide: edge_incidence for distinct original IDs would make both midpoint parameters endpoints. Equal IDs give equal occurrences.
- Original edge IDs cannot coincide across skeleton-edge and hybrid-parent tags because their target-hybrid predicates are incompatible.
- A skeleton edge cannot contain a new midpoint as an interior vertex, for the same original incidence reason.
- A prefix can meet its own new midpoint only at its new endpoint; it meets a retained old vertex only at the old source. Different prefix edges intersect only at their common old source endpoints when applicable.
- Every new arc is a subset of its original arc, so the complete opened drawing is a subset of the original drawing; retained ordinary taxon points remain unchanged.

This is a same-original-drawing construction, not an arbitrary planar redraw, rotation choice, or old-outside-face membership assumption for new tips. It still needs an exact Lean provider and the appropriate path-restriction endpoint identities. No such source or compiler acceptance is claimed here.

The inspected qualified128 supplier closure contains combinatorial Graph.Tree and single-arc complement results; the bounded name/body search did not identify a ready theorem that the complement of every actual finite embedded tree is connected/nonseparating. This is a specific remaining supplier need if the tree-nonseparation route is chosen, not proof that no theorem exists elsewhere. Even a one-face theorem would not by itself prove paired adjacency or collapse to the given original taxon circle C.

The original bounded-face/ear route remains available and useful. No existing supplier is discarded, and no further proof consumer has been stacked on this assessment.
