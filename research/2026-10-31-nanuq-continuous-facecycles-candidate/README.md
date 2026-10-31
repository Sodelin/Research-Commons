# Continuous same-drawing face cycles — candidate

**UNCOMPILED.** A single directly needed source adaptation, not an accepted theorem or full NANUQ certificate.

The candidate targets `Graph.face_cycles_continuous`: every face of a finite graph with the supplier's ORIGINAL `IsDrawing G drawing` and `G.IsTwoConnected` has a cycle boundary in that SAME drawing. It removes original polygonal-edge requirements by supplying their actual uses, not by deleting a required unused binder or postulating the missing property.

## Exact derivation and attribution

The base-cycle, one-ear and final ear-induction proof bodies are adapted from Álvaro Begué's Apache-2.0 `Schoenflies.FaceCyclesProof`, immutable upstream commit `05a43d29cde026618777db3d4e4316204ccca237`, source SHA256 `46902b10c30553fd56099fcc5e1f491391f2d9596631ddd4f2f4284ba5721a70`. Copyright, attribution and license are preserved. Adaptation: dot, 2026-10-31. This is not a graph-theory novelty claim.

The original proof's polygonality uses occur in cycle separation and its ear crosscut application:

1. Each actual cycle of the original continuous drawing is Jordan by `Graph.IsDrawing.cycle_isJordanCurve`. The qualified full `jordan_curve_theorem` supplies separation, both for the initial cycle and each spliced cycle. No redrawing occurs.
2. The same actual two boundary arcs from `arcs_of_split` form the required `IsCutPair`. The new original continuous crosscut theorem supplies the exact component-region alternative in the selected OLD face, whether bounded or unbounded. The ear's actual endpoint meeting, containment and edge freshness are proved by the original supplier argument.
3. Existing same-drawing ear induction, untouched-face preservation and spliced ORIGINAL cycle lists remain in place. No new rotation/order/collar/star or face-cycle premise is introduced. In particular, the old conditional `CrosscutSplitsRegion` is not retained as a new hypothesis.

The generation script validates the immutable upstream SHA before extracting the three exact proof sections and replacing the stated use sites. It is a source-preparation recipe, not a compiler receipt.

## Bigons and the ≥3 convention

`hasFaceCycles_cycleGraph_continuous` takes ANY actual `IsCycleThrough`, without a three-vertex assumption, and thus covers a named two-edge parallel cycle in its exact cycle subgraph. The final `face_cycles_continuous` retains the supplier's `IsTwoConnected`, including its ≥3 convention. A bigon is not falsely promoted to IsTwoConnected. The original source classification of singleton/two-vertex blocks, and the exact identification of each such block with its named cycle subgraph, remain separate source joins; they are not silently assumed here.

## Critical remaining gates

Even acceptance of HasFaceCycles would not prove the fixed original taxon circle C, the original displayed-split support theorem, or adjacent duplicate tips. In particular, a newly opened hybrid tip is NOT an old labelled taxon; old TaxonOuterFace membership cannot simply be reused for that new tip. Its incidence with the selected ORIGINAL outside face, cyclic position and adjacent-copy relationship still require an actual source proof. Bridges, vertex-star assembly and global original-network composition remain open.

This candidate neither changes the drawing nor chooses arbitrary child order. No supplier build or local execution has been launched. All upstream imports are already in the qualified 128-module supplier closure; the new continuous-region dependency has scoped compiler acceptance at `cb2d0ba9d2517cee120b5551aa44dbcbb40ec5e9`, unchanged source SHA256 `12ac1934b36fca9594bec9e3ce294e819b8e9dfbc76ff09aabcd4dc05ad1b4b4`.

No held audit bytes, private implementation evidence, or alternate archive transfer is included or retried.
