# Independent continuous face-cycle candidate source review

2026-10-31. Separate AI-assisted research review. **Hand/source ACCEPT; UNCOMPILED.** No compiler or supplier execution.

Exact candidate: ContinuousFaceCycles.lean, 9,342 bytes, SHA256 1a855b03925c4da0fc4e43ad7efe921c3f713e243d64ff278bf73c7406e5da73. Compared with pinned upstream FaceCyclesProof SHA256 46902b10c30553fd56099fcc5e1f491391f2d9596631ddd4f2f4284ba5721a70, and inspected the actual qualified JordanClosed theorem and existing HasFaceCycles/IsTwoConnected definitions.

The retained ear-decomposition argument has the same finite graph, actual IsDrawing, and IsTwoConnected hypotheses. It concludes the existing HasFaceCycles for the SAME drawing; it neither redraws nor supplies a rotation/cyclic order. The upstream ear guards remain: distinct endpoints in the old subgraph, internal vertices outside it, and genuinely new edge IDs (or the unchanged-union alternative).

The analytic replacements are justified at source level:
- Actual cycle_isJordanCurve plus the qualified unconditional Jordan theorem supplies cycle separation without polygonality.
- component_region projects the accepted continuous_crosscut_region decomposition/components, retaining the original two cut arcs and selected region (inside OR outside).
- In the cut-face branch, split arcs, exact endpoint-only intersection, and ear-interior containment are derived as in the original proof. The continuous supplier consumes these exact guards. Spliced cycle separation uses the SAME restricted drawing. An untouched face is carried through the same disjointness argument.

The cycle-graph base helper assumes only the actual IsCycleThrough witness and drawing. There is no three-vertex guard: a genuine two-edge parallel bigon can use this helper. This does not imply every small graph is a cycle. The final ear-decomposition theorem retains supplier IsTwoConnected, whose definition explicitly requires at least three vertices, connectedness and connected vertex deletions. Bigons are not silently promoted to that class.

No assumed CrosscutSplitsRegion, polygonality, new collar, prescribed order or face-cycle conclusion remains as an input. Upstream authorship, immutable pin, modification notice and Apache-2.0 attribution are retained. This is a derivative formal adapter for the standard face-cycle theorem, not a graph-theory novelty claim.

Acceptance is conditional on successful compilation against the specified already-qualified suppliers and exact named type/axiom receipts. This review does not establish raw original-network source admission, source-label/taxon order, duplicate-tip outside-face incidence, adjacent-copy opening, bridge/vertex-star assembly or full NANUQ closure. No held supplier audit or large payload is part of this candidate review.
