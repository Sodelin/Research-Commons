# Exact source object being opened: each admitted rooted CAP, with port labels

This is a source/API binding assessment, not a new geometric theorem.

For an original RootedBinary N, original nonleaf blob b and its proof hb, the existing source object is

`L_b := N.actualEveryNonleafRootedCapSource b hb`.

Its taxon/label type is `N.BlobPort b`, NOT the global label type X. A BlobPort is an ORIGINAL bridge edge ID incident to b in the original bridge quotient. `blobProjection b hb : X → BlobPort b` and positive `portTaxa` fibres are already separate source maps; their geometric interval order in the fixed original C is not supplied by the definition.

## Exact literal cap

`RootedCapVertex b` is the sum of original blob vertices, distinct port tips, and a fresh-root tag (inhabited only when b is not the original root blob). `RootedCapArc b` is the corresponding sum of original internal arc IDs, port arcs, and that fresh-root arc. The original internal arcs have both original endpoints in b and are not selected-switching edges.

Outgoing bridge ports are replaced by pendant port arcs at their original inner endpoint. A nonroot blob has one incoming port: a fresh binary root is inserted on that incoming-port attachment, with one arc to the port tip and one to the original blob entry. Thus the cap is not merely a subset of the global edge type; these new tags and endpoint incidences must be respected by a geometric realization.

The actual `actual_admitted_cap_hybrid_child_is_taxon hg b hb` supplies the opened-tree hleaf premise from the original GalledDetour hypothesis. `actual_galled_cap_opens_to_tree` then proves that this cap's literal opened graph is a tree. These are existing source declarations, not a new blanket hleaf assumption on the full global network.

## Exact opening of the cap

Apply `openedHybridGraph` to L_b. Its vertices and edges are each `Skeleton + HybridParentOccurrence` OF L_b. Every hybrid-parent occurrence corresponds to a cap arc entering a cap hybrid and becomes a distinct pendant edge to a distinct new tip. The hybrid vertex and its pendant PORT-taxon child are absent from the skeleton. Both incoming occurrences remain as separate truncated stubs; they are not merged into one edge.

`openedOriginalEdge` maps an opened edge to L_b's `RootedCapArc b`. It does NOT directly map every opened edge to an original global E: cap port arcs and the inserted-root arc have their own source tags. Internal cap arcs retain original global IDs. An exact physical implementation must therefore first realize the rooted cap in the given original drawing, and then realize the opening by restricted arcs of that SAME cap drawing.

A concrete candidate geometry is to place port tips and, when needed, the fresh root at distinct parameters on their original bridge arc, retaining/reversing the appropriate subpaths; then place each opened hybrid-parent tip at an interior parameter of its cap arc and keep the parent-side prefix. This is a candidate construction, NOT yet a verified PlanarCurves provider or a proof of outside-face/order preservation.

## Consequences for the remaining proof

- Do not treat both incoming-edge truncations, removal of the original hybrid and removal of its port-child as a proved sequence of connected full-global-graph edge deletions.
- Do not substitute global taxa for local portal labels. The global TaxonOuterFace witness refers to N.leaf:X→V; it does not automatically give TaxonOuterFace for the new cap leaves indexed by BlobPort.
- A geometric cap/port outer-face provider, actual local port contour and its correspondence with the original global C remain source obligations.
- Pair adjacency concerns duplicated PORT labels in the opened cap; the finite receiver and later global mass/composition maps use those labels and their positive global-taxon fibres.
- The required target remains the OPENED cap-tree contour with paired adjacency, collapsing to its correct local port order and then the GIVEN original global C. New tips need not be outer in the old graph.

The general removed-frontier-point merger currently being checked can help only after actual old/new drawing inclusion and actual frontier incidences are proved for this literal surgery. It does not assert face exhaustion, a dual-tree contraction, cyclic order or pair adjacency.

Successor status (31 October2026): RemovedPointMerge completed its local kernel check with three standard-axiom named receipts; its actual source application remains pending. The subsequently reviewed literal cap PlanarCurves/subset source candidate is public at b06850f7fcfbddc228447f835d4628c30fc2c41b, research/2026-10-31-nanuq-literal-cap-drawing-candidate. It is explicitly UNCOMPILED, not a geometry/contour acceptance. Earlier “currently being checked” wording records the preceding checkpoint.
