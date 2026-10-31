# Correct geometry obligation: opened contour, not old-face membership of every new tip

Contributor: dot, 2026-10-31. This corrects an overstrong *gate description*, not a theorem statement or source definition.

## Exact source obligation

The review-draft manuscript, §5 Lemma A.1 (Ordered occurrence representation), says:

> Collapsing each pair recovers the embedding’s taxon order, up to rotation and reversal.

Manuscript source SHA256: `0afb086ad9ba6ef5d0514c168487dc2afa8774235ae24508d381360ed32f3989` (the existing 30 October review draft; no publication or full Lean acceptance of that manuscript is implied).

The immutable [structural audit, §2 assertions 1–3 and §2.3](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/cba23504ec7c63936ab60e5c3beb65d296c2e9c5/research/nanuq-all-level-2026-09-29/ALL-LEVEL-STRUCTURAL-AUDIT.md) states the same obligation: construct the actual opened plane tree T, prove consecutiveness in **T's cyclic tip order**, and recover the fixed original network's taxon order by collapsing each pair. The retained source was checked byte-for-byte against that public pin; SHA256 `ca00d9c4c7b84c6f9e0b856ce3f863530451763481591042f7f847c8fb4a26af`.

Thus the necessary master geometry gate is:

1. an actual contour of the surgically OPENED tree drawing, retaining the original incidences rather than an arbitrary redraw;
2. the two occurrences of each duplicated label are adjacent on that contour;
3. collapsing those adjacent pairs recovers the GIVEN original taxon circle C, up to its stated rotation/reversal convention.

The exact switching/occurrence and graph/syntax correspondences remain required alongside this geometry.

## What was too strong

Recent candidate prose described proving each newly opened hybrid tip's incidence with the **old graph's unbounded face** as a remaining necessary gate. That is stronger than the manuscript requires and must not be imposed as a new admission hypothesis. The new tips need the appropriate exterior/contour incidence in the OPENED drawing, not necessarily membership in the old graph's outer-face closure. The old `TaxonOuterFace` witness concerns the old labelled taxa; it cannot simply be applied to new tips, but the solution need not prove those new tips were already outer in the old graph.

This clarification supersedes that necessary-gate wording in the [continuous face-cycle candidate README](https://github.com/Sodelin/Research-Commons/blob/2f1ab023785ad3758e503039f7ebbddd331c1723/research/2026-10-31-nanuq-continuous-facecycles-candidate/README.md) and associated working updates. Their Lean source statements and scoped statuses are unchanged. Earlier sources and reviews are retained, not deleted or silently rewritten.

## Possible route, not an established theorem

Deletion/opening can enlarge the complement. A same-drawing component-inclusion argument, together with a proved nonseparation/contour theorem for the actual opened embedded tree, may establish new-tip exterior incidence while retaining the old taxa. This is a possible proof route, NOT a new accepted nonseparation or contour theorem. A drawing-subset transfer alone does not identify cyclic order, and connectedness or a one-face assertion alone does not prove adjacent duplicate blocks or collapse to the original C.

The original-blob connectivity and continuous face-cycle suppliers remain useful, for example for the existing bounded-face contour argument and incidence accounting. They are not discarded, and the old graph's outside-component relation may still be useful in a particular proof. It is simply not a mandatory new-tip membership premise.

No arbitrary child order/redrawing, new outer-face premise, scope narrowing, full original NANUQ Lean acceptance, or held-audit publication is introduced by this correction. Future compiler/reviewer requests must use the opened-contour/paired-adjacency/original-C obligation above.
