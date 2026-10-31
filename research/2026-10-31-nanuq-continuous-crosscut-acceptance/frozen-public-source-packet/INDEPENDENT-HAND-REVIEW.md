# Independent source-only review — 2026-10-31

OpenAI assistant, G3 reviewer context, for Nolan / Sodelin Research-Commons.

**Hand-reviewed compositions, UNCOMPILED.** This review does not claim a successful compiler run, audit publication, end-to-end source adapter, or full NANUQ theorem. No supplier code was executed. The three source hashes reviewed:

- GeneralRegionCrosscut.lean: e207e9360a034e5f4dda49cd5145a2953933605fa7dec9329bbe361653a29b0b
- PrescribedLoopAmbient.lean: 503d2bb6390e0df97c260715ae64badf18fe5e63f6eb8ae3a48e039dab66c8b2
- CycleArcStraightening.lean: 6da4678734b8a949892f8a3cc19a12d39473ed38c6cf87443c44beb41a6f62dc

Reviewed against supplier alonamaloh/schoenflies-lean at 05a43d29cde026618777db3d4e4316204ccca237, including actual declaration bodies/types in CrosscutCells, PolyArcRealize, ModelCurve, Concatenate, PolyPath, Polygonal, Curve and JordanSchoenflies. The specified proof-only compatibility variants do not change those endpoint statements.

1. **General region:** the opposite complementary region misses Ai union P, hence belongs to one Wi; its companion Vi is exactly the cell used by crosscut_cells. Jordan separation gives the required openness, connectedness and nonemptiness. Endpoint intersection hypotheses yield both union-Jordan premises and P-intersection subsets. Exhaustion uses polygonal P and open preconnected region only; collars are supplied internally by crosscut_components_exhaust_of_isPolygonal. Distinct exact components are disjoint. No polygonality of C is assumed. Exterior cells are correctly merely IsRegionOf of their new curves, not asserted both bounded.
2. **Prescribed loop:** parameter-matched subtype homeomorphism extends to one ambient map. Its pointwise equalities give every parameter-subset image, with both image-membership equality orientations correct. No independent maps for separate subarcs.
3. **Cycle arcs:** endpoint-only meeting makes the given oriented arcs into a loop; corresponding fixed square sides satisfy the same premises. Exact lower-half and upper-half image identities are valid, including their seam because f(1)=g(0). One extension consequently maps P to top union left and Q to bottom union right, sends the labelled endpoints p,q to NE,SW, and witnesses polygonality by [NE,NW,SW]. The argument uses neither a three-vertex assumption nor artificial separation of parallel-edge bigons.

The third candidate makes an affine endpoint-fixing normalization unnecessary for this route: endpoints may move to labelled square corners because the eventual conclusions are pulled back by this SAME map. It does not prove the stronger unused assertion H(p)=p, H(q)=q. Original labels are not changed by inverse transport.

Still required: formal composition for an actual continuous crosscut of the original boundary, transport of all supplier source premises, and exact component/closure pullback. Bridges with no complementary cycle arc, vertex stars, repeated contour visits, coherent rotations, original chosen geometric cyclic order and duplicate adjacency remain open. No Lean acceptance should be inferred before an exact-source compiler receipt.
