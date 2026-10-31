# Literal cap port exterior — source candidate

Status: self-reviewed mathematical/source candidate, **UNCOMPILED**. No Lean acceptance is claimed for these four new modules. They use the accepted literal cap variant 9517bd6a, not either failed cap variant. Full NANUQ remains open.

## Exact intended endpoint

For the original `RootedBinary N`, its faithful original `PlanarCurves D`, a nonleaf original blob `b`, and the original `TaxonOuterFace D N.leaf`, construct

`TaxonOuterFace (actualRootedCapCurves N D b hb) (N.actualRootedCapLeaf b)`.

The original embedding is retained; no redraw, star/collar certificate, all-vertices-outer condition, extra face premise, or cyclic order premise is added. Local labels are actual `BlobPort b`, not global taxa X. The output exterior basepoint is the SAME original exterior basepoint.

## Actual bridge-side support

Fix a port p with original bridge ID e. Near vertices are those reachable from the original inner endpoint without e. All vertices in the original blob lie near by `sameBlob_avoids_bridge` applied to equality in the original blob quotient. For another port q, its inner endpoint is near and its different original bridge ID crosses from that endpoint without using e. Thus BOTH q endpoints lie near. Internal original cap edges have both endpoints near as well. No selected-switching order assertion enters.

`sideTrace` includes original points of a vertex set and full original arcs whose two endpoints belong to that set. Faithful original vertex/edge incidence implies disjoint vertex sets have disjoint traces. An original arc not wholly in a side can meet its trace only at an endpoint belonging to that side. This explicitly keeps parallel IDs and does not quotient to a simple graph.

## Exact retained intervals, including incoming root segment

The literal cap drawing lies in the near trace plus the following retained portion of e:

- outgoing p: parameter `[0,1/2]`, with cap tip at1/2;
- incoming p: parameter `[1/3,1]`, comprising root-to-port `[1/3,2/3]` and root-to-entry `[2/3,1]`, with cap tip at1/3 and fresh root at2/3.

Other port/root arcs lie in the near trace unless their original carrier is exactly e. In the latter incoming case the root arc is explicitly retained; it is NOT accidentally deleted or counted as an omitted tail. `CapTrace` proves this bound by the actual cap point and arc definitions, not by a graph-isomorphism assertion.

The opposite vertex trace is disjoint from that bound. The omitted tails `(1/2,1]` (outgoing) and `[0,1/3)` (incoming) are also disjoint from the cap bound. They contain the respective far original endpoint, are preconnected continuous images of half-open unit intervals, and their closures contain the actual cap tip.

## Actual port-fibre path and component transport

Surjectivity of the original `blobProjection` supplies a global taxon x in p's actual fibre. The original `GraphPortFibers` target/source-side equivalences give an original-ID `ReachWithout e` walk from the far endpoint to `N.leaf x`. Each vertex of that walk is outside the near side (otherwise e is not a bridge), and each used edge has both endpoints outside. Consequently the ENTIRE geometric walk is disjoint from the literal cap, not merely its vertices.

The old global taxon point is absent from the cap and lies in the closure of the old exterior component. The accepted removed-point lemma puts that old component in the new component based at this taxon point. Since the original exterior basepoint belongs to the old component, the new component equals the cap complement component based at the SAME original exterior point. Propagating along the original-ID far-side walk puts the far endpoint in it. The omitted preconnected tail is therefore in it, and the actual port tip belongs to its closure.

The old exterior component is a subset of this new component by the accepted literal drawing-subset theorem, hence the new component is unbounded. This supplies one common outer face for every actual local port.

## What this does not prove

No geometric contiguity of global port fibres, port circular order, agreement with original given C, opened-tree contour, adjacent hybrid copies, face exhaustion, or global NANUQ theorem is concluded. The exact original C-compatibility encoding and transport remain separate obligations. Global TaxonOuterFace alone contains no arbitrary C field.

## Static checks / evidence

The four files contain no `sorry`, new `axiom`, unsafe evaluation, or certificate assumption. Their external declarations were checked against retained full original G1 and original graph/cap source bodies; interval closure and connected-component equalities were checked against the pinned Mathlib source. This is static source review, not elaboration or an independent kernel replay. No local full-provider build or duplicate compiler job was run.
