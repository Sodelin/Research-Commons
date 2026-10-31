# One-ended slit nonseparation: a narrower degree-one target

Status: hand construction / formalization route, not an accepted Lean theorem. It is not yet the actual graph face-orbit provider.

## Exact proposed lemma

Let C be a Jordan curve, Ω one of its complementary regions, and A a simple arc with endpoints q∈C and v∈Ω, such that A\{q}⊆Ω. Then Ω\A is path connected. This is a genuine one-ended slit, NOT a crosscut with two boundary endpoints. It does not promise a full endpoint star-normal-form chart.

## Doubling/folding construction

1. Choose c∈C distinct from q. Since A meets C only at q, c∉A. Map the Jordan boundary to a round circle with c a chosen circle point; then puncture/invert at that point, sending C\{c} to a line and Ω to the corresponding half-plane side with the exception specified next. For the bounded region this is a genuine half-plane. For the unbounded region the image is a half-plane MINUS one interior point a∞ (the missing image of infinity); that puncture must be retained. The compact arc A avoids c, so its image remains a compact simple arc in the CLOSED half-plane, touching its boundary line only at q' and avoiding a∞ when present.

   This step is a coordinate construction, not an arbitrary redraw: use prescribed Jordan–Schoenflies and an explicit circle-to-line map. If the supplier's square model is used first, the square/circle change can be the radial norm-comparison homeomorphism. Exact coordinate and image formulas still require a formal implementation. No assumption of endpoint polygonal accessibility is made, and no off-arc interior inversion centre is required.

2. Reflect A' in the line. The original and reflected arcs meet only at q'; concatenate them there. Their union S is one compact simple arc joining the two reflected free endpoints. The unconditional `arc_complement_poly` supplier joins any two distinct points of the intended half-plane domain minus A' by a simple polygonal connector avoiding S (equal points use the constant path).

Before folding in the unbounded-region case, arrange that the connector avoids BOTH a∞ and its reflection. For either of these finitely many points, take a small closed ball disjoint from the doubled arc, the connector endpoints and the other excluded point. If the connector meets its centre, replace the portion between its first and last visits to the ball by a two-segment detour through a noncollinear interior point. The boundary contacts exist by compact extrema; the detour stays in the ball and avoids its centre. Disjoint balls prevent reintroducing the other excluded point. No finite intersection count is required, and the resulting connector need not remain simple.

3. Fold the whole connector to the closed half-plane by (x,y)↦(x,|y|). This continuous map has preimage of A' exactly S, so the folded compact path still avoids A'. It may touch the line; this is not yet a path in the OPEN half-plane.

4. The folded path image and A' (together with {a∞} when present) are disjoint compact sets, hence have positive distance δ. Shift the folded path upward by ε with0<ε<δ/3. The shifted path lies in the open half-plane and still misses A'. Its endpoints are shifted from the original endpoints; connect each by the short vertical segment. Those segments also lie in H and stay within ε of their original points (which belong to the folded path), hence miss A'. This gives the required H\A' path, also avoiding a∞ in the exterior case. Pull back through the SAME coordinate map.

This proof avoids the false inference that global arc-complement connectivity alone is already a local face-return theorem. The half-plane folding and compact-clearance shift supply the relative domain control explicitly.

## Actual source applicability still owed

For an actual pendant tip, the incident-dart rotation is unique. What the source face-orbit theorem needs is the two-side return around that tip, not necessarily a prescribed full endpoint chart. The proposed slit lemma supplies this when an actual Jordan region contains the pertinent one-ended arc with exactly its attachment on the boundary.

For a nontrivial raw blob, the accepted continuous face-cycle theorem gives Jordan regions, so the lemma is potentially directly useful for a pendant port in that raw face. But after adding several slits the face is no longer a Jordan domain. The finite-attachment localization/iteration and the singleton/bridge-only source case must still be proved; they cannot be hidden by applying the lemma to an arbitrary connected open region. In particular this note does NOT assert that every actual leaf already comes with the required Jordan localization, nor that finitely many disjoint arc complements are connected merely because each single complement is connected.

Existing global `arc_complement`, inversion algebra and prescribed Jordan extension are real suppliers. The relative coordinate construction, slit lemma implementation, source localization, sector assembly and C-order identification remain explicit formal obligations. No additional Lean layer has been queued while the continued-arm candidate qualifies.


Correction history: the initial hand wording treated both regions as an unpunctured half-plane. The exterior image-of-infinity exception above was found during owner checking and corrected before publication/formal use. No accepted result depended on the omitted puncture.
