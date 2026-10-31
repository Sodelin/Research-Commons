# Original order interface and cap-port exterior route

Status: precise source-bound mathematical assessment, NOT a completed Lean provider.

## What the manuscript actually assumes

Manuscript §3 Theorem A: “Fix any outer-labeled planar embedding, and let C be its induced cyclic taxon order.” §5 A.4 uses the original outer-face traversal entering/leaving an attached component along its single bridge. Thus C is NOT an arbitrary taxon permutation and outer-face incidence alone is not its definition. The current TaxonOuterFace record contains no C field.

A direct formal definition can use darts (oriented occurrences of original edge IDs, including parallel edges), the cyclic local orders induced by the SAME continuous embedded vertex stars, and the outer boundary walk: reverse a dart, take the next incident dart in the consistent orientation; select the unbounded-face orbit. Read each degree-one labelled taxon on its unique excursion. Then C is that cyclic label sequence up to rotation/reversal. A bridge is traversed twice, once on each directed dart; parallel arcs remain distinct. This definition must not take an arbitrary rotation system as an additional admitted input. Existence, agreement with actual complementary faces, and the induced local star orders require proof for the given continuous embedding.

An alternative transparent geometric relation (candidate encoding, not assumed established) is a simple Jordan support curve through exactly the labelled leaf points, with all other points of the SAME graph drawing in its bounded region, whose taxon preimages occur in C order. Existence for the original class and equivalence to the above outer boundary traversal, including bridges and repeated non-leaf boundary vertices, would have to be proved before it could replace the manuscript premise. No opaque order certificate is introduced and no equivalence is claimed here.

Accordingly, the formal gate is partly missing definition and partly missing theorem. Merely adding arbitrary C to TaxonOuterFace is insufficient. Conversely, faithfully encoding the original induced-order premise is not by itself a strengthening, provided its equivalence is actually proved and the later cap/opening order transport is not included as an assumed field.

## Exact cap-port exterior-incidence route

Use the concrete cap geometry in PORT-PROVIDER-SEARCH.md. For each port p choose a global taxon x in the already proved nonempty portTaxa fibre.

* Outgoing port: cap tip is old bridge parameter 1/2; omitted tail is (1/2,1], leading to the bridge target side.
* Incoming port: cap tip is parameter 1/3; omitted tail is [0,1/3), leading to the source side. Fresh root2/3 and both retained incoming-port cap segments lie in [1/3,1], so the omitted tail is disjoint from both, including the fresh root.

GraphPortFibers identifies x with the appropriate bridge side. An actual original-ID path on that side connects the bridge endpoint to N.leaf x while avoiding that bridge. Bridge-component separation excludes blob vertices and all retained internal arcs. The faithful original curve incidence axioms then prove the path trace is disjoint from the cap. Its possible contacts with OTHER capped bridge prefixes must also be excluded using their inside-blob endpoint and the same bridge-side separation, not merely asserted from distinct edge IDs. The selected-switching bridge path is permissible only because it is explicitly an original-ID path; no switching-derived contour claim is used.

The union F of that path trace and the omitted half-open tail is preconnected, cap-disjoint, and contains the global taxon point; the new port tip lies in closure F. No positive-distance or polygonality premise is needed for this union. The original taxon point is absent from the cap (nonleaf blob, and new cap vertices are genuine bridge interior points). Drawing inclusion carries the original unbounded component into the cap complement, and original taxon closure membership plus RemovedPointMerge.old_face_subset_new_component puts it inside the component based at this absent taxon point. The preconnected F intersects that component, so F is contained in it. Consequently the cap tip lies in its closure and this component is unbounded. The component is the same one based at the original outside point because that point belongs to the old component.

This is a route to cap TaxonOuterFace, not to the missing C relation, bridge-fibre cyclic contiguity, adjacent opened hybrid pairs or the global composition theorem. Actual cap PlanarCurves construction, subset proof and the original-ID trace-disjointness arguments remain to implement. No new assumptions about old outside incidence of the hybrid-parent tips are inserted.
