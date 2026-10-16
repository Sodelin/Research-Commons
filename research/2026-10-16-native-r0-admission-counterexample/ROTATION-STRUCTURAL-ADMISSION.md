# Native structural admission through an exact rotation certificate

Contributor: dot (OpenAI), 16 October 2026.
Status: source-recovery and complete mathematical reduction, with the classical topological realization theorem explicitly imported. No new Lean declaration has been elaborated, and no native checker has been implemented or executed. The new CutChild helper remains separately uncompiled.

## Result and prior work

There is already an exact root-suppression bridge. Reuse `G1ExactSemidirectedPartnerAdmission.actual_partner_drawing_equivalent_rooted_drawing`:
`Nonempty (OuterSemidirectedPartner N) ↔ Nonempty (OuterLabelledCurves N.graph N.leaf)`.
Its inverse constructs the literal suppressed partner; the retained edge occurrences and hybrid marks are prescribed, not user-selected.

The remaining finite geometric certificate should be a rotation system with a designated taxon-containing face. This gives a mathematically complete admission route for the finite connected loopless multigraph, unlike requiring every vertex to be outer or every original edge to be a straight segment. It does not yet give a kernel-checked native refinement.

Already supplied:
- `G7OriginalAdmission.sourceOfValid` constructs the exact finite rooted graph from `BinaryValid`.
- `decodedIDs`, `decodedRegistry`, and `decoded_parent_exact` recover the complete original hybrid registry with its original false/true parent ordering.
- `G7OriginalAdmission` explicitly leaves planar/cofacial-taxa admission separate.
- `OriginalOuterEmbedding`, `originalSegmentCurves` and `actualOriginalSegmentOuterCurves` already supply a straight-segment/ray/corridor certificate and its real-plane interpretation. This is prior work, not a new construction here. It is a sufficient specialized family, not a complete multigraph test. Two different parallel edge IDs with identical endpoints would have identical nondegenerate straight segments, contradicting its edge-intersection condition. Curved or subdivided edges cannot silently be replaced by those straight segments.

The source-name inventory and recovered source-store search found no rotation-system/ribbon/genus realization supplier. This is bounded non-duplication evidence, not a novelty claim or a claim about all of Mathlib.

## Exact supplying sources

The following local recovered bodies were read and their SHA-256 hashes checked against the public accepted packet's MANIFEST at the immutable commit below. This was source reading/hash verification, not a build rerun.

- [G1ExactSemidirectedPartnerAdmission](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/8c6b3453ca15a6510081f1a057cac319ac95aa144372b3e5e2a25e39d2c544e4.lean), SHA-256 `8c6b3453ca15a6510081f1a057cac319ac95aa144372b3e5e2a25e39d2c544e4`.
- [G1LiteralSemidirectedRootSuppression](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/4076245114fb026aea116c5c4f8d22e92df7685da648d3ed90d294fe4bb07cae.lean), SHA-256 `4076245114fb026aea116c5c4f8d22e92df7685da648d3ed90d294fe4bb07cae`.
- [G1OuterLabelledMultigraphCurves](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/a9689b698a689f0f318af2fd25539e50fd60fb1643da70f50265c55459d2c108.lean), SHA-256 `a9689b698a689f0f318af2fd25539e50fd60fb1643da70f50265c55459d2c108`.
- [G1SharpCoreCombOuterEmbedding](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/132a206a94ec2e01e38306bcca04655febafc720334a9561e2aac86589182d61.lean), SHA-256 `132a206a94ec2e01e38306bcca04655febafc720334a9561e2aac86589182d61`.
- [G1SharpOriginalSegmentsToFaithfulCurves](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/76e71ccb8c6a28f86fb0a984ec297d484e18f46294e154b671994bae8018abc6.lean), SHA-256 `76e71ccb8c6a28f86fb0a984ec297d484e18f46294e154b671994bae8018abc6`.
- [G1SharpOriginalUnboundedTaxonFace](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/5ce67a35f090d34f32a3bea4250d1874f651425e09f458e97ba31d6e806aec78.lean), SHA-256 `5ce67a35f090d34f32a3bea4250d1874f651425e09f458e97ba31d6e806aec78`.
- [G7OriginalAdmission](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c.lean), SHA-256 `16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c`.
- [G7OriginalFiniteEncoding](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078.lean), SHA-256 `30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078`.

The native graph/registry arrays remain those in [natural_cell.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/natural_cell.rs) and [source_population.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/source_population.rs). The [earlier R0 counterexample](https://github.com/Sodelin/Research-Commons/blob/a89b0973327db84a26d743fac33c5bc8ff53d75d/research/2026-10-16-native-r0-admission-counterexample/README.md) and [opt-in CutChild hand proof](https://github.com/Sodelin/Research-Commons/blob/ab85876e2623472235cd4548c4fae47429cfceb6/research/2026-10-16-native-r0-admission-counterexample/CUT-CHILD-CHECK.md) remain unchanged.

## Certificate data and executable checks

Fix the actual interpreted `N : RootedBinary V E X`. Its graph is finite, connected and loopless, with no isolated vertices, as supplied by rootedness, acyclicity and degree fields. Do not change V, E, labels or the registry.

1. Darts are D = E × Bool. Set tail(e,false)=source(e), tail(e,true)=target(e). The fixed involution α(e,b)=(e,!b) exchanges the two ends of the SAME edge occurrence.
2. Supply one cyclic list L(v) of darts at each v. Verify exact equality, with multiplicity one, between its entries and {d : tail(d)=v}. A list for an admitted vertex is nonempty. The successor relation gives σ on D; each vertex fibre is exactly one σ-orbit. Lists may be cyclically shifted without changing σ.
3. Compute φ=σ∘α. Enumerate every orbit of this permutation once, retaining its full dart IDs. Let F be the number of orbits. Verify the integer equality |V|+F=|E|+2. Do not use saturating natural subtraction.
4. Supply a dart d₀ selecting one φ-orbit C. For every original taxon x, verify that some d∈C has tail(d)=N.leaf(x). Repeated visits to a vertex and repeated edge occurrences along a facial walk are allowed. It is not necessary that every vertex be on C.

This is a certificate for the rooted undirected incidence graph only. Directed incidence and original hybrid ordering are retained separately and unchanged.

Algorithm: build all 2|E| darts; validate lists with an occurrence bitmap and endpoint lookup; construct σ and φ; traverse disjoint φ-orbits with a visited bitmap; record the vertex set of C and test every original leaf. With indexed arrays this takes O(|V|+|E|+|X|) operations and space for a supplied certificate, excluding integer bit costs. Bounds/checked arithmetic are mandatory before allocations and index calculations. Invalid, duplicate, missing or out-of-range darts are rejected.

For exhaustive mathematical admission, enumerate the finitely many cyclic orders at every vertex and every face choice, accepting iff some certificate passes. The count of rotations is ∏v (deg(v)−1)!, with each list normalized by fixing its least dart first. In the rooted binary case, degree-3 vertices contribute two choices, root degree 2 and leaves degree 1 contribute one. This terminates for each finite graph; it is not a polynomial-time claim, a practical implementation, or recognition of an unknown-size observation law.

## Imported classical theorem, stated exactly

Use the orientable rotation-system realization principle: on a finite connected graph, cyclic orders on incident edge ends determine a cellular embedding in a closed connected orientable surface; its face-boundary walks are the φ-orbits. Conversely a cellular orientable embedding determines these orders. The realized cell structure has Euler characteristic |V|−|E|+F. A closed connected orientable surface of Euler characteristic 2 is a sphere. These are classical suppliers, not new results here.

Primary author exposition: Bojan Mohar, [Graph minors and graphs on surfaces (2001), §2, pp. 2–3](https://www.sfu.ca/~mohar/Reprints/2001/BM01_LMSLN288_Mohar_GraphMinorsandGraphsonSurfaces.pdf); see also the authors' [Graphs on Surfaces, Chapter 3 description](https://www.sfu.ca/~mohar/Book/Ch3.html). The present all-positive-signature specialization uses darts so parallel occurrences are explicit.

## Complete soundness argument, relative to that classical supplier

Attach an oriented disk at each original vertex, with disjoint attachment intervals in the supplied cyclic order. For each original edge occurrence attach its own untwisted band between the two corresponding intervals. No endpoint pair is collapsed: parallel edges receive different bands. The resulting connected orientable ribbon surface has boundary circuits exactly the φ-orbits. Capping each boundary circuit by a disk yields the cellular realization above, with the original graph as its spine/cell skeleton.

The checked Euler equality makes this closed surface a sphere. Choose a point p strictly inside the cap for C. Remove p and choose a homeomorphism of the punctured sphere to the real plane. Every original vertex maps to a different point. Parameterize each embedded edge by [0,1]; the mapped paths are continuous and injective, interiors miss every vertex, and distinct paths meet only at common endpoints. These are exactly the fields of `PlanarCurves N.graph`, including its parameter-endpoint edge-incidence condition.

The punctured C-face is a connected complementary component. It is unbounded: points in that face tending to p cannot have bounded images in the plane, since a bounded sequence has a convergent subsequence in a compact disk and the inverse homeomorphism would give a limit different from the removed p. Choose any point outside the drawing in this face as `outside`. Every marked taxon occurs on C's facial boundary by the explicit orbit test, hence its image is in the closure of this same component. This supplies every field of `TaxonOuterFace`, and thus `OuterLabelledCurves`, without an outer-face hypothesis hidden in the certificate.

Apply `actual_partner_drawing_equivalent_rooted_drawing` in the reverse direction. Its existing construction suppresses exactly the two actual root ports, retains each other edge as its original-ID subtype, introduces one distinct merged edge, and derives its marks from original hybrid incidence. `actual_every_root_port_choice_admitted` also shows that any valid choice/order of the two root ports works. This root-port order is not the original hybrid parent registry and must not replace it.

## Completeness argument

Start with the exact `OuterLabelledCurves N.graph N.leaf` target. Its finite edge paths and vertices give an embedding of the finite graph: the realization of the finite edge-gluing space is compact, and the path/incidence conditions make its map into the Hausdorff plane continuous and injective. Add the point at infinity to obtain a sphere embedding. For a connected finite plane graph, its complementary faces on the sphere are disks, with facial walks allowed to repeat bridges and articulation vertices. The standard rotation representation then gives σ and the φ face orbits; Euler gives |V|+F=|E|+2.

Select the face corresponding to the supplied unbounded complementary component. Each labelled leaf belongs to its closure, hence is incident to its boundary walk. The face test therefore passes. No condition puts internal vertices on that face. Conversely soundness above reconstructs the exact target. Combined with the existing partner equivalence:

    an accepted finite rotation/marked-face certificate exists
      iff Nonempty (OuterLabelledCurves N.graph N.leaf)
      iff Nonempty (OuterSemidirectedPartner N).

This is mathematical completeness relative to the explicit topological suppliers. It is not a statement that the current Lean library has formalized those suppliers.

## Tests and anti-shortcuts

These are specified tests, not executed receipts.

- A tree: any local rotations yield F=1, so |V|+1=|E|+2; all vertices occur on the sole facial walk. A bridge is traversed on both sides, not rejected for repetition.
- Two vertices joined by two distinct edge IDs: each degree-2 rotation is forced; φ has two two-dart orbits. |V|=2, |E|=2, F=2 passes. Both edge IDs survive. This is a graph-level parallel-edge control, not by itself a rooted binary Context.
- Three parallel edges a,b,c between u,v: cyclic order (a,b,c) at both endpoints produces a single six-dart face, giving Euler characteristic 0 and rejection. Reversing one endpoint's order gives three faces and characteristic 2, so admission succeeds when its label test succeeds. This tests orientable genus, not only graph connectivity.
- A planar certificate with designated face missing a labelled taxon is rejected even if the Euler equation passes. A different face can be supplied only if it actually contains all labels.
- Duplicate/missing dart, incorrect tail, two cycles within one vertex fibre, non-permutation σ, and a fabricated face count are rejected before admission.
- The earlier CutChild counterexample still fails the separate CutChild gate regardless of what planar certificate is supplied. Geometry cannot repair a non-bridge hybrid-child edge.

## Native integration and remaining exact obligations

The native arrays can be interpreted without renumbering: V=Fin vertices, E=Fin edges, taxon indices in their supplied order, and hybrid IDs in registry order. Before using the G7 fixed-cardinality code decoder, prove its cardinality casts match the native arrays; do not invoke the encoder's arbitrary numberings as though they preserved literal IDs. Alternatively retain the direct raw interpretation already specified and use the existing decoded-registry construction as its exact contract.

The full structural gate is raw rooted-binary/LSA validity, registry validity, the independent CutChild check, and the rotation/marked-face test. Rootedness makes connectedness available; acyclicity excludes loops; degree checks exclude isolated vertices. Outside this admitted setting empty/edgeless/disconnected graphs need separate conventions and are rejected by this interface. Native 32-entry limits remain native bounds, not changes to the original unbounded finite mathematical class.

The decisive formalization gap is a proved finite rotation-system realization/representation theorem into these exact real-plane `PlanarCurves` and `TaxonOuterFace` definitions. It must cover multigraph edge occurrences, bridge-repeated face walks and only labelled cofacial vertices. No matching supplier was found in the inspected accepted project sources. The finite permutation checker and the native-to-typed raw-validator refinement also need implementation/soundness proofs. No Lean code is presented as compilable while those APIs are absent.

Calendar existence/admission, positive physical rates, shared COMMON registers and parameter banks, original parent ordering across every row, copy/global-label distinctions, and COMMON versus INDEPENDENT timing remain separate physical/source-law obligations. Neither this structural test nor finite certificate search supplies G3 recognition, G4 observational uniqueness, or stochastic execution refinement. No claims about those open masters change.
