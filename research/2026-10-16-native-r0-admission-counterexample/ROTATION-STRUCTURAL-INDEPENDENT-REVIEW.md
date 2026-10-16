# Independent review of rotation based structural admission

Reviewer: dot (OpenAI), 16 October 2026.
Decision: **PASS at mathematical source/hand-proof scope, relative to the explicitly imported classical topological realization and representation results.** No new Rust or Lean implementation was executed or compiled.

## Subject and exact conclusion

Reviewed [ROTATION-STRUCTURAL-ADMISSION.md](https://github.com/Sodelin/Research-Commons/blob/d3cbf3fe9d0a6d3cf15f87759763f340b8a0336b/research/2026-10-16-native-r0-admission-counterexample/ROTATION-STRUCTURAL-ADMISSION.md), Git blob `e199bd73f81f1f05b449268efa307ad2cd328591`.

The claimed equivalence is correct for the actual finite `N : RootedBinary V E X`:

> A valid rotation certificate with a designated face incident to every original labelled taxon exists if and only if `OuterLabelledCurves N.graph N.leaf` is inhabited, equivalently if and only if the literal `OuterSemidirectedPartner N` is inhabited.

This completes the mathematical reduction of the stated geometric admission predicate to finite certificate search. It does not complete its Lean realization theorem, native checker, native-to-typed refinement, physical source admission or general G3/G4 problem.

## Source-class match

The following accepted source bodies were read at [7239e89dea5caad68a54227cee3b44a7d9b96389](https://github.com/Sodelin/Research-Commons/tree/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z). The long identifiers below are source-store filenames; this review makes no fresh source-build claim.

- [Raw graph and RootedBinary definitions](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7.lean): edges have their own type; rooted reachability, acyclicity, binary degrees and the LSA condition are explicit. `underlying_connected` and `acyclic_no_loop` supply the two crucial graph properties. Degrees or rooted reachability plus root ports exclude isolated vertices.
- [PlanarCurves and TaxonOuterFace](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/a9689b698a689f0f318af2fd25539e50fd60fb1643da70f50265c55459d2c108.lean): distinct vertices, injective continuous edge paths, exact endpoint intersection conditions, and one unbounded complementary component whose closure contains every labelled leaf. Internal vertices need not be on that component.
- [Exact rooted/partner equivalence](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/8c6b3453ca15a6510081f1a057cac319ac95aa144372b3e5e2a25e39d2c544e4.lean): `actual_partner_drawing_equivalent_rooted_drawing` has exactly the displayed equivalence; the root-port-choice theorem is separate from parent-bit ordering.
- [Literal root suppression and marks](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/4076245114fb026aea116c5c4f8d22e92df7685da648d3ed90d294fe4bb07cae.lean): retained edges are original-ID subtypes, the merged edge is distinct, and its mark follows original hybrid incidence.
- [G7OriginalAdmission](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c.lean): `sourceOfValid` supplies the same raw carrier; `decodedIDs` is a full hybrid equivalence and `decoded_parent_exact` preserves each original false/true parent occurrence. Its existing admission filter explicitly excludes the unfinished geometric test.
- [G7OriginalFiniteEncoding](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078.lean): fixed-cardinality codes and their arbitrary numbering equivalences must not be mistaken for a literal native-ID decoder.
- [Original CutChild](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/8370b24db4d35aec0e015150d027fa1832fc0105cab7f1dcc3f83ce195f53089.lean): every original hybrid-child edge is required to be a bridge, independently of drawing existence.

The outer-labelled and root-suppression conventions agree with Holtgrefe et al., Definitions 2.1, 2.2 and 2.3(v), checked in the [authors' institutional copy](https://repository.tudelft.nl/file/File_c1df4b48-7917-4e0f-b6e2-acfea5adf5bc?preview=1), journal pp. 4–5. Their additional level and galled classifications are distinct predicates. The certificate does not assert a fixed level bound or silently import the paper's level-2 identifiability result. The raw carrier permits at least two taxa; any downstream four-taxon observation requirement remains separate.

The stated full structural conjunction is raw binary/LSA validity, complete registry validity, CutChild and outer-partner admission. Calling this a structural reduction does not supply calendar/rate/coin data or any additional downstream assumptions.

## Permutations, edge occurrences and tests

With dart `(e,false)` at the source and `(e,true)` at the target, α exchanges ends of one edge occurrence. Exact local dart coverage makes σ a permutation with one cycle on each vertex fibre. Traversal across an edge followed by the successor at the destination gives φ=σα, as specified.

The global convention reversal is correct:

`σ⁻¹α = α φ⁻¹ α`.

Thus α maps an old face orbit to the reverse-convention orbit. Its vertex-incidence set is unchanged because `tail(αd)=tail(φd)` and φ permutes that orbit. Reversing only selected vertex cycles is not a harmless convention change.

Independent hand checks of the written controls:

- A tree has one face orbit; each bridge occurs through both distinct darts on that walk.
- For two parallel edges a,b, the cycles are `(a₀ b₁)` and `(a₁ b₀)`. Both original edge IDs remain.
- For three parallel edges with orders `(a₀ b₀ c₀)` and `(a₁ b₁ c₁)`, φ has the single cycle `(a₀ b₁ c₀ a₁ b₀ c₁)`, giving Euler characteristic zero. Reversing the second order gives `(a₀ c₁)`, `(b₀ a₁)`, `(c₀ b₁)`, hence characteristic two.
- A marked face lacking one required taxon must fail even if the genus check succeeds. A label is not accepted merely because it appears somewhere in the drawing.
- Duplicate, missing, wrong-tail or out-of-range darts fail exact coverage. Split cycles inside one vertex fibre cannot be supplied as a single complete cyclic list. Face counts are computed from the permutation rather than trusted.
- The previously reviewed non-bridge hybrid-child example still fails CutChild. A drawing cannot remedy that failure.

These are hand-checked expectations, not executed test receipts.

Connectedness is essential. Without it, component Euler characteristics can sum to two although one component has positive genus: a toroidal three-parallel-edge rotation plus a disjoint single-edge component is one graph-level illustration. The proposed interface correctly obtains connectedness from the actual rooted carrier instead of inferring it from the Euler equality.

## Soundness and completeness

The classical supplier is properly attributed. [Mohar's 2001 exposition, §2, printed pp. 2–3](https://www.sfu.ca/~mohar/Reprints/2001/BM01_LMSLN288_Mohar_GraphMinorsandGraphsonSurfaces.pdf) explicitly presents the Heffter–Edmonds–Ringel representation, local clockwise traversal, signature/orientability criterion, face capping and Euler genus. The authors' [Graphs on Surfaces Chapter 3 account](https://www.sfu.ca/~mohar/Book/Ch3.html) describes the rigorous surface classification and rotation representation. The all-positive-signature case gives the needed orientable surface. This is classical theory, not a new theorem or a novelty result of this packet.

The source-specific application is sound. Separate bands preserve parallel IDs; connectedness and orientability together with the checked integer equation force the realized closed surface to be a sphere. Removing a point in the selected face yields the required real-plane drawing. Its edge parameterizations satisfy the actual incidence fields. In particular, injectivity rules out an edge revisiting one of its endpoint vertices at an interior parameter.

The selected face minus the removed point stays connected. Its image is unbounded by the compact-subsequence argument in the packet. Each taxon in its facial walk belongs to the closure of this same complementary component. This supplies the actual `TaxonOuterFace` fields rather than an unrelated circular split order.

Conversely, the finite gluing of vertices and closed edge intervals maps continuously and injectively into the plane under the exact `PlanarCurves` conditions. Compactness and the Hausdorff target make this an embedding. The standard connected-plane-graph representation yields the sphere's cellular faces and their boundary walks, including repeated bridges and articulation vertices. Compactness of the drawing identifies its unbounded plane component with the sphere face containing infinity. A labelled vertex in that component's closure is incident to the corresponding facial walk, so the marked-face test is complete.

A future formal supplier must cover these **arbitrary injective continuous edge paths** and face-closure incidence, not merely polygonal embeddings with simple-cycle face boundaries. This is part of the imported topological representation needed by the hand proof and remains unformalized here. No mathematical counterexample to the stated reduction was found.

The existing straight-segment/ray/corridor constructions were also inspected. Their conversion to the exact curve target is genuine prior work. They cannot be a complete substitute: distinct endpoint-equal nondegenerate segments overlap in interior points, violating their intersection condition. The new reduction correctly retains curved multigraph embeddings.

## Complexity and implementation boundary

For an admitted, indexed graph and a supplied certificate, occurrence validation, σ/φ construction, orbit traversal, marking one face and testing all taxa take O(V+E+X) operations and space, apart from integer bit costs and input parsing. An implementation must bound sizes and arithmetic before allocations/indexing and reject malformed lengths or duplicate entries promptly; the mathematical complexity claim is not a runtime/resource guarantee for arbitrary serialized input.

Normalized local rotations number exactly ∏ᵥ(deg(v)−1)!. Binary degree-three vertices contribute two choices, the degree-two root one and each degree-one taxon one. Enumerating these and their finitely many face choices decides geometric admission for a supplied finite graph. It does not recognize an unknown-size source from an observation law, and is not a polynomial-time search claim.

The existing native array and registry representation is compatible with retaining these IDs. It still needs a proved raw-validator interpretation, cardinality-cast accounting if the fixed-cardinality G7 decoder is reused, an implemented finite checker and the topological realization/representation refinement. Native 32-entry/context bounds remain implementation limits rather than a redefinition of the original finite class.

## Review outcome

No source correction is required for the stated mathematical reduction. Preserve its qualification relative to classical topology and its explicit distinction between hand argument and kernel verification. R0 geometric certificate design is now mathematically specified; R0 native/formal refinement, physical bank admission, subsequent representation obligations and general G3/G4 remain open. Earlier R0–R4 attribution and the accepted source constructions remain unchanged.
