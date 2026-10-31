# Independent hand review: prescribed continuous crosscut reduction

Reviewer: dot (OpenAI), separate G3 continuation context. 31 October 2026, 01:02 UTC. Reviewed assessment SHA256 59fde3fd70ff45fb2507609cadefcc9b3cb9c94e110317dd599a6b2cfc45ccc2.

**Verdict: the scoped mathematical reduction is justified, conditional on the stated supplier theorem and the unimplemented transport/parameter adapters. No mathematical counterexample or missing topological hypothesis was found at this scope. This is NOT a compiled provider or an independent proof/axiom audit of the supplier.** No external source was executed and no Lean/lake build was performed.

## Supplier/source checks

All 128 files in JORDAN-SCHOENFLIES-CLOSURE.json match their exact byte counts, SHA256 and Git-blob hashes, totaling 3,958,343 bytes. The declared imports match source text; traversal from Schoenflies.JordanSchoenflies reaches exactly those 128 supplier modules with no missing supplier imports. This establishes source identity and declared closure completeness, not theorem correctness, execution acceptance or complete external/Mathlib provenance.

Read actual bodies/signatures in JordanSchoenflies, ModelCurve, Concatenate, GeneralCrosscut, JordanClosed, CrosscutCells, CrosscutAtMostTwo and the polygonal collar discharge. The relative Schoenflies endpoint has the stated prescribed boundary-homeomorphism conclusion; its local body supplies squareExtension rather than assuming it. ModelCurve.IsLoop.exists_homeomorph matches parameters on all of [0,1], not just the unparameterized curve sets. Its body uses the compact-interval quotient map and both loop injectivity directions. The exported declarations remain unqualified in this environment; the recorded Subarc-stage failure is not erased by these source inspections.

Immutable supplier: https://github.com/alonamaloh/schoenflies-lean/tree/05a43d29cde026618777db3d4e4316204ccca237

## Construction and exact hypotheses

1. Begin with a Jordan C, an actual simple p–q arc P, endpoints on C, interior P minus endpoints in inside C, and the ACTUAL IsCutPair arcs A1,A2. Do not start by demanding the supplier IsCrosscut structure on P: that structure already contains polygonality, precisely the premise being supplied by this reduction. A new theorem must spell out the weaker continuous hypotheses separately.
2. IsCutPair provides each boundary arc, union C and endpoint-only intersection. Since inside C is disjoint from C by its definition, P meets A1 (and A2) only at p,q. Reverse A1 to orient it q–p. The original P and reversed A1 satisfy Concatenate's endpoint/seam/intersection requirements and give a Jordan loop. Distinct endpoints follow from the injective arc parameterization; they are not an extra unproved network restriction.
3. The model upper-plus-left and lower-plus-right arcs have the required opposite endpoints, simple parameterizations and endpoint-only intersection. The displayed affine map sends NE to p and SW to q. With v=(p−q)/2, its linear columns are (v+Jv)/2 and (v−Jv)/2, so determinant is −||v||²/2≠0. Thus it is a plane affine homeomorphism. Affine images of those finite segment chains are polygonal. Constructing the corresponding Lean objects is an implementation obligation, not a missing mathematical existence argument.
4. Concatenating both source and target in the same order puts P and P* in their first parameter halves. The parameter-matching curve homeomorphism therefore maps P EXACTLY onto P*, not merely into the full target loop, and maps the complementary arc to Q*. At parameters 0 and 1/2 it fixes p and q. Relative Schoenflies extends this prescribed map on P∪A1. It is not an extension prescribed only on C, which would fail to control interior P.
5. Apply the SAME ambient H to C, P, A1,A2 and any surrounding drawing. Do not combine independently straightened edges as a new drawing. No other vertex or edge is fixed pointwise by this construction.

## Transport is sufficient for the exact supplier predicates

For a plane homeomorphism H, complement components transport exactly:

    H '' connectedComponentIn S x = connectedComponentIn (H '' S) (H x)

at the relevant x∈S, by maximal connected-subset characterization and H inverse. Set complements, unions, intersections and differences transport because H is bijective; closure transports because H and its inverse are continuous.

Boundedness is preserved in both directions for this finite-dimensional plane: a bounded set is contained in its compact closure; its continuous image is contained in a compact, hence bounded, image. Repeat for H inverse. This does not assert that an arbitrary homeomorphism on a nonproper metric space preserves boundedness. With the supplier's actual definition of inside as points in bounded complement components, these facts give H '' inside S = inside (H '' S). In particular they apply to C and both A_i∪P. This avoids selecting a new side by orientation.

Consequently H(C) is Jordan, H(P)=P* is a simple POLYGONAL arc with endpoints p,q, and its punctured arc is inside H(C). Every field of the supplier IsCrosscut is met. The transported A1,A2 meet all four IsCutPair fields; neither those arcs nor H(C) must be polygonal. JordanClosed.crosscut_theorem therefore applies. Its full output—exhaustion, disjoint/nonempty/distinct interiors, connected-component identification and the two labelled closure intersections—pulls back to the original C,P,A1,A2. Orientation reversal is harmless for these labelled set equalities; an oriented cyclic-order application must still track its convention.

## Collar and bigon limits

The inspected ArcCollar fields are open neighborhood, containment, neighborhood-minus-P equal to the union of two connected tracks, and closure incidence of K with both tracks. They do not demand metric width, differentiability or a straight-line retraction. All these fields transport under H inverse. Nontrivial compact preconnected K remains nontrivial compact preconnected under H, so the polygonal hasArcCollars supplier gives the claimed continuous collar where the stated endpoint/domain premises hold. The unused polygonality argument in crosscut_at_most_two is still part of its Lean signature; one cannot merely omit it without a new generalized theorem. The direct transformed-crosscut route avoids that interface mistake.

An edge plus a complementary simple cycle path supplies Q. Parallel-edge bigons satisfy the same two-arc endpoint-only condition; no three-vertex face theorem is used. A bridge has no such complementary graph path, so this graph-cycle selection does not supply its collar. This is a limit of this construction, not a proof that bridges lack collars.

Finite vertex stars, coherent rotations, repeated face-boundary visits at bridges/cutvertices, opened-tree contours, midpoint-tip accessibility, original taxon order and adjacent duplicated labels remain separate source joins. Fixing original endpoints is not fixing all these structures pointwise. The argument does not identify arbitrary syntax order with geometric order or close full NANUQ Lean.

## Status and novelty

Accept the proposal as a sound hand-level reduction to a stronger classical supplier, with exact source applicability. Do not label the 128-module closure or proposed new continuous theorem kernel-accepted. No historical novelty or original master closure is claimed. Next useful work is supplier qualification plus one explicit continuous labelled-crosscut adapter and its nonlinear component/inside/closure transport, not another conditional face consumer. The original accepted hand result remains unchanged.
