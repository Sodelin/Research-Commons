# Actual original-edge trivalent star — UNCOMPILED candidate

Contributor: dot, 2026-10-31. This is a source-bound formalization candidate, not a new topology novelty claim or a Lean acceptance. No compiler has been invoked for these eleven modules. Existing scoped providers are reused at immutable hashes; their full audit summaries are not independently reconstructed here.

## Exact endpoint

`Nanuq.ActualStar.actual_binary_trivalent_star` takes the ORIGINAL finite `SourceNetwork.RootedBinary N`, the SAME FULL `G1OuterLabelledMultigraphCurves.PlanarCurves N.graph`, a vertex v, and three distinct ORIGINAL edge IDs incident at v. It derives exhaustion from the existing original binary incidence bound. There is no extra collar, local radius-once condition, polygonality, embedding, cyclic order, face certificate, or no-loop premise.

It returns one ambient plane homeomorphism H, a radius ε>0, and q with q_y>0 and ε<‖q‖. H sends the original vertex to zero. The image of the WHOLE original drawing (through the existing faithful coordinate equivalence), intersected with the ε-ball, is exactly the horizontal line together with segment [0,q], intersected with that ball. Thus q is outside the ball, not an artificial interior terminal endpoint.

The scope is TRIVALENT vertices. It does not supply degree-one endpoint localization, all-degree star charts, a coherent orientation/rotation system, face-orbit identification, the actual opened pair contour, original taxon order C, or full NANUQ. The original hand theorem is neither weakened nor promoted.

## Constructive chain and source correspondence

1. `OriginalShortArms` obtains full continuous injective endpoint-preserving parameterizations of each selected original edge carrier. Halving the parameters makes distinct germs meet only at v, even when original edges are parallel and share the far endpoint. Exact original edge images and IDs remain in the witness.
2. `TwoGermCarrier` uses the accepted actual continued-arm auxiliary Jordan provider and same-map straight carrier to straighten the first two germ prefixes, with labelled endpoints +2 and -2. The common vertex is strictly inside that carrier, not at an endpoint.
3. `ThreeGermFrame` shifts the vertex to zero. An actual point of the third arm on the horizontal line inside a sufficiently small square would lie in the first carrier, contradicting ORIGINAL distinct-edge incidence. This derives, rather than assumes, the intermediate no-line-hit condition.
4. `SquareFirstExit` uses compact closed-set first exit and the intermediate value theorem; neither finite line intersections nor a radius-once assertion is assumed. The third arm has a constant strict half-plane sign before first exit. Reflection, if needed, fixes the first carrier pointwise.
5. `HalfRectangle` is an explicit affine image of the qualified model Jordan square. `HalfCrosscut` uses the accepted relative crosscut extension to map that actual third prefix to its chord, fixing the entire horizontal line and its labelled first two cutpoints. The third exit endpoint is fixed too.
6. `actual_three_incident_frame` retains the FULL original-edge parameterizations and the labelled correspondences: edge 0 cut 1/6 maps to (2−c,0); edge 1 cut 1/6 maps to (−2−c,0); edge 2 cut s maps to q, with 0<s≤1/2. |c|<2 gives distinct positive/negative rays. These named intermediate witnesses are retained even though the final point-set endpoint forgets the labels. Parameters belong to returned same-image parameterizations, not promised pointwise original curve parameters.
7. `FiniteTrace` forms a compact residual K from ALL other vertices, ALL nonincident original edge carriers, and EACH FULL residual tail [a_i,1] of the selected edges. Original faithful incidence and injectivity show v∉K. The actual whole drawing equals K union the three prefixes. A later metric ball avoids H(K); no tail is silently discarded and no wild-arm finite-crossing assertion is used.
8. `OriginalBinaryStar` derives exhaustive enumeration from the accepted original incidence bound ≤3, and transfers the exact whole point set through the unchanged faithful drawing adapter.

## Explicit edge-case audit (static, not compiler verification)

- Parallel IDs: distinct IDs are never replaced by unordered endpoint pairs. The proof excludes their shared FAR endpoint using t/2≤1/2 and full-edge injectivity. Bigons elsewhere remain in K. Three parallel edges, if excluded by a source degree case, are not needed as a premise of the generic drawing argument.
- Loops: original `RootedBinary.acyclic` and `EdgeGraph.acyclic_no_loop` already exclude source loops. The generic drawing layer itself supplies injective arc parameterizations with distinct endpoints. No new source no-loop assumption was introduced.
- Tail re-entry: the closed full tails [a_i,1] are compact and avoid v. The final ball is chosen only AFTER the complete ambient map; it avoids all their images, including any arbitrarily many pre-chart returns.
- Radial endpoint: ε≤‖q‖/2 and ‖q‖>0 explicitly imply ε<‖q‖. q_y>0 separates the third ray from both horizontal rays.
- Labels: intermediate named source theorem preserves original es/ws and endpoint-to-ray equalities. No arbitrary child order is substituted for original C. Reflection is allowed for local topology and makes no global orientation assertion.
- Degenerate/small blobs: no ≥3-vertex block premise is used. The theorem applies wherever there really are three distinct incident IDs; singleton and degree-two cases are not falsely claimed covered.

## Qualification boundary

All code is UNCOMPILED. Tuple elaboration, coordinate normalization, interval/set membership, finite-subtype inference and imported API usage still require the sole compiler. Do not infer kernel acceptance from this static construction. Preserve any failures and repair only proof bodies while holding stated source assumptions and endpoints fixed. See BUILD-REQUEST.md and DEPENDENCIES.json.
