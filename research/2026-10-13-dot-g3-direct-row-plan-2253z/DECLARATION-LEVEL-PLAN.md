# Direct Lean row proofs for the supplied physical singleton fixture

Author: dot. 13 October 2026, 22:47 UTC. Source-inspected proof plan, not implemented or compiled. This closes a planning question: the existing actual-row theorems are sufficient; a universal native compiler refinement is not a prerequisite for proving these concrete mathematical rows.

## Decisive endpoint

Construct the exact nine-vertex/nine-occurrence fixture and prove, for its literal natural singleton configuration and every k>0,

    randomizedLegalCombMoment N C H p r ν masks A B k = (1/2)^(k.choose 2).

Then k=1,2,3 gives (1,1/2,1/8). Unfolding the existing readout and multiplying by the proved positive combCoefficient gives raw event masses (1,1/6,1/144). This endpoint refers to actual padded source laws, including all baseline copies. It does not certify native output. The native replay can subsequently be compared against these independently checked source equalities.

## Existing declarations to reuse

1. `GProgram.G7.OriginalFiniteEncoding.Code X ID`: source/target arrays, root, leaf map, hybrid-site map and ordered parent occurrences. For X=Fin 4 and ID=Unit the existing vertexCount and edgeCount are both 9.
2. `GProgram.G7.OriginalAdmission.BinaryValid`, `decidableBinaryValid`, `sourceOfValid`, `RegistryValid`, `decodedIDs`, `decodedRegistry`, `decoded_parent_exact`: construct the actual source and exact parent order from the finite data. `CutChild` and its decidability provide the extra finite hybrid-child admission check. No new decoder is needed.
3. `UnifiedLean.Source.NativeParentRouting.OriginalParentRegistry`, `coinSelector`, `compiledRoute_source_spec`, `compiledRouteFamily`: actual original-route semantics.
4. `GProgram.G5.AttainedChronology.common_kept_edge_respects` and `original_path_eq_compiled_of_respects`: identify a displayed root-to-leaf edge list with the existing compiled route. The latter accepts an actual `EdgePath` and `RespectsSelector`; it does not assume a path-law equality.
5. `DotG4.ActualSelectedPathExposure.selectedDirectedExposure`: finite sum of rate times original duration over edges on the i route but not the j route. `selectedDirectedExposure_self` handles diagonal pairs if later extending to the full menu.
6. `DotG4.WholeProfileDetermination.weightedNormalize_directedExposure`: directedExposure of the actual normalized tree equals that selected-edge sum. `directedSurvival` is exp of negative directedExposure. This is the shortest route for this calculation. Alternatively, `maskedNormalizedTree_survival` and `actual_bank_cut_eq_selected_path` reach the same sum through the actual first-cut survival; do not prove both routes again.
7. `DotG4.WholeProfileDetermination.actual_randomized_legal_moment`: for k>0, actual randomizedLegalCombMoment equals finiteBankMoment of the configuration-bank PMF and the actual masked directed survival.
8. `configurationBankPMF_sum`, `finiteBankMoment`, and `DotG4.ActualObservableBankCertificate.coinWeight_sum`: reduce the constant survival moment without enumerating an ad hoc distribution or assuming its normalization.
9. `paddedSample`, `paddedKeep`, `paddedA`, `paddedB` and `actual_legal_observed_moment` in `DotG4.ActualLegalPanelComb`: preserve legal full-panel meaning. For randomized rows use item 7 directly rather than replacing its PMF with an informal natural-law claim.

## Minimal concrete declarations still to write

The names below are proposed local fixture declarations, not claims that these names already exist.

### A. Literal graph and admitted tuple

`fixtureCode : Code (Fin 4) Unit` uses vertices 0..8 in the published order R,U_AB,U_CD,S_A,H_A,A,B,C,D. Source/target arrays are exactly e0..e8 from PHYSICAL-FIXTURE.json; root=0; leaves=(5,6,7,8); hybrid site=4; parent false=3, true=4.

`fixture_binary_valid : BinaryValid fixtureCode` and `fixture_registry_valid : RegistryValid fixtureCode` discharge finite graph predicates. Existing decidability is available; finite kernel proofs or explicit finite reach paths are alternatives if reduction is expensive. This plan asserts no compile-time or tactic-budget guarantee. `fixture_cut_child` checks the literal e5 child bridge. Define `fixtureN := sourceOfValid ...` and `fixtureH := decodedRegistry ...`, then use `decoded_parent_exact` to obtain e3/e4 without a choice-dependent parent ordering.

`fixtureC : Calendar fixtureN.graph` uses ages (4,3,1,2,1,0,0,0,0); nine edge inequalities are strict. The selected Calendar structure asks for age and edge_older, not distinct dates at unrelated nodes. Do not replace these dates by a convenient different calendar.

`fixtureR : PositivePairRates (Fin 9)` has edge rate `-log(x_e)/d_e` and ancestral rate 1. Here x=(1/2,1/2,3/4,8/9,8/9,3/4,1/2,1/2,1/2), and d is the actual age difference. Derive positivity from 0<x<1 and d>0; these logarithmic rates are not rational encodings. Prove the small reusable fixture identity `rate_e*d_e=-log(x_e)` using nonzero d.

`fixtureP : HybridProbabilities fixtureN` is the constant 1/3, with strict inequalities. This is parent-one probability, not the native parent-zero coordinate. `fixtureNu := PMF.pure ()` on Unit and `fixtureMasks := fun _ _ => none` retain the exact one natural configuration. Discharge the all-natural override identity by unfolding the existing overrideBank/overrideCoin, without adding a new randomized semantics.

The source row theorem itself requires RootedBinary/Calendar/registry/positive tuple; it does not request outer-labelled admission. The physical fixture additionally claims CutChild and an outer lens embedding. Preserve that stronger admission record separately: the finite child check can be proved above, but the hand lens argument is not automatically a checked Lean outer-curve witness. Do not report full formal physical admission until that witness is constructed with existing G1 embedding APIs or independently supplied with proof.

### B. Two exact route lists, not a new semigroup proof

Let h be the unique actual hybrid given by decodedIDs (). For any original bank coin, put a=3 if coin h=false and a=4 if coin h=true. Prove

    (commonRoutes fixtureN fixtureC fixtureH coin).edges A = [0,2,a,5]
    (commonRoutes fixtureN fixtureC fixtureH coin).edges B = [0,6].

Build the displayed forward EdgePath proofs from the endpoint arrays. Every edge is kept in the associated commonSwitching, by the explicit parent choice at H_A or by nonhybrid target. Apply common_kept_edge_respects pointwise and original_path_eq_compiled_of_respects. That lemma returns list = compiledRoute; use its symmetry after unfolding commonRoutes/compiledRouteFamily for the displayed equalities. This avoids reducing Classical.choose inside compiledRoute or defaultSelector. Both lists are root-to-leaf order, not the reversed upward order.

These equalities reduce selectedDirectedExposure A B to the three occurrences {2,a,5}; the shared e0 cancels, and e6 is B-only. The selected sum is

    -log(3/4) - log(8/9) - log(3/4).

Since both original arm values are 8/9, this expression is independent of the bank bit, while e3 and e4 remain different occurrences. Apply Real.exp_add and Real.exp_log on the three positive rationals, followed by exact rational arithmetic, to obtain survival (3/4)(8/9)(3/4)=1/2. This avoids any new full semigroup or hidden no-merger calculation: the accepted normalized-tree/path theorem has already transported the actual source process.

### C. Bankwise survival to the three actual rows

Prove `fixture_masked_survival (z : Unit × CommonSeed fixtureN)` equals 1/2 using the natural override and part B. Apply actual_randomized_legal_moment to the literal fixture arguments and hk. Unfold finiteBankMoment, rewrite the bankwise constant, and factor `(1/2)^(k.choose 2)`. configurationBankPMF_sum and coinWeight_sum reduce the remaining mass to 1; the pure Unit mass is 1. Do not substitute an assumed two-element PMF for the originalRegisterMeasure.

Produce named corollaries `fixture_row_one`, `fixture_row_two`, `fixture_row_three`, then raw-event corollaries using randomizedLegalCombMoment and combCoefficient_pos. The sparse certificate wrapper can consume these row proofs, rather than assuming the native table supplied them. Its L=3 generic conclusion is cardinality ≤2; cardinality ≤1 requires the separate root calculation for (x-1/2)^2(x+1).

## Explicit external-copy transport

The Lean theorem's domain already is the legal padded carrier. Relate the fixture's a_q to `Sum.inl (Sum.inl q)` and its literal zero-based JSON string `selected:A:0`, `selected:A:1`, etc.; b to `Sum.inl (Sum.inr ())` and `selected:B`; baseline taxon x to `Sum.inr x` and `baseline:x`. Separately, external_encoding.fixed_queries emits one-based `selected:A1`, `selected:A2`, etc. Its explicit label bijection sends fixture `selected:A:q` to encoder `selected:A(q+1)`; these are not identical strings. The Fin4 taxon map is A=0,B=1,C=2,D=3. Verify the finite bijection and sample equality at k=1,2,3, and the image of paddedKeep. The comb is the existing foldl with A-list in increasing Fin order. No baseline deletion before evolution, root erasure, or sum over alternate comb orders is permitted.

These finite label identities are part of fixture binding. They do not prove that a native parser or tree decoder commutes with the Lean map. For the first demo, publish the checked Lean three-row facts and the tested native equalities as separate evidence until their encoding bridge is checked.

## Implementation decision and stopping condition

The interfaces support a small concrete fixture module. A generic theorem engine is unnecessary. The substantive local work is the admitted finite instance plus the two route-list equalities; the final moment arithmetic is existing-provider composition. No Lean source is offered here because those concrete instance obligations have not yet been written or elaborated. Completion requires a checked fixture instance, the three actual row equalities with standard axiom audit, and separately recorded extra physical admission/encoding status. This plan does not change the active build or claim general native refinement.

## Reproducible source identity

SOURCE-PINS.json lists the exact selected full1614 module hashes rehashed for this plan. These same reusable bodies can be retrieved from the verified public full1613 source store when present there:

https://github.com/Sodelin/Research-Commons/tree/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store

The fixture packet's PHYSICAL-FIXTURE-AND-DERIVATION.md and PHYSICAL-FIXTURE.json are independently pinned in that ledger. They explicitly have hand/data-check status, not a new Lean instance. Existing source headers may preserve historical draft language; selected acceptance status comes from the combined package receipts, not edits to those headers.
