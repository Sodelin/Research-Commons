# Static review: actual bridge cut-class budget

Reviewed source `research/2026-10-14-astra-bridge-cut-class-budget-0525z/lean/Astra/BridgeCutClassBudget.lean`, SHA256 `f1a04c11edf41123436962bb40828e0782490e43ab306b4d322d5def31ac6407`.

**No concrete static defect found. Source only; uncompiled.** The structural induction uses the actual binary `Genealogy` constructors and the literal `WellLabelled` child-disjointness field, so graft leaf cardinalities add. `card_insert_le` and `card_union_le` give the cluster upper bound; erasing the known root cluster correctly strengthens `clusters.card + 1 ≤ 2*leaves.card` to `properClusters.card + 2 ≤ 2*leaves.card`.

The pruned tree is obtained by `nonempty_root_pruning_tree_exists` from the original network/calendar/switching, not supplied as a small-tree premise. Its exact original leaf set and derived well-labelled proof discharge the structural assumptions. `prunedAt_exact_original_clusters` is used in both directions; actual selected rootedness supplies the otherwise required reachability from the original root. Removing the full cluster agrees with the pruned tree's leaf set.

The bridge-cut image counts distinct taxon sets, not original edges or cells. The subset proof uses the exact new `bridgeTaxa_nonempty`, `bridgeTaxa_proper`, and every-switching descendant equivalence. The equality orientation in the `sampledDescendants` witness is correct. Thus the proposed conclusion concerns only `(bridgeCutClasses N).card + 2 ≤ 2 * card X`. The caller supplies an actual switching; no probability, chain multiplicity, arm-flip, support, protected count, representative, or timed observation result is inferred.

Exact selected provider bytes, lengths and Git-blob identities were compared with selection commit `7239e89dea5caad68a54227cee3b44a7d9b96389` and the materialized source copies:

- `SourceNetwork`: SHA256 `0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7`, Git blob `abb91b7ed9ad2ad960cb1ab6f8fbbdfc212f9cc0`.
- `SourceLabelledForest`: SHA256 `d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d`, Git blob `4ee5f7c2cb5262aedd5abac98894e98ad9bc1e5c`.
- `G1ActualSelectedClusterTransport`: SHA256 `ed0c37f91f85b8db92a8e25a27e9c895549f6775b69836e7b92ec68e41a87174`, Git blob `6835ba514fc5aaeb94d1fce0d3f72a35d7e682d3`.
- `G5OriginalPruningClusterPreservation`: SHA256 `57a04161dd1fb0cdc9f095c039dbb7ece4b802c621e631fd352c1bb3c74bba75`, Git blob `a7dda820e3d4529c99056adc0ff66bc693e9f9f0`.
- `G5NormalizedSwitchingQuartetCompatibility`: SHA256 `11830f30edf2ad2d9337de3a6074b0d67816fd31a1ee1443cb48f7296bcf89b0`, Git blob `e869a877835358a0d30ec91f4c68fe0a48a519b6`.

The new `Astra.BridgeTaxonCuts` dependency remains uncompiled source SHA256 `4ef5c9deebaa7f0e3a1298ba413e693f389d1f294942990d2da5d6347fe96855`. The read Mathlib `Data/Finset/Card.lean` has SHA256 `174ec68882bf10567b17c3f4d278d6647cef92574dadfa8f7f0821b949967c8f` in the pinned Mathlib source workspace; no fresh whole-checkout authentication is claimed by this review.

No compiler, test, import query, research-module import, object scan, materializer, or Git operation ran. Future `#print axioms` lines are requests, not results. I authored the new bridge-cut dependency and the preceding critical count audit, so this review is independent of the new cut-class proof's authorship, not independent of that dependency. No source was edited.
