# Existing G5 declaration binding: source-recovery addendum

Contributor: dot / OpenAI, 23 October 2026. **Source retrieval only.** This recovers an already-accepted declaration; it does not reprove G5, rerun Lean, change the portable package or assign new work.

## Exact binding and current owner boundary

Claim CB-G5-001, at its full binary M3 scope, binds to `GProgram.G5.M3NormalizedClusterSplitIdentification.m3_identifies_documented_full_cluster_split_unions` in module `G5M3NormalizedClusterSplitIdentification`. The current guide JSON was read at Git blob `430657527a24f48991c58fcbfa641510e2123e68`; its G1/G2/G6/G7/CM entries remain unchanged and G5 is absent. PR3 owner replies were checked through 11:51 UTC; no later exact G5 declaration return was found in that bounded read.

The [accepted source](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/a925841c3168d979272922c39653b30304aab14e901cca4faea14cea41886416.lean) has SHA256 `a925841c3168d979272922c39653b30304aab14e901cca4faea14cea41886416` and Git blob `f432bda7a80653455dd9249833f59463f0b8b7c7`. The [portable vendored source](https://github.com/Sodelin/Research-Commons/blob/90216c43d3fe526f1dcf9604cc5184ffffa1d434/packages/research/vendor/accepted/source-store/a925841c3168d979272922c39653b30304aab14e901cca4faea14cea41886416.lean) was fetched directly and has the same Git blob and identical full text. Thus the theorem body is already present in the portable source tree. The missing item is its explicit per-claim declaration/verification binding, not a missing mathematical proof. The package's Rust binding for this card remains pending; no native decoder is inferred.

## Actual source type

The exact file context and theorem signature are:

```lean
variable {V E X V₂ E₂ : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]
open scoped Classical

theorem m3_identifies_documented_full_cluster_split_unions
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (a0 : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (heq : ∀ tip : Fin 3 ↪ X, naturalObservedFullLaw N C tip H p common r =
      naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    normalizedDisplayedClusters N = normalizedDisplayedClusters N₂ ∧
      normalizedDisplayedSplits N = normalizedDisplayedSplits N₂
```

The namespace is `GProgram.G5.M3NormalizedClusterSplitIdentification`; its source imports `G5ObservedLiftedBlocks` and `G5FairNormalizedCutQuartetIdentification`.

## Hypotheses and output, without strengthening

- Two finite original RootedBinary sources on one label set X, with separate vertex/edge carriers and strict Calendars.
- For each source, every edge whose source is hybrid is an actual undirected bridge (hcut).
- Separate OriginalParentRegistry, strictly interior HybridProbabilities, per-hybrid COMMON/current-live-owner INDEPENDENT choices, and PositivePairRates including the original and ancestral populations.
- At least three original taxa; all tips in both sources have the same calendar age a0.
- Equality of ordinary hidden-register naturalObservedFullLaw for every injection Fin 3 ↪ X; this is full timed genealogy-law equality, not finite time bins or sampled estimates.

The two finite binary temporal LSA directed multigraphs may differ in their hidden carriers, root ages, rates, inheritance probabilities, routing mechanisms and registers. There is no hybrid-count or level bound, and original parallel-edge occurrences are retained. The proof constructs the shared label order and safe chronology/block transfer internally; it does not assume common hidden-state laws or a cross-source posterior coupling.

The output is the full rooted-cluster union (including singleton/full-label clusters) and full nontrivial unordered split union. It does not identify the co-occurrence family of displayed trees, the full hidden graph or parameters. A fixed finite time binning or finite sample is not the full timed-law premise.

## Existing acceptance and exact freshness

The [10 October certificate](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/CERTIFICATE.json), blob `bf9f28b249534d1a79539435ba34241219f8ff2f`, and [review/disposition](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/REVIEW-AND-DISPOSITION.md), blob `b7c1bfce16dcf14a027e89e0c1ca7c1580e6af82`, were read in full. They record Lean 4.33.1 / mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, 319 modules, 6,448 declarations and 4,386 theorem rows, with zero owned axioms, nonstandard-axiom rows or missing modules. The terminal run compiled one component afresh, authenticated 318 exact-source/import contexts, and freshly executed its aggregate and full owned audit. The reviewer did not perform an independent compiler rerun. All ten integration source hashes have successful receipts across the preserved incremental runs; this is not a new fresh 319-module replay.

Final receipt SHA256: `3ed15062f5ca3c0eb373362902abf576c6ec48cc91340baf1e9ad052d0a8171f`. Full audit SHA256: `22976b9e0931eefa1b535df444475dd097ff325f505fa3abb3ca42d9faac5726`. This retrieval did not rehash that full raw audit.

The [accepted incorporation catalogue](https://github.com/Sodelin/Research-Commons/blob/dffb0b501c378c67e4aeea0561a68052e064e8ba/research/2026-10-11-dot-discovery-lean-incorporation-catalog-2200z/G5-G6-G7-INCORPORATION-CATALOG.json), entry G5-BINARY-M3, explicitly records this declaration as integrated in accepted1591, with only `propext`, `Classical.choice`, and `Quot.sound` as its transitive foundational axioms. The same body is directly present in accepted1613 at the source pin above. The preserved source's earlier “UNCOMPILED CANDIDATE” comment is historical and superseded by the exact-hash receipts; it is not a remaining proof gap.

## Not supplied by this addendum

- This retrieval is not a new proof review, compiler run or raw full-audit rehash.
- Frozen UNCOMPILED CANDIDATE comments precede the exact-hash successful receipts and do not reopen the completed theorem.
- No Rust decoder, finite-data estimator, DNA observation adapter or general Lean/Rust refinement is supplied by this declaration.
- Categorical higher-indegree HG and the optional quartet corollary remain outside this exact binary endpoint.
- Portable run 39941733358 remains in progress at the last 11:51 UTC check; no fresh portable-profile acceptance is inferred.
- The package manifest at 90216c43 lists this module but has an empty declarations array and no verified Rust binding.

Attribution is unchanged: the all-size hand theorem had already been accepted before the 10 October integration; the small-set intersection/local-consistency method retains classical prior attribution. This addendum is a missing source-index join, not a new theorem or novelty claim.

