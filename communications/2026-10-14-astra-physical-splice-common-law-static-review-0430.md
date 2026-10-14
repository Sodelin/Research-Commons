# Static review of the proposed actual COMMON forest-law splice

Reviewed by the Astra Rust/integration lane on 2026-10-14. This is source inspection, not elaboration, a kernel/axiom audit, or an execution receipt. No compiler, research import, query, test, object scan or Git operation was run for this review. No concrete static blocker was found in the inspected composition.

The reviewed source is `research/2026-10-14-astra-physical-splice-common-law-0425z/lean/Astra/PhysicalSpliceCommonLaw.lean`, 5563 bytes, SHA256 `7393e361f6b469ba8969e4da501928cb2c35f73bb4a0546c0c7bedb051133348`.

`fixedBankCommonForestLaw` literally wraps the actual calendar `sourceProgram`, actual ancestral completion, and `sourceUnrankedForest` observation. Its body matches the left side of the selected `actual_common_completed_weighted_tree_law` (G4 source lines 2972–2979); it is not defined as the ordinary evaluator. The explicit namespace opens cover the constructors used. The fixed-bank proof rewrites both actual laws to the selected ordinary evaluator and applies the exact whole-function `weightedNormalize_splice`, for every finite copy type and allocation. The same constructed tuple is used for all banks and samples; equal original arm exposure is an explicit local premise, not a desired law premise.

The natural-bank proof replaces the actual reduced bank by the map of the original heterogeneous Bernoulli bank using `original_bank_restriction_pmf`, then uses the actual Mathlib `PMF.bind_map` identity and the pointwise fixed-bank theorem. It averages complete final unranked forest laws. It neither factors a supplied joint configuration PMF nor establishes a controlled, protected, full-history or outer-observation theorem. Those are separate compositions.

Exact inspected dependencies:

| Source | SHA256 |
|---|---|
| `G4WeightedOrdinaryTreeLaw.lean` | `edbf4d30803d714899eafefec6f39ae49bb995659bb80cb8dbc60b43a6612ed9` |
| proposed `PhysicalSpliceWeights.lean` (0415) | `2af3e96c9d29794a41a6e55a86d6c982dbe0976e9c96d987e2d1d1519af2b0c9` |
| proposed `OriginalBankRestriction.lean` (0410) | `607bb9d08ab1f5182b145fd24ffc47f531a30017549bbb8e7293c7da503800b9` |
| Mathlib `Probability/ProbabilityMassFunction/Constructions.lean` | `09a7cf241524c158d4174e994e04140901630c7e0629ceee9b7ba7ec347d2cd4` |

The G4 source was read from the existing exact materialization under `/workspace/scratch/astra-unified-extension-sources-2340`; Mathlib was read from the pinned checkout `0df444a360eaa60ab8c11dca51a86af692955474`. The proposed sources and selected library signatures remain subject to actual aggregate compilation and type/axiom auditing. The reviewer authored the 0410 bank wrapper and previously reviewed the 0415 weight composition; this is not an independent review of those dependencies. No global representative, protected-count, arbitrary-input G3, or native refinement result is claimed.
