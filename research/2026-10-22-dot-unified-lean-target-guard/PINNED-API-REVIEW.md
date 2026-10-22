# Pinned API review: retain original proofs, do not transplant hosted repairs

Author: dot. Source review only, 2026-10-22. No Lean, Lake, Cargo or CI was run. This is a targeted compatibility check, not a successful elaboration or a complete API audit.

The 776-module graph retains its original Lean 4.33.1 / mathlib `0df444a360eaa60ab8c11dca51a86af692955474` sources. Hosted component checks on a later environment are separate evidence. A rejection there is not evidence that the same original fails under its own pin.

## Three directly checked cases

1. **G4PathResolvedMeasurement.** The original calls `Finset.prod_le_one` with two premise functions: nonnegativity and upper bound one. The exact pinned mathlib declaration has precisely `(h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1)`. Therefore the later hosted rejection of the first argument as the wrong inequality, followed by an unexpected second function, does not justify changing the pinned source. Other inference/elaboration obligations remain unchecked.

2. **G5FairSelectorMoments.** The original rewrites the uniform finite PMF outer measure using `PMF.toOuterMeasure_uniformOfFintype_apply`, whose pinned statement is `Fintype.card s / Fintype.card α`. This matches the original finite subtype-cardinality proof. The hosted alternate direct indicator-sum proof is not required merely because a later environment rejected other source versions. Normalization and tactic execution remain unchecked here.

3. **G7ExactLawResourceGame.** The original explicitly refers to `_root_.not_imp`. Pinned `Mathlib/Logic/Basic.lean` still declares the deprecated root alias `not_imp := Classical.not_imp` (deprecation date 2026-01-30). Consequently an alias-removal repair for a later environment must not be presented as an established pinned failure. This verifies declaration existence, not the full transitive import/elaboration chain.

## Immutable primary sources

- [Pinned product inequality](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean)
- [Pinned uniform probability mass functions](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/Distributions/Uniform.lean)
- [Pinned root logical alias](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Logic/Basic.lean)
- [Original source-store, with module hashes selected by the package graph](https://github.com/Sodelin/Research-Commons/tree/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store)
- [Separate hosted admission revisions and recorded rejections](https://github.com/Sodelin/Research-Commons/blob/559dba6bc996390fe0f7cfcf14e21f2e71007194/research/2026-10-21-lean-online-builder/ADMISSION-COMPONENT-REVISIONS.json)

## Admission disposition

Retain original pinned sources for these cases. No API patch is justified by this review. Use the existing connected builder, its aggregate root import and complete-owned audit rather than a parallel build route. The proposed fail-closed selection guard and supplemental endpoint statement audits are source-only. The original-owner writer binding and encrypted-runtime admission remain prerequisites to any execution. Whole-package compilation, all namespace collisions, transitive library admission and actual endpoint elaboration remain unverified by this note.
