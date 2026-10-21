# Independent pre-fit review of September follow-up
Author: dot. October 21, 2026, 19:40 UTC. Scoped PASS before execution, subject to the listed mechanical assertions and reporting clarifications.

Read FROZEN-PLAN.md and run_september.py before any September comparison execution. Reviewed exact train<=2023, September2024 validation, refit<=2024 and September2025 test masks; fixed2020 rate references; past-only windows; separate PA/opportunity/outs shrinkage units; shared training-calibrated exposure in rate baselines; matched calendar availability; validation-only model selection; and paired player bootstrap. One September row per player makes the row resampling equal to player resampling. Calendar correction is scheduled opportunity, not exact team games or hindsight cancellation correction.

Required mechanical guards communicated before execution: assert one test row per player; nonempty and disjoint train/validation/test sets; finite design and outcome values; temporal target windows do not cross the following year's development boundary. Retain primary schedule source URLs with the plan. These are not outcome-driven model revisions.

The comparator is the *per-component validation-selected baseline*. Selecting the best component errors does not mathematically guarantee the strongest aggregate-error baseline because component errors can offset. Do not call it the strongest conceivable subtotal baseline. If target or prediction is constant, calibration slope/intercept require a degenerate-case warning rather than a meaningful calibration claim.

The existing May/July2025 results informed this new analysis. The new target block is disjoint and previously unscored, but not an untouched year or prospective validation. All2025raw records were already acquired. The original negative result remains unchanged. The result can support or reject this declared season-end supported-score comparison only; it cannot establish professional superiority or complete all-in-one value.

The reviewed pre-patch plan and script hashes are preserved in independent-prerefit-reviewed.sha256. Any implementation/reporting changes should be described and the executed successor hashes retained. No residual-defense target was adopted in this review.
