# Independent September result review
Author: dot. October 21, 2026. Scoped execution PASS; improvement gate FAIL.

The new comparison was reviewed before execution in INDEPENDENT-PREREFIT-REVIEW.md. Subsequent changes were mechanical assertions and reporting/source clarification, not test-outcome-driven feature changes. The original May/July negative result is preserved.

Independently authored independent_september_review.py reproduced the ridge regressions by augmented least squares and the shrinkage/exposure baselines by a separate rowwise implementation, including September 2024 model selection. Selected ridge penalties were 1000,100,1000; baseline pseudoexposures were 600 batting PA,200 steal opportunities and 90 pitching outs. On 738 test players, maximum ridge prediction discrepancy was below 3.9 e−14 and baseline discrepancy below 1.8 e−15. This verifies computations from saved design, not independently re-parsing all raw source events.

Supported-subtotal MAE: ridge 2.2378658510 versus per-component validation-selected baseline 2.2379939226. Relative improvement is only 0.0057226%, well below the 1% gate. The saved paired-player 95% interval for baseline-minus-ridge absolute error is [−0.0372843,0.0386390], crossing zero. The gate fails. Each component's pooled MAE worsens individually, while the subtotal nearly ties through error cancellation; this is not evidence that all component estimates improved.

The previously reported 24% gain against unshrunk last 60-day persistence was a weak-baseline comparison. This confirmation shows no meaningful incremental advantage over the stronger simple shrinkage/calendar-exposure baseline in this season-end task. It does not prove every future model impossible, but it supplies no basis for a superiority claim, a new-stat deployment recommendation, or further tuning on this same September test.

September 2025 is a previously unscored disjoint retrospective outcome block, not an untouched year or prospective test. Earlier 2025 results informed the follow-up design; all raw rows had already been acquired. Calendar availability is scheduled season-end availability, not exact team games. Supported components still exclude identified individual fielding, full baserunning and other full-value adjustments. The all-in-one goal remains open; the team-residual alternative has not been adopted in this audit.
