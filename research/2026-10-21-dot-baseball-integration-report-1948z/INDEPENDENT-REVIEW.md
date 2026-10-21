# Independent review of the coverage-aware integration

Author: dot (OpenAI-assisted research). 21 October 2026.

**Scoped PASS after corrections.** This is a mechanical integration review, not validation of a full player-value statistic, independent raw-data reconstruction, or proof that the supplied components measure disjoint causal effects.

The reviewed composer enforces a positive half-open ISO-date window, matching component player/window/reference/version/mode metadata, finite numeric run values (excluding booleans), and explicit attribution and definition. Not-applicable components also need matching metadata and a reason. Partial components contribute to a supported subtotal but prevent a complete total or run-to-win conversion. Missing is not zero. Semantic disjointness remains a supplier declaration, not something that the component-name whitelist can prove.

Five independently authored adversarial cases initially exposed missing guards for reversed dates, component window mismatch, wrong player, a not-applicable reference mismatch, and boolean values. After correction, all five reject while a valid synthetic complete control is accepted. See `independent_contract_tests.py` and `independent-contract-final.log`. The separate author suite also passes twelve tests. These are synthetic contract tests, not measurements on baseball performance.

A separate row-level audit checked all 1,410 original partial ledgers and all 738 selected September baseline ledgers. Every supported subtotal equals the supplied batting, steal-only, and simplified pitching values. Every row retains missing or partial status for all seven full components; full total runs and wins are null. No actual full-value ranking is thereby certified. Forecast windows are half-open: the September window ends exclusively on October 31, covering September 1 through October 30, with only regular-season observations included.

The September reporting script constructs subtotal residual bands from the 2024 validation block and evaluates them on 2025. They are posthoc descriptive bands, not independently calibrated 90% prediction intervals. The same 2024 outcomes selected the component baseline, and final refitting and calendar changes can shift residual distributions. Role counts, pooled fallback, quantile convention, width, and observed coverage must accompany them. They apply only to the supported subtotal; missing full-value components have no estimated uncertainty distribution.

The separate empirical confirmation remains negative: the selected stronger baseline and augmented ridge nearly tie on subtotal MAE, while every pooled component favors the baseline and the improvement gate fails. Mechanical integration does not reverse that result. The proposed team-residual defense allocation remains unadopted and is not supplied here.

Underlying source definitions, independent refits, and limits are preserved in the pinned stronger-baseline package linked from README.md. Third-party player-level records remain outside this review text.

## Final presentation review

`BASEBALL-REPORT.md` was read in full. Historical September 2025 scope, supported-subtotal status, missing full-value components, role-specific uncertainty coverage, shared selection/calibration outcomes, and the unadopted alternative allocation are prominent. Its empirical claims match the independently reviewed computations. Retaining the simpler baseline means retaining a reference for this historical exercise, not recommending current deployment.

A separate arithmetic check of all 738 saved report rows verifies 655 covered outcomes (88.7534%), the role coverage figures, and mean/median band widths. Batting-role coverage is 93.09%, pitching-role coverage 85.40%, and the single two-way case is uncovered. This does not validate calibration assumptions.
