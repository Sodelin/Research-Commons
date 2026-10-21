# September follow-up, frozen before new outcome scoring
21 October 2026, 19:39 UTC. Exploratory hypothesis selection follows the May/July negative results. September 2025 is a previously unscored, disjoint retrospective outcome block, not an untouched dataset or prospective validation. All 2025 raw rows were already acquired and audited. No claim of generic 60-day or professional superiority.

Exact targets and eligibility remain the supported component test: batting frozen-reference score, steal-only centered score, simplified pitching proxy; prior 365/60 eligibility remains unchanged, union of batter and pitcher roles. Train May/July/September 2021–23, tune September 2024, refit May/July/September 2021–24, test September 1–October 30, 2025 only. Every feature event date must be strictly before its anchor. All outcomes are regular season only, with no future survivor filter or postseason. Earlier 2025 test outcomes may enter September history because they are then past, but not model fitting or tuning. Final predictions are not refitted after September scores.

Calendar: each method receives fraction f=min(60, scheduled final regular-season date−anchor+1)/60, clipped to [0,1]. Scheduled endpoints are October 3, 2021; October 5, 2022; October 1, 2023; September 29, 2024; September 28, 2025. Use scheduled 2024 September29, NOT the subsequently extended September30. f is calendar availability, not exact team game counts. Retain actual regular-season outcomes occurring later than the scheduled endpoint within the 60-day horizon; schedule disruptions are forecast errors rather than removed rows.

Features: same past 30/60/120/365 supported totals and PA/O/pitching outs, role flags, July and September indicators, f; plus each past total times f. Ridge penalties .1,1,10,100,1000 selected by September 2024 MAE separately by component. Training transforms only. No role hard-zero rule: future position-player pitching and changed roles remain possible.

Stronger baselines: zero reference; calendar-adjusted persistence = previous60 score*f; and shrinkage-rate times calibrated exposure. For component exposures PA/O/pitching outs, shrink prior365 total toward fixed2020 rate with pseudoexposure grid [0,50,200,600] PA or O, and [0,30,90,270] outs. For zero denominator use fixed2020 rate, never silently assert zero outcome. Forecast exposure from recent60 exposure*f times a nonnegative pooled training calibration factor sum(future exposure)/sum(recent60 exposure*f), separately for each component and pre-cutoff role. Calibration uses all training anchors, not 2025. All rate baselines share it. This multiplication is explicitly a plug-in approximation, not E[Nr]=E[N]E[r]. Select the strongest baseline by September2024 MAE per component, then recompute its fitted calibration on training through2024. No baseline is chosen on2025.

Report paired errors of ridge versus selected stronger baseline, components and supported subtotal, pre-cutoff role groups, calibration slopes/intercepts, exposure counts, and player-bootstrap 1,000-replicate CI seed20261022. No-fielding/full-value claim. O=0 does not imply no runner contribution; pitchingouts=0 does not imply no pitching event; count zero-denominator/nonzero-score examples rather than recode as zero. Zero future PA includes actual zero batting target, not exclusion. Dates of later postseason cannot increase opportunities.

Claim gate: at least1% subtotal MAE improvement, bootstrap95% lower bound above0 and no>2% RMSE worsening relative to validation-selected baseline; even a pass concerns only this retrospective season-end supported-score task.

Implementation guards: assert nonempty and disjoint split masks, one test row per player, finite matrices and all target ends before next year. Degenerate constant calibration is reported null. The selected comparator is per-component validation-selected, not the globally strongest possible subtotal predictor.

Scheduled endpoint primary sources:
-2021: https://www.mlb.com/press-release/press-release-mlb-announces-2021-postseason-schedule
-2022: https://www.mlb.com/press-release/press-release-mlb-announces-revised-2022-regular-season-schedule
-2023: https://www.mlb.com/amp/news/mlb-announces-2023-regular-season-game-times.html
-2024: https://www.mlb.com/press-release/press-release-game-times-announced-for-2024-regular-season-spring-training-spring-breakout-games
-2025: https://www.mlb.com/press-release/blue-jays-announce-2025-regular-season-schedule
