# A real 60-day batting forecast test: no improvement detected
Author: dot (OpenAI-assisted research), prepared for Nolan. 21 October 2026.

The proposed handedness-standardized K/BB change did not improve the frozen retrospective test. This negative finding is retained. It is a reduced ablation, not the full contact-quality/age model, not a new WAR, and not a comparison with professional projections.

## Result
3,129 eligible player-anchor snapshots across 2021–25; training 2021–23, tuning 2024, test 2025. The test contains 647 snapshots (307 May 1,340 July 1), including 25 with zero future PA. Standardized-change MAE 4.433619, raw-change 4.430238, baseline-only 4.431732 fixed-reference run-score units. The standardized model's gain against raw is −0.0763%; paired player-cluster 95% bootstrap interval for absolute-error improvement is [−0.006911,+0.000128]. The predeclared improvement gate fails. This is not proof that all context adjustment is useless.

The fitted output predicts cumulative value over the following 60 calendar days, not performance conditional on surviving to 200 PA. W and D use exact frozen 2020 weights and denominator in PLAN-BEFORE-RESULTS.md. No future qualification. As-of vintage weights were not archived: these are historical 2020 constants retrieved and frozen now. Raw/source revisions, shortened 2020, one test year, limited context adjustment and lack of contact quality are explicit limitations. No causal context-neutral interpretation is supported.

All 979,855 completed PA across 2020–25 reconcile to independent game/player batting totals from the same provider. Required batting fields have no blanks; duplicatePAkeys and denominator identities are asserted. These checks do not independently establish that every underlying source event is correct.

## Reproduce
Requires existing Python 3 and NumPy; executed with NumPy 2.3.5. No package installation is performed by these scripts.

From this directory:
```
python acquire_panel.py
python run_reduced.py > replay.log
python independent_fit_review.py > independent-replay.log
```
Acquisition is bounded to six annual archives, 20 MBcompressed maximum each, one request per missing archive, no retries. The source manifest records bytes and SHA 256. Exact replay requires matching source snapshots; if the live provider revises them, report the mismatch rather than asserting byte-identical replication. Archive files, generated player-level tables, and model-input arrays are intentionally not bundled. The first command downloads them locally; the second generates the derived inputs for independent refitting.

Independent numerical review refitted all three saved designs using augmented least squares rather than normal equations. Predictions agreed to <7.8 e−12. This independently checks fitting and cohort assertions, not an independent raw-data parser. The first run stopped before fitting on a NumPy integer JSON serialization error; that technical failure is retained in the log. Repairs added data-integrity/reporting guards, not post-test feature tuning.

Do not publish generated raw or player-level data merely because these scripts generate it. This package contains own methods and aggregate findings only. No empirical superiority or complete all-in-one baseball-value result is claimed. The separately developing supported-component ledger must keep full defense, park, replacement and accounting gaps visible.

## Attribution
The information used here was obtained free of charge from and is copyrighted by Retrosheet. Interested parties may contact Retrosheet at 20 Sunset Rd., Newark, DE 19711.

Data: https://www.retrosheet.org/downloads/csvdownloads.html
Schema: https://www.retrosheet.org/downloads/plays.html
Frozen weights: https://www.fangraphs.com/tools/guts?type=cn
Baseline context: https://www.tangotiger.net/marcel/ and https://library.fangraphs.com/principles/projections/
