# Stronger baselines erase the apparent forecast gain
Author: dot (OpenAI-assisted research), prepared for Nolan. 21 October 2026.

A previously unscored September 2025 outcome block was tested after the May/July results motivated stronger baselines. This is a disjoint retrospective season-end confirmation period, not an untouched dataset or prospective evaluation. The exact 60-calendar-day target still excludes postseason; all methods receive scheduled regular-season availability. September development anchors in earlier years match that regime.

On 738 eligible players, the supported-score subtotal MAE is 2.237866 for ridge versus 2.237994 for the per-component validation-selected shrinkage baseline. This is only a 0.0057% difference. The paired 95% player-bootstrap improvement interval is [−0.03728,+0.03864] run-score units. The frozen scientific improvement gate fails. Each pooled component separately has slightly greater MAE than its baseline; the subtotal near-tie reflects offsetting component errors, not demonstrated across-component improvement.

The comparator's pseudoexposures were selected on September 2024: 600 PA for batting, 200 reference opportunities for steal-only, and 90 outs for simplified pitching. Selection also considered zero and calendar-adjusted persistence. It is a stronger same-information comparator, not a professional projection or the strongest possible model. Component and role tables, calibration, and zero-denominator diagnostics are retained in SEPTEMBER-RESULTS.json. There is one two-way player, so no subgroup generalization is possible there.

The test concerns a supported subtotal only. Full fielding, advancement, replacement, park/league and modern WAR accounting remain outside it. The first standardized-change batting test also remains negative. Neither result was tuned away. No further September tuning is permitted by this plan.

## Replay
With Python and existing NumPy, from this directory:
```
python acquire_panel.py
python cache_components.py
python next-round/run_september.py > next-round/replay.log
python next-round/independent_september_review.py > next-round/independent-replay.log
```
The package includes the next-round directory needed by the cache generator. Acquisition is six bounded annual archives, no retry; source hashes must match for exact replay. Raw and player-level derived data are generated locally, not bundled. The cache also reruns the same-provider per-game reconstruction checks before making any new cohorts. Independent refitting reproduces ridge predictions within 3.9e-14 and baseline predictions within 1.8e-15; it is not an independently authored raw parser.

All target definitions, split masks, season-end source links and prefit review are included. Scheduled September 29, 2024, not the later September 30 extension, is the forecast input. Actual regular-season events within each 60-day horizon remain outcomes even when rescheduled beyond the scheduled season end.

The information used here was obtained free of charge from and is copyrighted by Retrosheet. Interested parties may contact Retrosheet at 20 Sunset Rd., Newark, DE 19711.

Sources: https://www.retrosheet.org/downloads/csvdownloads.html ; https://www.retrosheet.org/downloads/plays.html ; https://www.fangraphs.com/tools/guts?type=cn . Official scheduled-season endpoints are linked in next-round/FROZEN-PLAN.md.
