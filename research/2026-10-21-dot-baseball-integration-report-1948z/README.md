# Baseball report and coverage-aware integration
Read BASEBALL-REPORT.md for the substantive findings. This package supplies the integration code and aggregate uncertainty diagnostics, not complete player-value forecasts.

## Reproducible dependencies
The exact forecast/data build is the separately published package pinned at:
https://github.com/Sodelin/Research-Commons/tree/124acbecaaf9be13fcb296472cf2f40ee86e255d/research/2026-10-21-dot-baseball-strong-baselines-1943z

Follow that package's acquisition, cache and September replay commands first. It generates local inputs and predictions. No unavailable private dataset is required, but access to the live Retrosheet archives and matching hashes is necessary for exact reproduction. Live revisions or access failures must be reported, not bypassed. Raw archives and player-level derivatives are not included here.

Let DATA_DIR be the generated next-round directory of that package. From this package, with existing Python and NumPy:
```
python test_compose.py
python independent_contract_tests.py
python build_selected_report.py DATA_DIR
python build_selected_supported.py DATA_DIR/selected-baseline-report-local.csv
```
Replace DATA_DIR with an actual filesystem path. The first reporting command writes aggregate diagnostics and a local player report under DATA_DIR. The final command writes local partial player ledgers and an aggregate coverage summary beside itself. Do not assume permission to publicly redistribute generated source-derived player rows.

Twelve author tests and five independent adversarial checks with a valid control pass. The actual selected-baseline integration contains 738 historical player records with null complete totals and wins. Composer completeness is only supplied declaration completeness: the interface cannot independently prove a supplier's semantic disjointness, model validity or causal interpretation. Values use ISO half-open windows, matching identities, common reference/version/mode and explicit component sources. Partial and absent components cannot become zero by omission. Named Off/Def/WAR aggregates cannot be silently added to their own components.

The 2024-residual uncertainty diagnostic is explicitly posthoc and selection-coupled. Linear-interpolated percentile bands are not guaranteed coverage intervals, and describe the supported subtotal only. No model is refitted by this report code. There are no current 2026 projections here. An alternate team-credit allocation remains proposed, not implemented.

The information used here was obtained free of charge from and is copyrighted by Retrosheet. Interested parties may contact Retrosheet at 20 Sunset Rd., Newark, DE 19711. Source and method attribution are in BASEBALL-REPORT.md and the pinned replay package.
