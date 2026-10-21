# Baseball value modeling: what the real tests establish
Prepared for Nolan by dot (OpenAI-assisted research), 21 October 2026.

## Bottom line
A working historical forecasting and component-integration pipeline now exists. It processes six seasons, produces individual forecasts, preserves uncertainty and missing coverage, and has independently reproduced numerical checks. The proposed handedness-standardized change did not beat the ordinary change baseline. A broader component model looked promising against simple persistence, but that advantage disappeared against calibrated shrinkage on a separate September outcome period.

The reference model to retain for this historical exercise is the simpler, validation-selected baseline, not a deployed forecast recommendation or a claimed new superior statistic. It is integrated into 738 historical player records. This is not a current 2026 projection, complete WAR replacement or identified all-in-one skill ranking. Full totals are deliberately unavailable where components are partial or missing.

## What was actually tested
The target was the following 60 calendar days of regular-season contribution, with no future playing-time qualification. Eligibility depended only on past activity. This prevents the common mistake of evaluating only players who remain healthy or employed long enough to reach a future PA threshold. Zero future activity remains in the data. Postseason is excluded consistently.

The six 2020–25 Retrosheet archives contain 979,855 completed plate appearances. Reconstructed batting and later runner/pitcher event totals reconcile to separate daily game/player tables from the same provider. These are strong consistency checks, not proof that the source has no errors. Event dates, rather than original game IDs, handle resumed games.

The batting score uses fixed historical 2020 event weights and a precise wOBA denominator. It is an additive frozen-reference run score, not conventional park-adjusted wRAA. The weights were retrieved retrospectively, not certified from an archived vintage projection. The components added later were centered steal-only value and a simplified FIP-difference pitching proxy. Established sabermetrics supplied those definitions; they are not newly invented metrics.

## Results that survived review
| Test | Comparison | Result | Interpretation |
|---|---|---|---|
| May/July batting, 647 snapshots | Standardized change versus raw change | MAE 4.43362 versus 4.43024 | Standardization is slightly worse; improvement gate fails |
| Same component-period subtotal, 1,410 snapshots | Ridge versus last-60-day persistence | MAE 3.57480 versus 4.70408 | Improvement over a weak comparator only |
| Same component period, posthoc diagnostic | Ridge versus zero-reference subtotal | MAE 3.57480 versus about 3.78366 | Much smaller apparent advantage; steal-only slightly worse than zero |
| Previously unscored September, 738 players | Ridge versus validation-selected shrinkage | MAE 2.23787 versus 2.23799 | Effectively tied; improvement gate fails |

September's paired 95% bootstrap interval for absolute-error improvement is −0.0373 to +0.0386 run-score units. Each pooled component separately is slightly worse than its selected baseline. A tiny subtotal improvement can arise because component errors offset. That is why the report retains component and role errors rather than presenting only a flattering aggregate.

The September outcome period is disjoint from the earlier July target, but the dataset was already acquired and the earlier findings motivated this follow-up. It is retrospective confirmation of a season-end task, not an untouched-year or prospective experiment. Predictable season-end loss of opportunities was supplied to every method using scheduled endpoint dates. Earlier September anchors supplied training and validation examples. Nothing was tuned after the September scores were examined.

Independent refits used a different numerical implementation and reproduced all models and baseline choices to floating-point tolerance. This verifies implementation of fitting and comparison, not predictive superiority or an independently reconstructed source dataset.

## The baseline retained for the usable report
For September, validation selected a prior-365-day component rate shrunk toward a fixed 2020 reference, multiplied by calibrated recent exposure and scheduled calendar availability. Pseudoexposures were 600 PA for batting, 200 reference opportunities for steal-only, and 90 pitching outs. These are separate units. The product is a practical plug-in predictor, not an assertion that the expectation of a product equals the product of expectations.

The player table records the selected component forecasts, their supported subtotal, actual historical subtotal, role, exact half-open target dates and coverage limitations. It does not rank players by a fictitious complete total. The current report is for September 1 through October 30, 2025. It contains no current-season roster recommendation or 2026 forecast.

## What the uncertainty does and does not mean
Fixed 5th/95th percentiles of September 2024 selected-baseline residuals give a descriptive band for the supported subtotal. On September 2025, empirical coverage is 88.75% overall, 93.09% among batting-role players and 85.40% among pitching-role players. There was no two-way calibration example, so the single test case used a pooled band and fell outside it.

Those differences matter more than simply calling the bands “90% intervals.” Model selection and calibration used the same validation period, temporal distributions can change, and the two-way sample is inadequate. These are not conformal guarantees, confidence intervals for intrinsic player ability, or uncertainty bounds for missing full-value components. The mean band width is about 9.57 supported-score units; the median is 7.07. Quantiles use NumPy's linear interpolation. Calibration contains 348 batting-role and 419 pitching-role cases.

## Full-value coverage and the remaining suppliers
| Component | Implemented evidence | What is still needed for the original full-value goal |
|---|---|---|
| Batting | Audited fixed-reference event score and real forecast tests | Park/league normalization, stronger contact and age inputs, comparison to an as-of established projection |
| Baserunning | Centered stolen-base/caught-stealing value | Advancement and other baserunning contributions with non-overlapping attribution |
| Fielding | Actual defensive exposure and accounting checks | A permitted individual defensive-value supplier or a validated opportunity model; putouts/assists/errors alone do not establish skill |
| Position | Non-DH legacy exposure calculation exists separately | Complete role/DH exposure convention aligned to the chosen accounting version |
| League and replacement | Explicit composer slots | Frozen common reference and replacement allocations, not silently assumed zeros |
| Pitching | Audited simplified defense-independent score and forecasts | Full run-prevention allocation including relevant framing, park, relief and replacement conventions |
| Full total | Coverage-aware composer and real partial ledgers | All required disjoint components on one common definition before a total or win conversion is emitted |

The composer checks identities, dates, accounting versions and modes, rejects named aggregate double counting, and distinguishes partial from complete coverage. Its tests cannot certify a supplier's semantic assumptions. Existing Off, Def or WAR must not be added on top of their own components. Current WAR methodology also differs from old explanatory pages, notably in defensive/framing and baserunning allocations.

An alternate team-context credit allocation was proposed separately. It could balance a complete team ledger under declared assumptions, but would allocate park, sequencing and luck along with defense rather than identify individual defensive skill. It has not been adopted or fitted. Missing tracking-quality data is not a theorem that no coarse model can exist; the distinction is between a model's explicit assumptions and evidence identifying the quantity it claims to measure.

## Concrete next gates
1. Do not tune again on September 2025. A further prediction claim needs a new temporal evaluation period or an explicitly separate retrospective development exercise.
2. Obtain and validate a permitted defensive-value/opportunity supplier and complete advancement data, with exact version and attribution. A small attempted Savant fielding-value acquisition returned HTTP 403 and was not bypassed. That is a specific source-access failure, not a claim that no other source exists.
3. Freeze complete replacement, position and run-to-win conventions before presenting a modeled total. Keep observed contribution, forecast contribution and intrinsically uncertain skill separate.
4. Extend the selected baseline only when the added component or data genuinely supplies an unfilled part of the model. More features or a more elaborate name do not establish improvement.

## Sources and reusable evidence
- Retrosheet: https://www.retrosheet.org/downloads/csvdownloads.html and https://www.retrosheet.org/downloads/plays.html
- FanGraphs historical constants: https://www.fangraphs.com/tools/guts?type=cn
- Baseline forecasting context: https://www.tangotiger.net/marcel/
- Modern accounting update: https://blogs.fangraphs.com/2024-fangraphs-war-update/
- Catcher/pitcher allocation: https://blogs.fangraphs.com/war-update-catcher-framing/
- Published negative batting test: https://github.com/Sodelin/Research-Commons/tree/5ea75f2f6003fe466b75eb8f2a6f67f1d86ebfd0/research/2026-10-21-dot-baseball-real-test-1935z
- Published stronger-baseline follow-up: https://github.com/Sodelin/Research-Commons/tree/124acbecaaf9be13fcb296472cf2f40ee86e255d/research/2026-10-21-dot-baseball-strong-baselines-1943z

Public packets contain own methods, aggregate results, source hashes and checks. Raw archives and player-level source-derived tables remain local. The information used here was obtained free of charge from and is copyrighted by Retrosheet. Interested parties may contact Retrosheet at 20 Sunset Rd., Newark, DE 19711.
