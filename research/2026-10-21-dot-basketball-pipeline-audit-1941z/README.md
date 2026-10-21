# Basketball all-in-one value pipeline: implementation and data gate

Author: dot (OpenAI-assisted research), prepared for Nolan. 2026-10-21.

## Current empirical status: source labels quarantined

A subsequently acquired institutional derived NBA table failed external score reconciliation. A completed retrospective run is preserved only as a flawed-source diagnostic; its apparent loss reduction is NOT actual game-margin validation. See QUARANTINE.md. The complete-game duration gate also caught two genuinely missing overtime periods. No score repair or period relabelling was inferred.

A separate licensed publisher-reference calculator is implemented in `licensed_reference_value.py`. It retains all 747 rows, including 60 unresolved rookie IDs, and scales publisher estimates at explicitly supplied exposure/reference scenarios. It is not our fitted statistic or a calibrated future-production interval.

## What is now implemented

This extends the offense-portability proposal into a dataset-agnostic end-to-end **conditional value framework**:

1. Audit complete game totals, unique game/stint keys, dates, two teams, ten distinct players, within-game team consistency, positive possession counts and historical shot totals.
2. Construct each player's smoothed historical perimeter-attempt mix strictly before the observation date. Entire same-day histories are excluded. Validation features freeze at the training cutoff; final test features freeze at the validation cutoff. Prior is explicitly fixed at .35 with 50 pseudo-attempts, not claimed optimal.
3. Tune three sparse ridge models: additive offense/defense; common-context main effect; common context plus player-specific teammate-context interactions. The same three-lambda budget is used for each. Interaction penalty is ten times the main-player penalty, fixed rather than secretly optimized on the test set.
4. Refit on training+validation after selection. Predict all chronological test rows, including unsupported ones. Report offensive game/team squared error and net game-rate squared error, player coefficients, unseen-player/season flags and marginal context support diagnostics.
5. Calculate offense, defensive points saved, net points per 100 possessions, then total value at explicitly supplied playing-time/availability scenarios relative to an explicitly labelled reference. Recompute all teammate spillovers AND the shared context effect when replacing a player. A common-context term changes by one-fifth of the player's attempt-rate change; each other teammate's context changes by one-fourth.
6. Produce a range across supplied models and exposure scenarios, labelled sensitivity rather than statistical confidence. No automatic wins conversion: a points-per-win calibration must be supplied, if desired.

The defensive coefficient predicts points **allowed**: lower is better. Thus net contrast against a reference is offensive improvement plus reference defensive coefficient minus player defensive coefficient. Model coefficients are in points per possession; deployment reports multiply by 100. Total value multiplies per 100 impact by on-court possessions/100. A pace assumption applies to each side's possessions, not the sum of offense and defense; do not double-count.

This is not an empirically validated NBA all-in-one statistic yet. It is working code and an explicit path from permitted records to conditional outputs. Ridge coefficient allocation is model-dependent, not proof of isolated talent or a causal contribution. All-in-one here means combining defined offensive, defensive and exposure components, not solving confounding or making a universal ranking.

## Files and commands

Existing Python, NumPy 2.3.5 and SciPy 1.17.0 were used; no installations or network downloads occur in the pipeline.

Run from this directory:

```sh
python test_pipeline.py
python portability_pipeline.py implementation-fixture.json --train-end 2020-01-04 --validation-end 2020-01-08 --out fixture-output
python build_value_report.py fixture-output/audit-and-fit.json implementation-value-config.json fixture-output/value-report.json
```

The fixtures are original implementation-test data, NOT NBA data or a new simulation research result. 20 tests passed, including duplicate IDs, reconciliation errors, same-day exclusion, future-history exclusion, unchanged selection/coefficients when only test outcomes change, defensive sign, teammate/common-context recomputation and exposure scaling. The CLI was exercised through final value-report output. Fixture players A 0/B 0 and the zero-coefficient reference are artificial, not athletes or an estimated replacement level.

A real input must supply provenance, an explicit permission basis, documented source-label validation and the `--permitted-real-data` flag. Both the possession and duration pipelines reject real fits lacking the independent label-validation declaration/evidence. This mechanical gate records the operator's declaration; it does NOT verify licensing or confer permission. Do not use it to override a denied source. Outputs preserve source metadata and the input SHA 256.

## Input contract

One JSON object:

- `provenance`: `kind` (`implementation_fixture` for tests, otherwise an accurate real-data label), `source`, `permission_basis` and ideally source version, retrieval time, license, as-of time and hash.
- `games`: objects with `game_id`, ISO `date`, explicit league `season`, `home_team`, `away_team`, `home_points`, `away_points`. Every included game must be complete.
- `rows`: `game_id`, unique-within-game `stint_id`, matching ISO `date` and explicit league `season`, `off_team`, `def_team`, five-string-ID arrays `offense` and `defense`, integer nonnegative `points`, positive integer `possessions`, binary `home`, positive integer `period`, integer pre-possession `score_margin`. Scores and possession counts must use a consistent reconciliation convention.
- `history`: one row per player/game with `game_id`, ISO `date`, `player_id`, numeric integer `three_pa` and `fga`, where 0≤three_pa≤fga.

The implementation fixture is a complete executable schema example. No actual source adapter is assumed. Zero-possession scoring events, technical free throws and possession boundaries must be reconciled upstream rather than silently discarded. A five-ID cardinality check and matched final score do not prove lineup reconstruction correct. Source event ordering and substitutions still need independent checks. Rows should be possessions or sufficiently short stints for the recorded pre-possession covariates to make sense.

Validation/test game separation is chronological; no random row split. Current model requires the source's explicit league season label and flags unseen test seasons. No calendar-boundary heuristic is used, preserving the 2019–20 label for the 2020 bubble. Unseen-season effects fall back to the reference-season coding; this is a limitation, not a learned next-season prediction. No recency decay, age curve or injury dynamics is fitted yet.

## Reference and availability: explicit, not smuggled in

`build_value_report.py` requires a reference label and numerical reference profile. It does not equate ridge-zero with replacement level. To estimate an empirical replacement reference later, define the eligible low-cost/available player pool and a training-only selection/aggregation rule, then test its sensitivity. A roster transaction, salary or low minutes alone does not uniquely define replacement ability.

Supply four teammate profiles, with interaction slope and lagged attempt rate, and exposure scenarios (`minutes_per_game`, `games_available`, `pace_per48`). These can express a deployment of interest but are not forecasts learned by this pipeline. A real availability model needs dated injury/rotation/appearance information and a chronological evaluation of its own. Combining known ratings with arbitrary expected minutes would not finish that empirical task.

The report's sensitivity envelope is usable for conditional comparisons but has no calibrated coverage guarantee. Future implementations should add game-block uncertainty, temporal/transfer strata and benchmark interval coverage. These are explicitly unimplemented, rather than filled with false precision. The current code reports all-case point losses and flagged support, without suppressing difficult cases.

## Actual licensed comparator audit

A separately acquired publisher board has been structurally audited with `audit_comparator.py`. Source: LUMA Basketball Research / CourtShare, https://court-share.com/luma ; source commit `e98feb10444e075777c95926cf070e908332e0a6`; CC BY 4.0 for the publisher outputs, with preserved LICENSE and acquisition manifest in the adjacent licensed-comparator directory.

The 747-row board has 687 distinct nonblank player IDs and 60 missing IDs, matching rookie-prior records. The denominator remains 747. Missing rows retain their original CSV line and source rank in the audit, rather than collapsing blanks into one identity or hiding them from coverage. No duplicate nonblank IDs, nonfinite numeric fields, reversed intervals or skill-plus-lineup discrepancies beyond rounding were found. This is not an accuracy test. Publisher intervals remain publisher intervals, not our calibrated uncertainty.

This net-rating comparator lacks observed game outcomes, ten-player lineups and per-game dates; the board also lacks separate offensive/defensive fields. Source review dates this release to October 2026, so it is a candidate prospective 2026–27 comparator, not an archived pregame baseline for earlier seasons. It cannot be fed to the possession model as training outcomes. Verified source identity is a prerequisite, not empirical evidence for our candidate statistic.

## Exact remaining data barrier

As of this packet, no permitted complete NBA possession/lineup/outcome dataset with required chronology has been acquired. The institutional derived-table lead inspected by the access reviewer contains game, quarter, own-team lineup, duration and plus/minus, but not possession counts, separate offensive/defensive scoring or synchronized opponent-five intervals. Own-team substitutions do not necessarily split at opposing substitutions. Treating those records as the required input would invent missing information. Source adapter inspected: https://github.com/arnaud-odet/lineup/blob/29f64f982ebeabe68187144ad00aefb1f84fca10/roster_lib/data/season.py . The bundled raw source and its permissions need separate review.

NBA source download restrictions are not bypassed. Public parser licenses are not dataset licenses. A non-NBA source, if permitted, could test an adapter but must not be labelled NBA validation. No contact, purchase or credential request has been made by this implementation.

Next executable step once a permitted source is established: write a source-specific adapter, audit a complete game against the source, then a complete season, preserve missingness and timing metadata, run the frozen chronological pipeline and compare against legitimately available as-of baselines. Until then, the real fit and empirical all-in-one ranking are blocked by missing authorized inputs, not reported complete. Further data access work is separate from the completed implementation tests.

Independent implementation review caught and corrected two issues before release: the generic scenario helper must receive common-context coefficients rather than silently using zero; season labels must be explicit because a July calendar boundary fails for the 2020 bubble. Regression tests cover both corrections. This targeted review is not a claim of complete independent software verification.

## Additional executable checks and separate components

```sh
python test_duration_adapter.py
python test_reference_and_gates.py
python duration_net_fit.py duration-implementation-fixture.json --train-end 2020-01-03 --validation-end 2020-01-06 --out fixture-output/duration-fit.json
```

Five duration tests and four reference/gating tests passed in addition to the 20 core tests. The duration target is net points per 48, not the possession-based outcome. `adapt_institutional.py` preserves source row order and explicitly rejects discontinuous quarter labels; its source currently remains quarantined and the real-fit gate rejects it.

For an independently permitted publisher board, the reference calculator takes a board CSV, a scenario JSON and output directory. The example scenario is deliberately the same for everyone, 24 minutes for 40 games at 100 possessions per 48; it is **not** an availability or playing-time forecast. The published board's intervals are merely transformed at that fixed exposure. Reference zero is the publisher's average reference, not replacement. Own source checks/calculator code are separable from licensed source tables.
