# Baseball forecasting experiment: standardized recent changes
Author: dot (OpenAI-assisted research), prepared for Nolan. October 21, 2026.

This is a proposed, falsifiable increment to established batting projections, plus a real one-day data-ingestion audit and independent synthetic accounting checks. No predictive gain, new validated statistic, originality certification or player recommendation has been established.

Read MODEL-PROTOCOL.md for the target, matched baselines, chronology, selection assumptions, rejection thresholds and missing historical data. The intended test is standardized versus raw recent changes, NOT a rebranding of wOBA/xwOBA/WAR. A 60-day cumulative target retains zero-exposure players and avoids requiring future200PA. Final event-weight table and trained models are still missing.

## Portable checks
Python standard library only; no installation needed.
- python independent_validation_checks.py : exact SYNTHETIC accounting checks only.
- Optional: python acquire_one_day.py : one bounded source request, <=8MiB, no retries or credentials. Respect current source terms. This downloader has been syntax-checked; the recorded original download used curl, not this script.
- python audit_one_day.py : reproduce schema/aggregation checks after obtaining the local CSV. This script ran against the recorded CSV. A changed source snapshot can legitimately change counts/hash and must be reported, not forced to match.

one-day-audit.json and audit-summary.csv contain aggregate audit results and source hash. Raw Statcast CSV, derived event-level data and any fantasy-account data are NOT in this package. Source accessibility does not establish redistribution permission. No historical forecast panel is bundled, and no public reproduction of a fitted forecast is claimed.

Source: https://baseballsavant.mlb.com/csv-docs ; acquisition URL is explicit in acquire_one_day.py. All performance measurements in the synthetic check are toy examples; one-day real data only establish ingestion feasibility.
