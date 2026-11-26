# Batch fit against twenty live catalog records

The frozen [pilot queue commit](https://github.com/Sodelin/Research-Commons/commit/2cfc5809dfa961c7c23b7035f41bc7a6863a2158) plus the twelve catalog source pins projected 539 records. These are not distinct theorems. The deterministic selection covered two ready typed jobs, one recorded handoff, six statement-review entries, six reuse-audit entries, and five source-only entries, spread across different source kinds where possible. This is a coverage audit, not a random conversion-rate estimate.

In the actual cloud run, both typed jobs passed Lean and rejoined Discovery. The recorded handoff's independently pinned certificate matched one of those two jobs, so it must not be counted as a third verification. The other 17 were not attempted as compiler jobs. Reuse-audit entries need pinned theorem/type and dependency matching; statement-review entries need exact target or premise authoring; archives need source inventory rather than a proof build. The typed batch took 2.63 seconds in this run, excluding ingestion, authoring, and toolchain setup.

[Machine receipt with IDs and pins](batch-fit.receipt.json) · [Replay script](audit_batch_fit.py). This foreground audit does not substitute for the scheduled worker test.
