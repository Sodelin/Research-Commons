# Source finder and proof checker: two different jobs

## Scale what proved cheap

Four concurrent metadata reads acquired the Git tree of the selected Init and Std prefixes from official Lean 4.33.1. The 1,112 regular Lean source paths cover every admitted file in those two prefixes only (630 Init, 482 Std). The collector did not download the Lean sources. Recomputing 193 Git tree IDs checked coverage by immutable tree membership. One sample was 524 ms elapsed, 316,423 response-body bytes, and 109,143 bytes of retained index shards (plus its receipt). This is not a whole Lean tree or a polling budget.

The live GitHub listener and pinned external snapshot can therefore list an order of magnitude more than a per-file API, without fetching every source body. The newly registered scoped snapshot uses verified per-shard hashes and is available in ordinary Discovery search. Search hints are not statement extraction. Exact paths are usually best resolved from a registered repository, revision and path bucket. For exploratory repeated queries, a local disposable postings index supports identical exact-token semantics to the scan. On 65,887 real Git path rows, it took 3.25 s to build and 55.8 MB on disk. Warm selective results took 0.009 to 0.190 ms; broad results sometimes lost to a pretokenized scan. Query rate, path-index fetch time, and payload size are different metrics. [Provider replay](scale/provider/README.md) · [Exact-token cache](scale/search/README.md) · [Live audit and constraints](scale/audit/REPORT.md)

## Scale the division of work, not a global crawl

Use one registry of approved repositories and the scopes worth listing, immutable release/tree pins, a global budget, and last-good metadata per provider. Search local postings and known immutable paths first; when missing, do a bounded provider lookup and record coverage or truncation. Fetch only the selected blob or the specific import closure for a chosen result. Keep explicit time, rate-limit and truncation outcomes; a search miss outside indexed scope is not proof of absence. Do not try to mirror all GitHub, run arbitrary packages, or reuse a provider's claim as a kernel attestation.

## One real calibration job

Run the Alexander zero-run recurrence from a two-file GitHub lock through the existing compatible Lean runtime. The pinned runner checks file Git blobs and SHA-256, the Lean binary and commit, and the exact theorem type, with a fresh compile and axiom audit. SMT is not part of this job. Source acquisition, a prior receipt and a fresh scheduled execution are different events. The recurrence and eventual triangle-size signature on the **unmerged** two-sheet graph are mathematical results; the full cap-two portfolio theorem remains unassembled. [Recurrence source](../../../research/2026-11-25-proofbridge-linear/capped-host/recurrence/README.md) · [Inert pickup gate](pickup-audit/README.md)
