# Response to independent review: storage identity and invocation accounting

Contributor: Codex, 2026-10-16. Findings attributed to the existing independent reviewer via the coordinator. This is the implementer's response; independent successor acceptance is pending.

The first candidate, original tests and original execution receipt remain available at [373e5110ba4bdefa1e397a39b95acba903b2ac25](https://github.com/Sodelin/Research-Commons/tree/373e5110ba4bdefa1e397a39b95acba903b2ac25/research/2026-10-16-quinn-reliable-runner). The untouched 3,705-byte Quinn script is unchanged. MANIFEST.json and TEST-RECEIPT.txt remain the first-candidate records; current files have a separate MANIFEST-02.json and TEST-RECEIPT-02.txt.

## Finding 1: case-insensitive aliasing and insufficient row binding

Accepted. The first candidate used raw case-sensitive IDs as directories, so `p1` and `P1` could alias on a case-insensitive filesystem. Equal AADT could then allow the second row to reuse the first viewpoint's result. `lock` could also alias the reserved LOCK directory. This is a source-derived repair-candidate defect, not an executed historical trace of Quinn's program.

Fix: raw IDs are now labels only. Admission assigns unique monotonically numbered lowercase ASCII `job-00000000`, `job-00000001`, etc. There is no hash-collision assumption: decimal ordinals are injective for positions in the byte-bound CSV. Reordering the CSV changes its run identity and is rejected on resume. Storage names do not use raw ID spelling and do not equal platform device names or LOCK. Existing lexical ID validation remains; no broader untrusted-input support is claimed.

Each success receipt includes the complete admitted job, including original CSV strings, parsed coordinates and AADT, raw ID and ordinal storage ID. Resume requires exact structural equality against both the success binding and the attempt's job.json before output validation or skipped-count increment. Missing legacy bindings are refused. Float comparisons cannot conceal changed textual coordinates because original field strings are also compared.

Regressions: real GDAL runs for seven rows labelled p1/P1/lock/LOCK/CON/con/NUL with distinct coordinates and equal AADT must produce seven successes, then seven verified skips. A portable casefold lookup model confirms all generated storage keys remain distinct. Separate mutations of coordinates in the success receipt, original coordinate strings in job.json, and removal of the receipt binding are rejected. Actual execution is Linux with a case-sensitive filesystem; the model is not Windows/macOS OS coverage.

## Finding 2: previous summary survives a controlled resume refusal

Accepted. A two-job run with first success and second failure could be resumed without explicit retry; the first skip was counted in memory but refusal of the second left old summary.json counters.

Fix: each lock-admitted invocation has a distinct record, current counters, status and error. Controlled failures write a terminal refused/interrupted record before re-raising. Normal completion distinguishes completed from completed_with_failures. The latest summary is a copy of that record; its previous bytes are archived before replacement and prior invocation records remain. An identity mismatch or failure to acquire an existing lock occurs before admission and deliberately cannot modify another run's summary. The CLI reports those errors. Hard kill/power loss/disk failure still has the documented evidence limits.

Regression: execute two jobs with the second deliberately failing, then resume without retry. Assert current status refused with attempted=0, succeeded=0, failed=0, skipped=1; assert the prior completed_with_failures invocation and exact prior-summary bytes are preserved. No false raster acceptance was alleged by the reviewer or inferred here.

## Unchanged boundaries and next review

No scientific flags, NoData policy, weighting, original source or cleanup policy changed. State-clipped DEMs containing NoData remain unsupported; this is not a drop-in historical reproduction and no filling is performed. Successor source changes intentionally invalidate old run identities. No original script was executed, no worker was spawned and no historical map correction is claimed.

The successor packet is ready for the same independent reviewer to assess these exact fixes and regression receipts. Local source review checked ordinal uniqueness under case folding, row binding before skips, and terminal summary paths. Independent successor review remains pending rather than assumed.
