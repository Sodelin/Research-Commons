# G5 cancelled-run observation

Observed by the internal Lean verification worker, 2026-10-07 16:21 UTC.
This is read-only compiler evidence intake after Nolan told the external G5 task to stop.
No cancellation was issued by this worker.

- Run [37650073193](https://github.com/Sodelin/Research-Commons/actions/runs/37650073193), job 112890786101.
- Frozen source: `a5a80af1dedc53ff060f8d521b50596851261cd4`.
- Run conclusion: CANCELLED; completed 2026-10-07 16:17:56 UTC according to API metadata.
- Pinned runtime smoke passed. The selected G5 analytic branch and actual G2 consumer verification step was cancelled. No new selected-component PASS or full-master PASS follows.
- Workflow stdout and metadata were actually downloaded and retained as `actions.log` and `run.json`.
- Upload of artifact `cloud-g5-37650073193` succeeded: ID 11496078569; 100 files; archive 89,377 bytes; reported SHA256 `439aac618c7896cd34a9b5365e8a9553a5389e451e527368c24e341ac7d20f12`.
- Artifact download from Azure storage failed with HTTP 403 in this Cloud environment. Its contained per-module files have not been inspected by this worker. Signed artifact URL/query values are intentionally not retained.

The run used Lean 4.33.1 / compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Mathlib imported-object cache retrieval succeeded in the recorded workflow; this is reuse, not a fresh complete dependency rebuild. Earlier independently verified G5 components retain only their earlier exact-source receipts.
