# Actual startup block and one same-input G6 retry

Input `1eb4b9a7f39f50aa6bc59f2791e82d380764fdf5` includes corrected G6 Taylor, earlier checked program budgets, independent G3 scalar and repaired narrow G5 analytic branch. Their pending combined scope is 80 selected declarations: 64 G6, one G3, 15 G5.

Both intended G6 run 37655542723 and newly unintended G5 full-context run 37655542728 ended `startup_failure` with no jobs and no compiler execution, observed 2026-10-07 17:03 UTC. Check suites contained zero check runs; startup log endpoint returned 404. Neither result is a mathematical failure or a proof PASS. Source/workflow bytes were preserved.

The G6 public run-page annotation reports: “An unexpected error has occurred and we've been automatically notified. Errors are sometimes temporary, so please try again.” It supplies no YAML location or source diagnostic. Both workflow blobs were unchanged from the earlier successfully started `eac8195` run. No YAML root cause was authenticated, and no speculative workflow/source correction was made for this startup error.

Root authorized ONE explicit rerun of G6 37655542723 only, at the same frozen source. The request exited zero at 17:05:14 UTC and immediate readback showed QUEUED with no jobs. G5 was not rerun. Request acceptance does not establish compilation. `startup-and-one-retry-request.json` preserves the exact annotation, command, outcome and readback.

If that one retry cannot start, preserve the environment block and current pending source gates without indefinite retries. The previously verified source/program components, Taylor failed attempt, program budget PASS and exact original G5 diagnostic remain individually pinned. Full masters stay IN PROGRESS.
