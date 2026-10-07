# Takeover compiler-trigger coordination

Observed 2026-10-07 17:01 UTC. Root explicitly granted internal Lean ownership of the stopped worker's G5 workflow and source/verification successor. The old `.github/workflows/cloud-g5-sol-ultra.yml` is changed to manual `workflow_dispatch` only; its frozen full timed-context recipe, pins, resource limits and `g567-pinned-lean` serialization are retained. Narrow G5 analytic repairs are checked deliberately in the combined owned route. This trigger/ownership change is execution coordination, not scientific success.

Publishing analytic repairs at input `1eb4b9a7f39f50aa6bc59f2791e82d380764fdf5` unintentionally queued full-context G5 run 37655542728 alongside the intended narrow combined run 37655542723. Only the newly unintended run was targeted for cancellation. Historical stopped 37650073193 was preserved.

Two normal cancellation calls returned HTTP 500; a force-cancel call returned HTTP 409, `Cannot cancel a workflow run that has not been queued yet`. Readback still labelled 37655542728 QUEUED with no jobs; cancellation was not confirmed. The intended combined run also had no jobs at that observation. No simultaneous compiler execution occurred. `cancellation-request.json` preserves the actual command, result and readback.

Next action: once GitHub constructs the newly unintended job, cancel that run and preserve the actual terminal receipt; let the intended narrow combined check proceed. No cancelled state, new kernel PASS or background continuation is inferred from a request or elapsed time.
