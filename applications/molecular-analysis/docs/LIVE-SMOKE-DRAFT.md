# Bounded live smoke launcher draft

**DEFERRED by user steering after the already-running offline gate completed. SOURCE UNREVIEWED; LIVE ACCESS/SDK INTEGRATION PENDING.** The 25 passing offline mocked tests below are preserved at their exact inputs; they do not promote the draft to accepted implementation. No further API implementation, review, test, SDK or live command is authorized by this checkpoint. Next step, only if the user resumes this lane: independently review these frozen files before considering any separately authorized installed-SDK or public-reference live smoke.

Private implementation owner: Cloud / Sol, `/root/dot_source_transfer_sol`. Only the new launcher, its tests and this note are changed. Existing contracts, provider, CLI, haplotype/RNA modules, examples and historical receipts remain fixed. Root owns access setup, review and publication. No credentials are read, SDK installed/imported, service terms accepted or model request executed during this offline implementation.

The standalone entry point is `python -m molecular_apps.live_smoke`; the library entry point is `run_smoke(SmokePlan(...)) -> dict`. Initial support is the existing haplotype application only. It must receive the exact predeclared request and exact track-selection files, their lowercase SHA256s, a hash-pinned JSON source manifest with exactly `SOURCE_PATHS`, native executable SHA256 and current Python executable SHA256. Both `--access-authorized` and `--public-reference-confirmed` must be explicit. These flags record operator assertions; they do not independently verify permissions, terms or public-reference provenance. Root must first review a frozen derivative of the public TERT request with its official model and exact track names; the historical synthetic request is refused because its model is `synthetic-v1`.

The parent validates request context, phase, endpoint preflight and the adapter's existing model/window/output allowlists without calling provider capabilities or inspecting the API-key environment variable. Child environment inheritance is `env=None`; no key value enters command arguments, input, log or receipt. The existing access-check is not a credential validation or a substitute for the explicit assertions.

Exactly one `Popen` attempt is made and there is no launcher retry. The authenticated request bytes go to stdin, so long DNA does not hit argv limits. Track bytes go through a private mode-0600 temporary snapshot because the existing CLI accepts a track-selection path. The child command is the existing molecular CLI with provider `alphagenome`, the explicit authorization flag and the declared native binary. Normal completion and refusals reuse the accepted application status/exit-code contract.

The supervisor enforces wall time across stdin delivery, stdout/stderr reading and waiting for EOF/process exit. All three pipes are nonblocking and reads are capped before allocation; either output stream exceeding its predeclared budget ends the run. Default wall/stdout/stderr limits are 120 seconds/1MiB/64KiB; allowed maxima are 600 seconds/8MiB/64KiB. A local SIGKILL is attempted on the new POSIX process group, including descendants, followed by at most one additional second waiting for reap. A failed reap is explicit EXECUTION_FAILURE. POSIX is required. Process creation and kernel system calls are not independently interruptible by this Python supervisor; the execution deadline is checked immediately after process creation returns. No hostile-host immutability guarantee is claimed.

The receipt contains only fixed status/codes, source/input/executable hashes, counters, limits, selected allowlisted model/output enums and scope flags. Raw child stdout/stderr, exception text, arbitrary child codes/messages, DNA, environment values and track names are excluded. Stderr is counted and discarded, and no live raw-log hash/file is produced. Successful child JSON must match the declared input/settings/native identities, four scenario names, endpoint identities, real-model evidence and the existing prediction-only/biological-false boundary. UNKNOWN phase remains UNKNOWN even when conditional computation succeeds. This protocol acceptance does not independently verify a server inference: the offline tests deliberately use fake production-shaped objects and never count as real-model evidence.

All allowed source files, request/track files, native executable and Python executable are authenticated before launch and after termination. The temporary track snapshot is also checked after termination. Any changed or unreadable final identity invalidates success. Fixed source identities and before/after hashes are reproducibility evidence, not proof against a malicious host changing bytes and restoring them between checks. The installed SDK package, server metadata and immutable server weights are not authenticated by these project-source hashes. A future authorized live receipt must add the actual installed SDK/version and selected metadata evidence through a separately reviewed procedure; immutable server weights are not exposed by the current API.

One complete haplotype child expects **four `predict_sequence` method invocations and four `output_metadata` method invocations**, plus one lazy `dna_client.create`. Requested modalities are bundled into each prediction call. Early refusal may make fewer calls. This is an adapter-source count, not an RPC or quota count: metadata caching, SDK retries and server request accounting are unverified. `create(timeout=30)` bounds channel readiness only. The launcher does not invent a prediction deadline or modify SDK internals. Local termination/reap never establishes cancellation of a submitted remote request, quota recovery or no later billing/service work. The receipt always records these facts as unknown/false. Optional metadata preflight is not implemented or silently run; it needs its own separately bounded, authorized stage and request-count declaration.

Failure boundaries are INVALID_INPUT, UNSUPPORTED, RESOURCE_LIMIT and EXECUTION_FAILURE with fixed launcher codes. A failed/partial child does not provide a model comparison or biological result. This closes a local execution-supervisor design/test gate only; it does not establish real SDK integration, model accuracy, interaction biology, quota guarantees, held-out validation, confidence, clinical use or original G1–G7/RNA-E8 applicability.

## Frozen first offline source before execution

The following identities were recorded before any new tests. A test receipt will be appended without rewriting this historical freeze.

```json
{
  "stage": "offline-launcher-attempt1-pre-test",
  "molecular_apps/live_smoke.py": {"sha256":"bc0b946c34687e79a5037724fbd1232337533e8d182a1dd6709dd6346ea1a28d","bytes":20997},
  "tests/test_live_smoke.py": {"sha256":"b55b370b3447dd014a8a54278efad618d8c50d82058d63a6df48ce3ed6d39930","bytes":21230},
  "molecular_apps/contracts.py": "32d6b69ce48412de21e5160aac287415500c79a95aa306b29a6ea90ce3d71e67",
  "molecular_apps/cli.py": "cddeec13db9194f5d3f59842e8e2531de3bd7fa6d295fad356d63199138f3449",
  "molecular_apps/providers.py": "a1494dd5de42dd77afed22396c6b45f41c8ebf1eaab596a819f95f7ad4befe01",
  "molecular_apps/haplotype.py": "a65f3d4cec728c9931763378218e242c6192980e7c58455fe624fe07edce9a70",
  "molecular_apps/rna_processing.py": "f0f46b37cefca4d232eb01f37be1c3aa0d5cec84da635e3b603c238711c2d68a"
}
```

## Planned deterministic offline gate

Tests use synthetic request/reference/annotation/track fixtures and mocked `Popen`, selectors, monotonic clock, reads/writes, process groups and reap. No live child, SDK imports, credential inspection or network calls occur. Cases exercise one-launch/no-retry behavior, streamed stdin, authorization/public-input/hash/source allowlists, before/after mutations, a protected track snapshot, unsupported endpoints before cost, wall limits including blocked stdin, byte limits during reads, broken pipes/reap failure, sanitized exceptions/refusals, malformed/duplicate/nonfinite JSON, exit/status/matched-identity rejection, UNKNOWN phase and standalone CLI manifest pinning. The tests are source/mock verification, not actual OS scheduling or installed-SDK verification. The pre-existing full-product87 receipt remains distinct.

## Actual offline attempt1 receipt

**25/25 unit and mocked subprocess integration tests PASS**, 2026-10-08 01:27 UTC. Every recorded source hash is unchanged before/after. The outer test supervisor returned exit0 under its 30-second bound. This is new author execution evidence on the first frozen launcher source, separate from the pre-existing87 test receipt. The verbose stderr below consists entirely of known synthetic unittest output; its SHA is safe to preserve here. No live raw log is saved.

```json
+{
  "stage": "offline-launcher-attempt1",
  "command": [
    "/opt/codex/runtimes/codex-primary-runtime/dependencies/python/bin/python3",
    "-m",
    "unittest",
    "tests.test_live_smoke",
    "-v"
  ],
  "started_utc": "2026-10-08T01:27:48.217484+00:00",
  "completed_utc": "2026-10-08T01:27:50.639074+00:00",
  "supervisor_timeout_seconds": 30,
  "exit_code": 0,
  "source_before": {
    "molecular_apps/live_smoke.py": "bc0b946c34687e79a5037724fbd1232337533e8d182a1dd6709dd6346ea1a28d",
    "tests/test_live_smoke.py": "b55b370b3447dd014a8a54278efad618d8c50d82058d63a6df48ce3ed6d39930",
    "molecular_apps/contracts.py": "32d6b69ce48412de21e5160aac287415500c79a95aa306b29a6ea90ce3d71e67",
    "molecular_apps/cli.py": "cddeec13db9194f5d3f59842e8e2531de3bd7fa6d295fad356d63199138f3449",
    "molecular_apps/providers.py": "a1494dd5de42dd77afed22396c6b45f41c8ebf1eaab596a819f95f7ad4befe01",
    "molecular_apps/haplotype.py": "a65f3d4cec728c9931763378218e242c6192980e7c58455fe624fe07edce9a70",
    "molecular_apps/rna_processing.py": "f0f46b37cefca4d232eb01f37be1c3aa0d5cec84da635e3b603c238711c2d68a"
  },
  "source_after": {
    "molecular_apps/live_smoke.py": "bc0b946c34687e79a5037724fbd1232337533e8d182a1dd6709dd6346ea1a28d",
    "tests/test_live_smoke.py": "b55b370b3447dd014a8a54278efad618d8c50d82058d63a6df48ce3ed6d39930",
    "molecular_apps/contracts.py": "32d6b69ce48412de21e5160aac287415500c79a95aa306b29a6ea90ce3d71e67",
    "molecular_apps/cli.py": "cddeec13db9194f5d3f59842e8e2531de3bd7fa6d295fad356d63199138f3449",
    "molecular_apps/providers.py": "a1494dd5de42dd77afed22396c6b45f41c8ebf1eaab596a819f95f7ad4befe01",
    "molecular_apps/haplotype.py": "a65f3d4cec728c9931763378218e242c6192980e7c58455fe624fe07edce9a70",
    "molecular_apps/rna_processing.py": "f0f46b37cefca4d232eb01f37be1c3aa0d5cec84da635e3b603c238711c2d68a"
  },
  "stdout_sha256": "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
  "stderr_sha256": "36ebda85f9fa780c580cd7589cdbdf2979e8ca597814b09824201f4b111d78f2",
  "stdout_bytes": 0,
  "stderr_bytes": 3521,
  "scope": "synthetic deterministic subprocess doubles; no SDK/network/credentials/live child",
  "test_count": 25,
  "source_unchanged": true
}
```

Saved synthetic unittest output (stdout was empty):

```text
+test_authorization_refusal_before_reads_or_spawn (tests.test_live_smoke.SmokeTests.test_authorization_refusal_before_reads_or_spawn) ... ok
test_bad_exit_status_and_mock_evidence_are_not_live (tests.test_live_smoke.SmokeTests.test_bad_exit_status_and_mock_evidence_are_not_live) ... ok
test_bad_limits_platform_and_digest_refuse_before_launch (tests.test_live_smoke.SmokeTests.test_bad_limits_platform_and_digest_refuse_before_launch) ... ok
test_blocked_stdin_is_included_in_wall_deadline (tests.test_live_smoke.SmokeTests.test_blocked_stdin_is_included_in_wall_deadline) ... ok
test_broken_stdin_is_execution_failure (tests.test_live_smoke.SmokeTests.test_broken_stdin_is_execution_failure) ... ok
test_child_refusal_statuses_safe_allowlist (tests.test_live_smoke.SmokeTests.test_child_refusal_statuses_safe_allowlist) ... ok
test_cli_refuses_before_manifest_read_without_authorization (tests.test_live_smoke.SmokeTests.test_cli_refuses_before_manifest_read_without_authorization) ... ok
test_cli_source_manifest_is_hash_pinned_and_bounded (tests.test_live_smoke.SmokeTests.test_cli_source_manifest_is_hash_pinned_and_bounded) ... ok
test_extra_track_refused_before_child (tests.test_live_smoke.SmokeTests.test_extra_track_refused_before_child) ... ok
test_hash_mismatch_refuses_before_launch (tests.test_live_smoke.SmokeTests.test_hash_mismatch_refuses_before_launch) ... ok
test_invalid_json_duplicate_nonfinite_and_raw_traceback_not_echoed (tests.test_live_smoke.SmokeTests.test_invalid_json_duplicate_nonfinite_and_raw_traceback_not_echoed) ... ok
test_public_reference_assertion_required (tests.test_live_smoke.SmokeTests.test_public_reference_assertion_required) ... ok
test_reap_timeout_is_explicit_failure (tests.test_live_smoke.SmokeTests.test_reap_timeout_is_explicit_failure) ... ok
test_request_snapshot_race_is_detected_before_child (tests.test_live_smoke.SmokeTests.test_request_snapshot_race_is_detected_before_child) ... ok
test_source_and_input_changes_after_child_invalidate_success (tests.test_live_smoke.SmokeTests.test_source_and_input_changes_after_child_invalidate_success) ... ok
test_spawn_exception_never_returns_message_or_retries (tests.test_live_smoke.SmokeTests.test_spawn_exception_never_returns_message_or_retries) ... ok
test_staged_tracks_change_invalidates_success (tests.test_live_smoke.SmokeTests.test_staged_tracks_change_invalidates_success) ... ok
test_stderr_cap_is_enforced_and_not_retained (tests.test_live_smoke.SmokeTests.test_stderr_cap_is_enforced_and_not_retained) ... ok
test_stdout_cap_is_enforced_during_reads (tests.test_live_smoke.SmokeTests.test_stdout_cap_is_enforced_during_reads) ... ok
test_success_one_launch_stdin_and_safe_receipt (tests.test_live_smoke.SmokeTests.test_success_one_launch_stdin_and_safe_receipt) ... ok
test_unknown_phase_is_not_promoted_to_success (tests.test_live_smoke.SmokeTests.test_unknown_phase_is_not_promoted_to_success) ... ok
test_unknown_source_path_refuses_before_read (tests.test_live_smoke.SmokeTests.test_unknown_source_path_refuses_before_read) ... ok
test_unsupported_endpoint_before_child (tests.test_live_smoke.SmokeTests.test_unsupported_endpoint_before_child) ... ok
test_unsupported_model_before_child (tests.test_live_smoke.SmokeTests.test_unsupported_model_before_child) ... ok
test_wall_deadline_kills_and_reaps_once_no_retry (tests.test_live_smoke.SmokeTests.test_wall_deadline_kills_and_reaps_once_no_retry) ... ok

----------------------------------------------------------------------
Ran 25 tests in 2.248s

OK
```
