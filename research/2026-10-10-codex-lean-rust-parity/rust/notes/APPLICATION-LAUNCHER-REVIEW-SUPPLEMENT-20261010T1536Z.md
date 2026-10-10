# Final launcher static supplement

Contributor: Codex Rust implementation role. Status: bounded source-and-saved-receipt review, superseding the two implementation findings in [the historical review](APPLICATION-LAUNCHER-REVIEW-20261010T1526Z.md) at its final launcher identity. No native/frontend/RC1/Lean executions or accepted source/pin edits were performed. Root separately ran the focused and functional application controls.

Both identified findings are addressed for the reviewed supplied-calendar path and the tested Linux process environment. Final launcher SHA256 is `8c00f261d180452daa094b87f50a788b862efe7c0c5b0e2e133e44bb269352a7`; the earlier `f076a885…` review remains historical. Final launcher/README bodies are preserved in `rust/evidence/launcher-static-review-final-1536Z/`.

## Cleanup finding

Shared `execute()` now starts its wrapper in a separate session. At timeout, `terminate_process_tree()` stops that wrapper, walks `/proc/<pid>/stat` parent IDs, stops discovered descendants before traversing their children, kills those descendants individually, kills the wrapper's isolated process group and waits for the wrapper. Original native/reference child `os.setsid()` calls therefore do not hide descendants from the parent-ID traversal. The callback and wait operations are inside a `BaseException` cleanup block for a still-running wrapper. The timeout receipt records the observed cleanup method and discovered descendant count (launcher lines 142–206).

Root's retained controls explicitly exercise a detached child and grandchild under outer timeout, and a callback exception with detached descendants. The production wall limit remains 45 seconds; the timeout test uses a documented 0.5-second override. I inspected their saved PASS records; I did not repeat these experiments.

The acceptance is **Linux `/proc` scope**, not a portable descendant-kill theorem. The method requires readable process stat records and permission to signal the relevant processes. On a system without `/proc`, the recorded fallback is `PROCESS_GROUP`; that fallback cannot promise termination of a child that has already entered its own session. The source only skips vanished stat records and missing processes, so arbitrary `/proc` permission failures or malformed/unavailable records are not proved safe by this review. Likewise, a daemon already reparented outside the visible tree is not covered by a parent-ID traversal. The count called `descendants_killed` records discovered processes targeted for termination, not a universal reaping proof. No claim of malicious-process containment or all-POSIX detached cleanup is made.

## Request-binding finding

Before accepting delegated status, calendar dispatch checks parent-staged request bytes still equal its original raw snapshot and compares child `request_sha256` with `sha(raw)` (lines 452–459). This applies to all table/UNKNOWN/execution results and to refusals that report a request digest. A `REFUSED_REQUEST` without a digest is allowed for the actual adapter's pre-read malformed optional-pin refusal; it cannot be promoted to a table or exclusion. Existing required Boolean start evidence, exact status/exit mapping and all false scientific/certificate/full-solver flags remain checked afterward.

Root's retained synthetic controls reject a foreign child-request digest and changed parent staging bytes. Their receipt correctly marks that they do not execute a native solver. Twelve fresh functional cases on this final launcher passed: five complete tables, three UNKNOWN scopes and four refusals. The aggregate adds missing-input/no-overwrite outer controls. No changes to accepted Rust, borrowed native transport, independent helper, executable or component-pin bytes are inferred from these launcher-only tests.

## Current contract scope

The reviewed flags, command names, request paths and old command branches still match the unchanged contract and README. TABLE acceptance requires producer, replay and independent checker starts plus complete coefficient/agenda/substitution flags. Provider UNKNOWN remains qualified framing, source admission/certificate/full solver remain false, and the old RC1/frontend receipts are reused only at unchanged executable identities. The cleanup change does not establish a new scientific or formal claim.

## Exact identities

| Input | SHA256 |
|---|---|
| [run.py](../../../../applications/practical-solver/run.py) | `8c00f261d180452daa094b87f50a788b862efe7c0c5b0e2e133e44bb269352a7` |
| [README.md](../../../../applications/practical-solver/README.md) | `a94333a9cdbec1daec356ac57baeb3e6c89b1554e4d17344b481ac368211c5f2` |
| [APPLICATION-LAUNCHER-REVIEW-20261010T1526Z.md](APPLICATION-LAUNCHER-REVIEW-20261010T1526Z.md) | `406bc831743b23d136e42dd291e782f2bf17ffb8dee3dc83edd326cf5db8103f` |
| [native_calendar_component.py](../native_calendar_component.py) | `9de9c1bf056a7b0d40900b33ebd3d29f12b2efacab61e90f9ab5b633a86f0db6` |
| [native_component.py](../native_component.py) | `cbad55d031621f8e6d29ddc58d6156188c6b9344705d4612642b2423ca6aea3c` |
| [calendar_check.py](../../design/calendar_check.py) | `6190bcd125c51d2e133b571ecc9fe08298fe5a731dc6536459f66446f0ae29bb` |
| [CALENDAR-COMPONENT-PINS.json](../CALENDAR-COMPONENT-PINS.json) | `23751b40d609fce76ae82c0d921e81e74669a0dd0fe9b7da72f436ce92a99800` |
| [RECEIPT.json](../../quality/evidence/application-calendar-integration-20261010T1505Z/launcher-final-controls-2/RECEIPT.json) | `8a93bda3449f691c4204ef4d2238b99d6a8c1bb564ced4cae191b9c592c95f3a` |
| [RECEIPT.json](../../quality/evidence/application-calendar-integration-20261010T1505Z/RECEIPT.json) | `cc7904cd7925148587351e6619cb8c1f9817fbaa815c71c2185a1ad5b7433432` |
