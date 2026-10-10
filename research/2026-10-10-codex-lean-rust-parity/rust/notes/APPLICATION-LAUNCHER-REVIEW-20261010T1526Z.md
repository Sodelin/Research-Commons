# Calendar-law application launcher static review

Contributor: Codex Rust implementation role. Status: bounded independent static integration review of the historical launcher bytes identified below. Root's fresh application execution evidence is separate. No native/frontend/RC1 tests, Lean compiler, git operation, or accepted source/helper/pin edits were performed for this review.

The interface, status mapping, acceptance flags, preserved input path and README align with the frozen supplied-calendar application contract. Two concrete integration hardening findings remain in the reviewed launcher: outer timeout descendant cleanup and cross-layer raw-request identity. Root acknowledged the first and is repairing its own launcher; a later review must bind the corrected bytes rather than silently treating this hash as fixed.

## Reviewed identities

| Input | SHA256 |
|---|---|
| [run.py](../../../../applications/practical-solver/run.py) | `f076a8853e44f83aa9b4519df284bf8d25e5b970fbb0e6aae54a4d3f0a099abd` |
| [README.md](../../../../applications/practical-solver/README.md) | `a94333a9cdbec1daec356ac57baeb3e6c89b1554e4d17344b481ac368211c5f2` |
| [CALENDAR-APPLICATION-CONTRACT-20261010T1458Z.md](../../design/CALENDAR-APPLICATION-CONTRACT-20261010T1458Z.md) | `7ef233395d60a3e7cd6edd1418df428b5cb9f842088ac87ddc85f957b3eb18c4` |
| [native_calendar_component.py](../native_calendar_component.py) | `9de9c1bf056a7b0d40900b33ebd3d29f12b2efacab61e90f9ab5b633a86f0db6` |
| [native_component.py](../native_component.py) | `cbad55d031621f8e6d29ddc58d6156188c6b9344705d4612642b2423ca6aea3c` |
| [CALENDAR-COMPONENT-PINS.json](../CALENDAR-COMPONENT-PINS.json) | `23751b40d609fce76ae82c0d921e81e74669a0dd0fe9b7da72f436ce92a99800` |

`run.py` was reviewed at SHA256 `f076a8853e44f83aa9b4519df284bf8d25e5b970fbb0e6aae54a4d3f0a099abd`. The accompanying README was reviewed at `a94333a9cdbec1daec356ac57baeb3e6c89b1554e4d17344b481ac368211c5f2`; the contract was `7ef233395d60a3e7cd6edd1418df428b5cb9f842088ac87ddc85f957b3eb18c4`. Those observed historical bodies are copied into `rust/evidence/launcher-static-review-1526Z/` when still available at the observed hash. Immutable component pins remain `23751b40d609fce76ae82c0d921e81e74669a0dd0fe9b7da72f436ce92a99800`.

## Contract correspondence

The parser adds `calendar-law --request PATH --output NEWDIR --native-binary PATH [--expected-binary-sha256 SHA]` and forwards `--binary` to the calendar adapter. It selects `native_calendar_component.py` and requires child schema `rust_calendar_component_result_v1`. Existing affine, chart and LAW module/schema routes remain distinct (launcher lines 361–398 and 489–498).

Input must be a nonsymlink regular file at most 65,536 bytes. The launcher reads raw bytes, creates a fresh absolute output directory and copies them unchanged into parent `REQUEST.json`; it deliberately avoids the older nine-parameter request parser and its 256-bit rational cap. The child receives that absolute staged path and an absolute executable path. Output no-overwrite is enforced before subprocess launch. The public example is byte-identical to the frozen two-tip request, SHA256 `42eb6a95c160825cb19da7945bd025cb2e31e8a2d43aaab4fe1c87a0d4c64dbf`.

Status/exit mapping is exact: `SUPPLIED_CALENDAR_TABLE` → 0, `UNKNOWN` → 2, and `REFUSED_REQUEST`/`RESOURCE_OR_EXECUTION_FAILURE` → 1. The wrapper's observed exit must agree with the child's status; malformed/missing evidence, launch failure, time/memory/file exhaustion and identity drift become execution failure. Calendar input/file/output failures caught before wrapper launch return 1. Existing commands retain their previous exception exit path (lines 421–426, 464–465 and 499–503). Argparse usage errors remain its conventional exit 2.

Start flags begin false, become unknown (`None`) after wrapper launch until a child receipt exists, then require actual Boolean solver/checker/reference flags. Successful calendar tables additionally require all seven producer/replay/reference/formal-table/all-coefficient/agenda/substitution flags true. The launcher never uses native replay alone as independent coefficient evidence. It checks source admission, physical-image, observation-law, full-joint-calendar-law, statistical-confidence, source-census, full-solver and certificate flags are false on every calendar child status, including UNKNOWN/refusal (lines 401–420 and 443–458).

Full delegated evidence is retained as `component_result`, with child scope explanation and source hash recheck. No calendar result is promoted to an unrestricted exclusion, scientific source certificate, timed law or parameter-recovery result. The README's calendar section describes the separate package/build path, exact symbolic `EXP_NEG` convention, standard-library independent algorithm, success/UNKNOWN/refusal exits and provider-UNKNOWN framing limitation; it links the exact nine-field contract. Existing default examples, legacy diagnostic and other command dispatch remain separate.

## Actionable findings

1. **Outer timeout may strand a detached descendant.** Shared launcher `execute()` waits 45 seconds and calls `process.kill()` only on the wrapper at line 158. The calendar adapter launches producer, replay and independent reference sequentially through the frozen transport; that transport calls `os.setsid()` for each child and enforces its own 45-second timeout in the wrapper process. Killing the wrapper removes that waiter and does not terminate a child's separate process group. CPU/address/file limits do not bound a sleeping descendant's elapsed lifetime. This preexisting shared-helper issue is relevant to the new composition and other optional native commands; the accepted short-running table controls do not establish descendant cleanup. Root-owned remediation should terminate and reap the actual descendant tree/groups on timeout while preserving honest unknown start flags and fresh failure receipts. Merely increasing the outer timeout does not prove cleanup. No accepted Rust or transport source needs mutation.

2. **Bind the child's raw request identity to the outer snapshot.** The launcher records `request_bytes_sha256` but does not compare it with the child's `request_sha256`, nor recheck the parent `REQUEST.json` after child return. The adapter correctly binds the bytes it read; a changed parent staging file before that read could therefore yield a valid delegated calculation while the outer receipt still names the earlier raw digest. Add calendar-only equality `child.request_sha256 == sha(raw)` plus `staged_request.read_bytes() == raw` before promoting the delegated status. Ordinary trusted runs already use identical bytes; this inexpensive check closes the stated cross-layer snapshot contract without rerunning coefficient algorithms.

These are source-inspection findings with explicit trace and proposed scope; no timeout or file-race experiment was run in this static review. Root reported 12 fresh launcher cases plus missing-input/no-overwrite controls before this review. Any corrected launcher has a new byte identity and should preserve a separate focused application receipt; accepted native/frontend/117 executions need not be repeated when their executable bytes are unchanged.
