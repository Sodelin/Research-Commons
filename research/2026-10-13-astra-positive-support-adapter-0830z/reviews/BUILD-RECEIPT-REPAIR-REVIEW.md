# Build receipt repairs: independent follow-up

Reviewer: Astra Rust integration lane, 2026-10-13 09:42 UTC.

**The reported findings are addressed in the pinned repaired sources. No
further blocking evidence-authentication defect was found in this scoped
source review.** This follow-up does not establish Lean compilation success,
native correctness, or publication. No compiler or tests were run by this
reviewer; only source, existing evidence, and hashes were read.

| Earlier finding | Repair reviewed |
| --- | --- |
| Unauthenticated objects in the prepended import path | `build_support.py` authenticates successful selected receipts and their nonempty artifact maps, then rejects every other file in the owned build path before extending `LEAN_PATH`. Unrecognized files are preserved. |
| Resumed audit metadata and historical receipt trust | Fresh resumed receipts require log hashes and a newly parsed audit matching stored metadata. Historical compiler context, RESULT and logs are checked against the fixed previous manifest; origins are compared exactly. Copied artifact hashes remain bound to their specific extensions. |
| Incomplete binding to selected external execution | The new runner additionally compares external receipt module/source/hash/repository/target/import fields with the exact plan, rehashes source and logs, and requires an actual `.olean`. |
| Capture not bound to guard output | Capture verifies complete guard stdout/stderr byte counts and hashes before interpreting events. A successful batch requires one completion summary whose fresh-compile count equals its captured events. |
| Missing interrupted compiler evidence | The orchestrator records a pre-batch receipt/log inventory. On failure, capture reconciles changed files with completed events and preserves unmatched receipt/log bytes, including partial JSON, as explicitly unverified evidence. Base64 retains exact bytes even when diagnostic text is not valid UTF-8. |
| Receipt-write/event-output interruption window | A receipt existing without its completion event no longer causes the interrupted scan to skip that invocation. A complete but eventless receipt is retained with the same unverified status as other unmatched evidence. |
| Audit failure printed as compiler success | Events carry the effective receipt exit code and separately retain the compiler exit code. |

The original reviewed source hashes still match the preserved
`evidence/REVIEWED-*.py` files. The fixed previous manifest hash also matches
the current published baseline manifest. Historical execution is not relabeled
as having used repaired code. Reauthentication of batches whose processes had
already loaded earlier capture code remains a separate execution obligation.

I read all seven malformed-evidence test bodies and the existing guarded
receipt. The recorded command exited 0, with no resource stop, seven passing
tests, 0.502 seconds elapsed and 16,941,056 bytes peak child RSS. Actual stdout
and stderr hashes match the guard receipt. The tests cover truncated guard
output, an omitted completion event, eventless partial JSON and invalid UTF-8,
empty object sets, changed resumed logs, a placeholder axiom, and artifact
extension binding. This is bounded verification of these branches; it does
not exhaust all process-interruption timings or prove the runner universally
correct. In particular, a host or orchestrator interruption still requires
resumption from its preserved pending inventory and available files.

| Reviewed source or receipt | SHA256 |
| --- | --- |
| `build_support.py` | `2e4f5eef27b60c12475553246da8c23aa3ee2ff75416196498cbd946d0c03eb1` |
| `capture_batch.py` | `c748a27508cec46ee243ebc77ab256f515f87fbbb0e5c8c2b28d654d22febad4` |
| `run_external_batches.py` | `387f3469125cc28fcd91d4ee4d03d5eab4190c54b0ba546d9d8ee4c6690364ef` |
| `test_receipt_integrity.py` | `951924f569b593900f63bba10196e95aef8c363e9c287c9f73a642d8f04a0262` |
| `evidence/RECEIPT-REPAIR-0930.json` | `6a7d0451dccd72c9761836fc8e3c6d377b87248e9f7d8a615ac40c2da0996b92` |
| `evidence/receipt-integrity-tests-v1/RECEIPT.json` | `8edf96914040c436fd0288dfedc54e6b7ac7b79cf3350fea3971f1df4b92f6c0` |

The original [review](BUILD-RECEIPT-REVIEW.md) remains the record of the issues
in its earlier source pins. This note supersedes those findings only for the
repaired hashes above.
