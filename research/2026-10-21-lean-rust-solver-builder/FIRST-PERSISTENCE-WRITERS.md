# Selected first-persistence writer map and required owner binding

SOURCE REVIEW ONLY. No writer implementation, installed Linux callback,
recipient export, identity change or runtime execution is supplied here.
The existing workflow remains disabled. RECORD-WRITER-GAP.md is authoritative
for the active execution hold.

| Selected boundary | First plaintext path observed in source | Why outer stdout encryption alone is insufficient |
| --- | --- | --- |
| Original guard | Exclusive stdout/stderr file handles passed directly to Popen; later RECEIPT.json | Child streams hit files before a later wrapper can seal them |
| Original MCP bridge | incoming request bytes; launcher.stdout/stderr files | Input is persisted before the guard subprocess starts |
| Original runtime | REQUEST.json; save() uses exclusive open plus json.dump | Internal request/result files bypass the guard stdout channel |
| Existing native RC1 bridge | REQUEST.rc1; child stdout/stderr; execution/result JSON and RESPONSE.rc1 | These writes precede an outer wrapper; temporary executable staging has a separate source/build classification |
| Support composition driver | acquisition JSON, RESULT.json and printed full report | Both nested files and outer stream need the actual sink |
| Bank composition driver | acquisition JSON, NATIVE-OBJECTS/RESULT projections and full report | Output identity metadata is still a runtime record |
| MCP composition driver | RESULT.json and printed report | A projected result is also covered before its first write |
| Lake v4.33.1 configuration loading | ConfigTrace JSON/locks and configuration elaboration before target evaluation | A target-level UNBOUND error is reached too late to gate these writers; admission must precede the first Lake invocation |
| G6GeneratedChartAudit Lean elaboration | run_cmd directly calls IO.FS.writeFile for AUDIT-OWNED.json | Compiler stdout sealing does not mediate an elaborator's internal file writer |

RECORD-WRITER-MAP.json pins these actual source bytes and line candidates.
This is a SELECTED inventory, not complete transitive/native-loader coverage.
Original solver/provider/native-loader writers and failure/recovery paths must
also be traced before closing the admission. Source/build objects and generated
proof publication require explicit source/data classification; a public
synthetic input is not an exception for raw/projected runtime records.

## Required binding, not a fabricated callable

The existing privacy owner must supply the authenticated current public
recipient, exact writer/codec source and executable/callable, and ORIGINAL
controller-owned domain/stream/operation/sequence/prior-frame context.
The known phone public-recipient codec is a reusable primitive; its descriptor
does not install a Linux writer or allocate a journal operation.

Validate the binding before creating any raw output path or launching a child.
Capture stdout/stderr in RAM and seal through the real sink BEFORE file/temp/
database output. Change nested raw JSON/request writers too. Retain the complete
original returns before reviewed projections. Required encrypted reservations,
UNKNOWN/stop/failure/tombstones remain owned by the original controller.
A failed/missing sink stays RAM/refusal, never plaintext or a fresh-ID retry.

The selected frame primitive permits3MiB plaintext/4MiB encoded frames and
512KiB payload chunks. A long compiler stream needs an actually supplied
bounded framing/append contract preserving original stream/file limits and
required recovery; a single frame is not the existing64MiB/16MiB stream policy.
Do not invent the five context fields, claim sender authentication from public
encryption, transfer the private identity or create another key.

Preserve original wall/CPU/RAM/disk limits, stop precedence and process cleanup.
A new I/O/writer integration has new source hashes and needs actual evidence;
it cannot borrow the old unchanged-runner/profile acceptance. The existing
supervisor remains the reuse base. No new worker or compiler action follows
from this source map.

Only after every selected first writer is actually mediated may raw traces be
persisted encrypted and genuinely redacted mathematical dispositions published.
The full goal and independent source/provenance/cast work remain active.

LAKE-FIRST-WRITER-REVIEW.md supplies the exact official source hashes and order.
This is a source finding; no new Lake process was run.

NATIVE-WRITER-REUSE-REVIEW.md now pins the actual existing public codec,
local-Vault helper and pure v2 exact sink/ArtifactKind policy. Its bounded
helper is not a compiler-tree writer and the policy is not a writer API.
The authenticated original controller/recipient/sequence/transport remains
UNBOUND; no duplicate codec, private-key transfer or invented grant follows.

CARGO-FIRST-WRITER-REVIEW.md pins the official Rust1.90 Cargo submodule's
internal diagnostic cache, conditional build-script streams and compiler-query
cache. These bypass outer stream sealing. CARGO_CACHE_RUSTC_INFO=0 disables
only the selected query cache in the new source proposal, not the other writers.
No new Cargo/compiler job ran and no workflow/profile changed.
