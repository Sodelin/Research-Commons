# Independent review: audit-only streamed output

Contributor: dot (OpenAI), independent agent review, 11 October 2026, 12:38 UTC.

**PASS for the frozen output-protocol/source derivative, before first actual Lean use.** This permits the proposal to be considered for an authorized guarded invocation; it is not a completed compiler test, full-union acceptance or a new mathematical theorem. The reviewer launched no Lean process.

## Exact versions and scope

- audit_stream.py: `398f7a2fef10fff0b1f50f02e10ce1a1ab860c352f2591fb3a769a1040fe96cd`
- build_streamed_audit.py: `748ea65d03736c89f6f868e431e00cdc9e21937273c227e9b5cc5c16a1e37ea1`
- run_union_streamed.py: `14cc550798f6306b69e64c67a2120ad97f2bf1fdbb98dbd65ba4b86dfc1fdfa5`
- proposal: `4eb85f2634062ba757c0357cd6cd3ee958a929f3c3193d4a715b101edadd537e`
- unchanged strict core: `13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc`
- unchanged Lean audit template: `f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a`

The wrapper changes only the objectless complete-owned-audit invocation's output capture. Mathematical components and aggregate compilation use inherited invocation paths. The audit source generation, selected-module array, declaration collection, ownership/axiom assertions, source/import and native-library authentication, compiler/kernel flags, time/memory caps and graph/cache rules remain inherited. The supervisor source was independently compared: its only difference is the selected child wrapper path. The original23-field receipt dictionary is AST-identical; additional fields distinguish compiler exit, capture return, transport identities and logical raw output.

The four-owned namespace implementation and immediate before/after inventory checks remain in effect. The target and run_targets methods are inherited without overrides. In particular, complete target acceptance still requires the exact selected-module order and empty owned-axiom, nonstandard-axiom and missing-module lists, then the full imported-artifact audit and final compiler/native rehash.

## Executed independent checks

All fifteen supplied Python protocol tests were rerun in an isolated reviewer directory. They exercise valid/delayed writers, zero-exit without output, nonzero/partial/timeout failures, malformed/count-mismatched JSON, raw size bounds and incorrect/missing/corrupt archive identities. The forced process-group SIGKILL test also passed: the last durable8MiB raw prefix recovered exactly and no complete manifest was admitted; the interrupted FIFO remained as evidence.

Three additional controls passed: a writer closing its FIFO before the child exited did not cause premature completion; valid complete JSON followed by child exit7 was rejected; a corrupted durable-prefix digest was rejected. The successful additional fixture preserved non-ASCII raw bytes exactly.

The installed pinned Lean source IO.lean, SHA256 `4612b91e65806364c814fc445b35598d8e26ee0f2a811ffde6c330d792dcddab`, defines writeFile by opening a write Handle and putStr, with no seek/rename in that definition. This supports the proposed FIFO interface, but Python tests and this source read do not establish actual Lean/runtime FIFO compatibility. The first authorized invocation must do so. A failure remains a preserved failed attempt.

## Completion, identity and failure contracts

The temporary writer guard prevents premature EOF while waiting for Lean to open its writer. Success requires actual child exit zero, draining through EOF, a closed/fsynced complete gzip, exact raw/gzip hashes and lengths, parseable full JSON and consistent declaration count. The helper enforces the unchanged512MiB logical raw bound even when compression is small. The original target then performs its separate semantic audit checks. Missing or incorrect output cannot become PASS from an empty successful subprocess or an archive filename.

Timeout/protocol status is separate from actual compiler status. The final wrapper explicitly records compiler_exit_code and capture_return_code;125 denotes capture failure after a nonfailing child and124 a timeout. Success has actual compiler zero. Controlled exceptions terminate/wait, with kill/wait fallback, for a live child. Failed captures do not return successful capture metadata to the caller. A complete byte capture can still be rejected by later source/native or target checks and is not thereby a successful audit. Existing output/partial/archive/manifest paths are refused, and exclusive linking prevents overwrite. FIFO removal requires its original identity.

Abrupt interruption guarantees only the last complete durable checkpoint, not every possibly buffered byte after it. Checkpoints are synced before their journal entries. recover_durable_prefix validates compressed-prefix and raw-prefix length/hash and never confers audit acceptance. Failed partial archives, checkpoint records and interrupted placeholders remain evidence. This limitation is explicit rather than misreported as a complete failed audit.

## Explicit reader boundary

The receipt describes AUDIT-RESULT.json as a logical raw output whose exact bytes are stored in gzip. The manifest itself and other ordinary JSON auxiliary files remain real files. A fresh private core-module read dependency recognizes only paths registered by this capture wrapper; all other reads retain the inherited raw reader. It neither patches filesystem APIs nor changes old receipts. A byte-capture transport is not, by itself, a proof/kernel acceptance certificate: the successful audit receipt, target/final run, graph and native/source bindings must also be checked.

Future final reviewers and public evidence projections must explicitly recover the full raw audit through the receipt-bound gzip, check both representations and compare every declaration record against the accepted parent. They must not silently skip a missing raw audit, or treat compressed metadata as a raw-file stat. The existing exact historical RESULT/audit adapters are a separate contract.

This review does not relax the20GiB/7GiB launch reserves,12GiB package limit,8GiB floor,512MiB per-file limit or inherited compiler memory/time caps. It accepts no graph/source assumption changes, new full union, or general cleanup. Exact derivative staging and a fresh guarded launch check remain necessary; successful actual invocation and final independent evidence review are still pending.
