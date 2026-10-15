# CM-T02 bootstrap thread-startup source disposition

Record LANE3-CM-T02-BOOTSTRAP-STARTUP-01. Existing lane3 coordinator01a1252c. 2026-10-15 18:13:09 UTC. This is a focused source/config disposition for the SAME desktop operator's selected correction, not a new worker, guard implementation or compiler run.

## Disposition

The operator's distinct corrected bootstrap attempt is compatible with the exact pinned Lean4.33.1 source: retain `LEAN_NUM_THREADS=1`, add `LEAN_STACK_SIZE_KB=16384` and `LEAN_IMPORT_WORKERS=1`. Retain the actual8GiB address-space guard,600s per-process CPU,1200s whole bootstrap command,16MiB per log,1GiB file/core0,50GiB disk/12GiB host-MemAvailable floors and one inherited CPU affinity. No raised limit, installed runtime, source-proof change, full library/research rebuild or generic human/owner reapproval is required for that separately recorded attempt under authorization11.

This is SOURCE/CONFIG COMPATIBILITY, not a guaranteed fix, serialized-process proof or runtime PASS. The failed receipt does not expose the pthread errno; address-space pressure from default stack reservations is a supported hypothesis, not an independently observed cause.

## Exact pinned source

All lines below were independently fetched/read at Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, not inferred from a current branch.

| File | Git blob | Relevant source |
| --- | --- | --- |
| [runtime/thread.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/thread.cpp) | `3f21bc76761207656a0df934a5fbf8b8803f84b1` | lines23–28 default64-bit lthread stack1GiB;76–77 setter adds128KiB buffer;132–140 pthread-create failure throws the observed message;170–178 reads LEAN_STACK_SIZE_KB;192–195 applies it before lean_run_main launches its main thread |
| [runtime/thread.h](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/thread.h) | `71513b13ed1f8a13508c14147b8870bdfaebfb38` | line14 defines128KiB stack buffer;53 gets std::thread::hardware_concurrency |
| [runtime/object.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp) | `5237296cb0bf8009837b3f4fa08f55112de576f6` |1111–1126 reads LEAN_NUM_THREADS for native runtime task-manager initialization; otherwise hardware concurrency |
| [util/shell.cpp](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/util/shell.cpp) | `29b859887e2ca380b30216242fa02c95f291cb1a` |324–326 reads stack environment before CLI option processing;353 creates shell task manager; explicit --tstack can override stack setting |
| [Lean/Shell.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Shell.lean) | `3f73f6fe35d11cbccd9b6effe1bafad030fdbdce` |219–237 compiler-shell default workers follow hardware concurrency; --threads/-j is distinct from native LEAN_NUM_THREADS |
| [Lean/Elab/Frontend.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Elab/Frontend.lean) | `965a761b628ebc7b7c780c7a6d12fde6e2e9b339` |211–217 default importer workers=min(hardware,4), environment override then max1, spawns that many striped IO tasks |

16384KiB requests16MiB, with the128KiB library buffer making the configured lthread reservation16,908,288B. That reduces the default reservation; it does not enlarge the8GiB AS guard. Stack overflow or a different thread failure on the corrected attempt remains an operational stop/UNKNOWN, not a mathematical NO.

Do not replace these with `LEAN_MAIN_USE_THREAD=0`: that would instead change use of the main OS stack and is NOT the operator's selected correction. No unsupported Lake `--threads` flag is added. `LEAN_NUM_THREADS=1` is a real native-runtime control, but it is not a hard thread/process limit and does not establish the compiler-shell worker count. The known frozen proof Lake script uses explicit Lean `--threads=1`; that fact must not be generalized to all cache-bootstrap children.

## Actual failure and residue evidence

Existing operator/root supplied SELECTED-CACHE-01.json:5269B/SHA25672c3dbd8b4afb73a74019cd19c7e324107b4a9be6c8cfc0cc9823d8ceb83fce1. Hash provenance is the bridge's independent raw-file check; lane3 received the complete body and does not claim a new local raw-receipt read.

The first selected helper attempt ran18:06:57–18:07:25UTC and exited-6 with98B stderr, stdout0, complete pipe EOF, retained leader identity and `group_cleanup_unconfirmed`. Preserve that exact failed receipt and the generated config/setup artifacts. It created no Cache executable/oleans or downloaded cache objects. Eight locked source revisions and the authenticated9,032 Git source blobs/101,726,702 source bytes are source acquisition results, not compiled dependency acceptance.

A separate read-only /proc inventory by the SAME operator at18:08:28UTC found no members of own failed PGID6575. Retain this as a LATER observation; it does not rewrite the immediate cleanup-uncertainty receipt or make EOF proof of cleanup. Current exclusivity/residue checks before the corrected launch stay with that operator. No competing compiler/operator is selected here.

## One bounded correction

Use the same absolute Linux4.33.1 Lake, offline/no-cache package-manager mode, exact authenticated Mathlib checkout, eight unchanged dependency commits, official master/legacy cache scope and all nine selected roots. Keep the bootstrap attempt and log/output/receipt namespace distinct from the failed attempt and from proof EXECUTION-01. Record the exact three startup controls, current runtime/shared-library identity, actual bounds/affinity and produced native/helper/object facts.

There is no automatic loop. On nonzero/cancel/limit/stack/thread/unknown dependency or cleanup uncertainty, stop, preserve the full evidence and return the exact diagnostic. No unplanned native Mathlib or311-module research build is an alternative. This source disposition adds no approval condition beyond the operator's actual admitted finite scope; do not ask Nolan or the source owner an unchanged question.

## Final proof manifest consequence

These controls are currently selected for the BOOTSTRAP environment only. The sealed R2.1 proof runner `721d6145...` constructs its own PATH/LANG/LEAN_PATH environment; it does not forward these three startup controls. Therefore the later proof must NOT be described as inheriting this workaround. If the corrected bootstrap validates these controls, final proof admission must explicitly bind a reviewed minimal environment profile/change (new runner/config pin where bytes change), retaining original source/reviews, fixed proof limits and the still-unused900s record. That is a new concrete runtime/config fact, not another repair of the closed R1 identity logic. No sealed source or runner is silently edited here.

Actual compatible closure/core/runtime objects, complete authentication manifest/import order, fresh companion/Lake metadata inventory, actual kernel/resource/capture prerequisites and byte-specific final admission still precede the four-module proof. Cache completion alone is not proof readiness.

No runtime probe, compiler, helper execution, download, process signal or resource-limit change was performed on this cloud lane. Source reads and disposition only. Proof owner record remains RESERVED_NOT_STARTED; old3504 and Omni/Subspace stay paused, and Rust remains a separate package.
