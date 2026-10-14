# Isolated follow-on import query — unexecuted source draft

This runner is **NOT EXECUTED**. Preparation read existing source/manifests and
parsed the Python AST only. No Lean, Lake, import query, test, materialization or
object-authentication job has run in this packet. The compiler owner chooses a
later quiet execution boundary and the actual resource guard; this file grants
no compiler ownership.

`query_imports.py` takes the exact frozen2305 selection:469 accepted owned bodies
and six Astra source bodies from root2340's isolated materialization at
`/workspace/scratch/astra-unified-extension-sources-2340`. It authenticates original
and materialized byte/SHA256/Git-blob identities, selected import headers, the
materialization selection/Lake configuration, official Lean4.33.1 executable,
Mathlib0df444a360eaa60ab8c11dca51a86af692955474 and all package dependency revisions.
The counts identify a selection; they do not establish mathematical completion.

It reuses the exact nested-comment-aware header parser from frozen2305 and the
official compiler query method of `support0830/plan_external.py` and the frozen
`unified-solver0645/build_mathlib_serial.py`: `lean -j1 -s8192 --src-deps SOURCE`.
The direct source queries use the **actual materialized paths**, with their root
first in `LEAN_SRC_PATH`/`LEAN_PATH`. The observed dependency paths must match the
selected literal header and implicit Init exactly. This makes owned Mathlib
precedence visible and fails on an unexpected provider instead of silently
selecting another version. The source query does not elaborate theorem bodies.

Each query preserves a pre-execution request, exact source copy, command, selected
environment, compiler hash, stdout/stderr, exit/error, elapsed time, before/after
source hashes, resolved dependency paths and dependency-source hashes. It stops
on the first mismatch, timeout, pause marker or failure. Individual queries have
a10s wall timeout; the complete run permits at most550 queries. All commands are
serial and inherit the owner's outer guard/process group. No query starts another
session or automatic retry. An interrupted partial request/log remains partial
evidence; no missing receipt or guard outcome is synthesized.

The second phase uses the frozen external graph walker and its ordering rules,
seeded with the immutable3591 source records. It extends from **only** the two
selected owned Mathlib roots `Mathlib.Algebra.MvPolynomial.Funext` and
`Mathlib.Algebra.MvPolynomial.Polynomial`, whose full source bytes must equal the
selected accepted versions. The new official queries use the upstream source
paths and are separately recorded; they are not substituted for the475 owned
source queries. Existing3591 import edges are authenticated reuse of the pinned
historical source-query plan; they are not all freshly queried. All3591 source
body hashes are rechecked, and the original plan is copied byte-exact before
extension. No existing object or compiler receipt is inspected for reuse.

The sole output argument must name a new direct child of `/workspace/scratch`
starting `astra-follow-on-import-query-`. It writes only that new directory.
The active319 selection,3591 plan, materialized sources and all object files stay
unchanged. The generated `EXTERNAL-PLAN.json` retains historical target paths only
as **unauthenticated existing object candidates**; the query runner never writes
them and is not a builder. A future isolated builder must authenticate the exact
source/compiler/import/options/receipt/object correspondence before reuse and
must choose its explicit output policy. Source availability is not object
compatibility or an executed aggregate.

The runner refuses unbounded address-space/CPU/file limits and limits exceeding
6GiB AS/600s CPU/1GiB file. It does not replace the frozen guard's4GiB physical
stop,8GiB disk and1GiB RAM floors. A proposed owner invocation is:

```sh
python3 -B research/2026-10-13-astra-unified-solver-0645z/guard.py \
  --out NEW_EXCLUSIVE_EVIDENCE_DIRECTORY --cwd /workspace/Research-Commons \
  --wall 300 --cpu 180 --memory-mib 6144 --file-mib 256 -- \
  python3 -B research/2026-10-13-astra-follow-on-import-query-2355z/query_imports.py \
  --out /workspace/scratch/astra-follow-on-import-query-2355-v1
```

This command is a proposal, not an execution receipt. The owner may choose a
shorter bounded profile; changing selection, query semantics or helper pins
requires a reviewed successor. Existing PAUSE-BUILDS is checked before the run
and every query. No source/body modification, Lake configuration replacement,
native rebuild, theorem/axiom claim or physical-representative conclusion follows
from this packet. The missing exact `G4ProtectedCommonRepresentative` provider
remains the separate authenticated-interface gap documented in frozen2305.
