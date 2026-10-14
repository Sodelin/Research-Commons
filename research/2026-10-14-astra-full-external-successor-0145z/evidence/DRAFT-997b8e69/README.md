This is an **unexecuted source draft** for a separate 3661-module external
state. It adds no prerequisite to the current 319-module support target.
The existing 3591-module plan, state, receipts, objects, sources and launchers
remain unchanged. The current support closure is still the first actual target.

`external_state.py` exposes
`authenticate_complete(state, repos, lean_bin, pins)`. The fixed new state is
`/workspace/scratch/astra-full-external-0145`. Its exact full plan is the actual
official-query output at
`../2026-10-14-astra-full-accepted-import-query-0100z/evidence/import-query-v2-authenticated/captured/EXTERNAL-PLAN.json`,
SHA256 `0c64ed24f1b9d237a7ccee440e9b360cce7ba797079c02d1b0154473866b1d0a`.
Its first 3591 source records literally equal the active plan. The additional
70 target paths are distinct from every original target path. This is a static
selection fact; no new object has been authenticated or compiled here.

The complete original provenance pin is deliberately **unset**. Both new
entry points and the consumer verifier refuse use until the original closure
finishes and an owner-reviewed, published `PREFIX-PROVENANCE.json` is bound by
an explicit fixed SHA in a reviewed source successor. No caller-supplied flag
can claim this provenance exists. See `PROVENANCE-SCHEMA.md`. This is a natural
condition on reusing the complete original closure, not a new gate on the
existing adapter or its ongoing execution.

`prepare_full.py` first reuses the frozen compiler/repository setup and the
complete dependency verifier, supplemented by exact selected row, source,
log, original command/options, runner/helper and published-origin checks.
Only after those pass does it create the new state. It copies canonical
`0000.json` through `3590.json` and their logs byte-for-byte, saves the selected
source bytes, and writes separate `reuse/NNNN.json` records labelled
`AUTHENTICATED_REUSE`. It never rewrites a historical receipt as a new compiler
execution. Missing early runner or execution fields stay absent in canonical
receipts and `null` in explicit provenance metadata. Original default options,
temporary synchronous elaboration, diagnostics and subsequent Mathlib-only
options remain literal. Earlier objects are reused in their authenticated
original locations, not copied or rewritten.

`build_external_full.py` uses the same pinned compiler setup, artifact helper,
resource helper and original elaboration policy as the current serial builder.
Each explicit invocation compiles at most 1, 4, 8, 16 or 32 of the 70 added
sources. Mathlib options apply only to `Mathlib.*`; package dependencies retain
their established command. Only disjoint new target families and this new
state are writable. Existing partial evidence, failed receipts or unreceipted
objects cause refusal and require a separately reviewed preservation/repair.
There is no automatic retry or next job.

Both entry points require the exact direct frozen guard command: 6 GiB virtual
address space, 4 GiB physical cgroup stop, 900 seconds wall, 600 seconds CPU,
1 GiB output-file cap, 8 GiB disk floor and 1 GiB available-memory floor. They
honor the old and new `PAUSE-BUILDS` markers. The reviewed serial helper retains
one compiler, per-child allocator control and acknowledged suspension around
read-only cache advice. No global settings or guard limits are changed. The
compiler owner must separately confirm an idle lane before any invocation.
This draft adds no detached launcher or environment-replacement guarantee.

After each new compiler returns, its literal receipt records source, imports,
target, exact command, environment, helper, logs, objects and the actual outer
guard directory. Later authentication requires closed guard bytes and the
specific successful module event. A successful module completed before a later
batch failure remains distinguishable from a successful outer batch. Guard
errors are refused. Original batches 042, 057 and 059 remain outer `UNKNOWN`,
with separately pinned recovery authentication, never manufactured receipts.

The complete verifier authenticates every receipt and provenance wrapper before
calling the unchanged `verify_dependency_state` for the full import graph,
actual object hashes and lookup shadowing. Its returned `modules` preserve the
existing fields `module`, `source_sha256`, `receipt_sha256`, and `artifacts`.
`receipt_sha256` always hashes canonical `state/NNNN.json` in plan order; artifact
maps retain absolute target paths. Added `execution`, `original_execution` and
`provenance` fields describe actual origins. The result has no per-call time or
duration and does not inherit the frozen verifier's blanket fresh-execution
description. The full-owned consumer must still establish its own exact
namespace routes after this gate and run its separate theorem/interface/axiom
audits. The external source query is not theorem elaboration, and an aggregate
build would not be a from-scratch rebuild of all components.

Only source reading, metadata comparison and Python AST syntax parsing have
been performed for this packet. No import, test, query, compiler, object scan,
initialization, launch, reuse audit or guard execution has run. This draft
remains subject to independent review and future bounded controls. Python,
the operating system, frozen tooling, actual build receipts, the reviewed
provenance manifest and the native Lean compiler remain explicit trusted
boundaries; no universal implementation-correctness claim is made.
