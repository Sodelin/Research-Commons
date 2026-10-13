# Guarded build continuation

Current checkpoint: the external prefix through2958 has been authenticated by
separate zero-compiler recovery059. Original059 has32 retained successful module
receipts but no original outer guard/capture; its exit status, timing, maxima and
interruption cause remain UNKNOWN, alongside original042/057. The unchanged pending
ORCHESTRATOR-059 is retained. New recovery guard passed8.008s/32.69MB.

Next selected work is2959 `Mathlib.RingTheory.TensorProduct.Finite`, one fresh
batch060 after verified publication and independent recovery readback. Use the
reviewed external-only6GiB virtual/4GiB physical policy and preserve all existing
time/disk/RAM/source checks. A separately reviewed persistent single-job launcher
may be added to reduce transport-related evidence loss; do not count launch as
completion. No compiler is active at this recovery cutoff.

Four new literal base proofs now have actual successful Lake execution and24
standard axiom audits. The selected accepted provider/new adapter/support wrappers/
interface remain uncompiled. Batch054 failure and its separate module2860 repair
remain literal history. Continue with one compiler and distinct batch numbers;
source/evidence publication and ordinary bounded continuation are authorized.

The 32 retained compiler invocations in original 042 were separately
authenticated after reconnection. Its missing original outer guard remains
UNKNOWN; none of the later successful guards repairs that missing observation.
The original recovery proposal and its source/evidence remain unchanged below.

The exact source package is materialized at
`/workspace/scratch/astra-support-sources-0936`. Its readback passed in
`evidence/materialize-source-v2/`, which preserves the source manifests,
configuration and entry points. It retains the original 1613 graph, all 68 G2
sources and original aggregate unchanged. Source integration is separate from
fresh aggregate compilation.

The external state is `/workspace/scratch/astra-support-external-0840`.
`PLAN.json` is the exact copy of `EXTERNAL-PLAN.json`. The first 916 module
receipts match the pinned published execution archive; see
`evidence/PREVIOUS-916-REUSE-AUTHENTICATION.json`. New successful invocations
are captured in each `evidence/external-batch-NNN/MODULE-RECEIPTS.json`.
Outer receipts preserve actual limits, elapsed time, return code and child peak
memory. `evidence/RESOURCE-MONITOR.jsonl` contains periodic physical-memory and
disk samples; those samples do not assert an unsampled peak.

Continue at the next unused batch number only after the preceding invocation
finishes and its receipt/capture is inspected:

```sh
python3 -B run_external_batches_6g.py \
  --first-batch NEXT_UNUSED_NUMBER --batches 3 --batch-size 32 \
  --state /workspace/scratch/astra-support-external-0840 \
  --mathlib-root /workspace/scratch/astra-mathlib-0645 \
  --lean-bin /workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin
```

Run from this packet. Each invocation allows at most three batches of at most
64 fresh modules and stops on a failed guard, failed compiler or `PAUSE-BUILDS`
file. The physical stop remains 4 GiB, external virtual ceiling is now 6 GiB, disk floor 8 GiB,
wall budget 900 seconds per batch and inherited per-process CPU ceiling
600 seconds. Failed or
interrupted state must be preserved and diagnosed before any explicit repair;
the runner refuses to overwrite existing invocation logs.

The index 1734 failure and explicit repair are preserved in
`evidence/SYNCHRONOUS-ELABORATION-REPAIR.json`. Diagnostic samples distinguish
virtual reservation pressure from physical memory use; no desktop incident
cause is inferred. A temporary 4.5 GiB virtual diagnostic also failed; the
successful repair restored the original 4 GiB ceiling and set
`-DElab.async=false`. That setting was later superseded by the original
elaboration mode after the index 2015 compatibility failure described below. The
failed batch 013 capture remains literal; its old receipt is preserved in
`preserved-failure-1734-batch013/` under the external state. Do not regenerate
that historical capture from the later successful live receipt.

Batch 017 stopped on physical pressure during index 1895. The complete original
interruption is captured, including the eventless invocation. See
`evidence/ARENA-AND-INPUT-CACHE-REPAIR.json` for the unchanged-source success
after limiting child glibc arenas and advising completed read-only input pages
out of cache. Both original 4 GiB limits remain. `serial_compile.py` now performs
this housekeeping and flushes begin markers before a sweep. Its sampler pauses
during the sweep; the outer guard is independent. The original interrupted logs
are under `preserved-interruption-1895-batch017/` in the external state. Retain
the literal failed batch capture rather than rebuilding it from repaired state.

`evidence/ORIGINAL-ELABORATION-REPAIR.json` records the exact index 2015 failure
and successful unchanged-source run. Future compiler calls omit the forced
`Elab.async=false` flag, retaining `-j 1`, stack controls, per-child arena limit,
input-cache housekeeping and the original physical/virtual guard limits. The
old failed receipt/logs are in `preserved-failure-2015-batch020/`; the failed
batch 020 capture remains unchanged.

`evidence/VIRTUAL-RESERVATION-REPAIR-v2.json` records the index 2056 virtual
failure and unchanged-source success with a 5 GiB address-space allowance and
unchanged 4 GiB physical stop. No other numerical limit changed. The sampled
successful peak was 4.356 GB virtual and 3.190 GB cgroup memory. An active
background-thread stack and mapped input objects contribute to virtual use;
libuv identity is a source-supported inference, not a native backtrace result.
The compiler and source identities remain unchanged. The failed stack-cache
tunable was not promoted. At that historical cutoff, external/provider guards used `--memory-mib
5120`. The later explicit policy changes only external continuation to 6144;
provider and final Lake profiles remain 5120 until separately reviewed.

The published execution plan contains the actual absolute compiler and source
paths above. The current strict replay scripts require this canonical layout.
A fresh machine must first provision the pinned compiler and Mathlib/dependency
sources using the previous packet's documented source-only bootstrap. A replay
may compile all planned sources; the documented 916 reuse applies only when
their exact successful source/object receipts exist. Moving the source roots
requires a newly authenticated compiler-derived plan and explicit path review;
changing only the command-line path arguments cannot authenticate a different
plan. No relocated execution has been claimed.

After the full external closure passes, use `build_support.py` in guarded
16-module preparation batches with `--prepare-provider`. Its arguments are
`--source-root`, `--external-state`, `--state` (a separate fresh owned state),
`--mathlib-root` and `--lean-bin`. The complete exact accepted provider requires
312 fresh research bodies and seven identical selected Mathlib bodies. The
existing kernel and three emitted proofs may be reused only through their
pinned published receipt and unchanged local objects. Otherwise their exact
source copies must compile afresh.

`run_provider_batches.py` automates at most three guarded preparation batches
of at most 16 fresh modules. It takes the same source/toolchain parameters,
`--external-state`, `--owned-state`, and `--first-batch`. Provider evidence keeps
raw source/receipt/log deltas, including authenticated copies without compiler
events. Its reused generic capture schema is explicitly scoped by the separate
`PROVIDER-SCOPE.json`; provider preparation never reports the adapter complete.

The final native Lake target is `lake build adapter`, with the environment
variables listed in README. It requires completion of every selected receipt,
fresh or authenticated reused artifacts, and actual printed audits for all
seven new theorem heads plus the accepted grid-bound theorem. Preserve failed
elaborations and exact repairs in fresh evidence directories. Do not modify any
accepted provider body or the frozen prior packet to make this target pass.

The independent runner review and repair review are in `reviews/`. Seven
malformed-evidence tests passed without invoking Lean. Capture outputs from
the already-loaded older runner processes (batches 001–007) were separately
reauthenticated; their original captures were not rewritten. New orchestrations
preserve a pre-batch inventory and unmatched partial/eventless receipts after
a stop as unverified evidence.

The current support adapter has no dependency on the missing physical1614
provider. Successful compilation will prove the conditional distinct
positive-support bound; it will not supply a physical COMMON representative,
prove source existence, identify a graph budget, or decide arbitrary G3 inputs.
The exact missing physical-provider hash and obligation remain in the frozen
unified packet's integration handoff. No new remote publication is asserted by
this local build checkpoint.

At 11:41 UTC, batch 024 passed, then batch 025 stopped at unchanged
`Mathlib.Analysis.Normed.Operator.Bilinear` with elaboration errors and no
resource stop. The same source passed using the pinned Mathlib Lake options
`pp.unicode.fun=true`, `autoImplicit=false`, and `maxSynthPendingDepth=3`.
Future fresh `Mathlib.*` compilations use those exact non-linter options; the
runner checks the selected `lakefile.lean` hash. Accepted research-source
compilation options are unchanged. The original failure, diagnostic and
explicit receipt replacement are preserved in
`evidence/UPSTREAM-MATHLIB-OPTIONS-REPAIR.json`. Earlier successful dependency
receipts retain their literal commands and authenticated objects; this does
not claim byte identity or declaration-wide equivalence with canonical
upstream Lake artifacts. Final selected-provider statement readback and axiom
audits remain required.

At 11:46 UTC, batch 027 stopped safely on physical cgroup pressure during
index 2141, after eight successful invocations. Its eventless empty compiler
logs are retained as unverified evidence. Read-only cache advice over the
task's toolchain/Mathlib files reduced cgroup use from 4.17 GB to 1.37 GB; no
files were deleted and no system settings changed. The same unchanged module
and options then passed in 11.85 seconds at the same 5 GiB virtual/4 GiB
physical limits. `evidence/BETWEEN-COMPILER-CACHE-REPAIR.json` binds the failed
batch, successful diagnostic and adopted receipt. The shared helper now advises
the same authenticated input files after a successful compiler exit above
2 GiB cgroup use, including toolchain libraries outside `lib/lean`; active
outputs remain excluded. Five bounded non-Lean helper tests passed. No causal
claim about the desktop incident follows.

At 11:56 UTC, batch 029 had stopped on physical pressure during index 2145.
A clean-cache probe without live advice also stopped. The unchanged source
then passed with own-PID suspension requests around read-only cache advice,
sampling 3.059 GB cgroup use and retaining the 5 GiB virtual/4 GiB physical
limits (72.77 seconds for the compiler/helper, 74.07 seconds for the guard).
The successful diagnostic allowed wall 300/CPU 180 seconds, compared with
120/90 in the failed no-live-advice probe. These are distinct receipts.
`evidence/ACKNOWLEDGED-SUSPENSION-REPAIR.json` preserves the full chain.

The shared helper now requests suspension of its unreaped compiler PID,
observes state T/t/Z within one second, performs cache advice, and always
requests resume in `finally`. It retains the helper's 3 GiB advice threshold
(the diagnostic used 2.5 GiB) and a 0.2-second minimum interval. Six bounded
non-Lean tests passed, including observed suspension and resume. Actual batch
030 then passed one fresh module in 19.02 seconds under the unchanged outer
build limits. Batches 031–033 are limited to 32 fresh modules each. The final
separate interface audit source is `audits/ProviderInterfaceAudit.lean`; it
is prepared but remains uncompiled with the adapter.

The observed T/t/Z status is the process leader status from `/proc/<pid>/status`,
not an independent acknowledgement from every thread. The process-group memory
guard remains authoritative; the scheduling observation does not replace it.

The final custom Lake `adapter` target now also requires the separate
`audits/ProviderInterfaceAudit.lean` module. Its explicit signatures retain
the selected provider premises, exact sparse-polynomial levels, positive
support domain, zero-weight behavior, and the three literal examples.
`audit_support_interface.py` first authenticates the complete existing owned
closure with a zero fresh-compilation budget, then compiles or authenticates
the separate interface audit. Its final output binds the entire owned receipt
ledger, configuration, source, exact arguments, and pinned native Lake binary.
This target update is pending actual Lake execution.

`capture_final.py` requires `--source-root`, `--state`, `--external-state`,
`--mathlib-root`, `--lean-bin`, `--lake-output` and a fresh `--out`. It requires
the exact invocation returned by `audit_support_interface.lake_command`,
this packet's working directory, successful bound guard outputs, another
zero-budget authentication of receipt origins, and matching compiled source,
artifact, log and interface bindings. It exports full source/receipt/log
ledgers and package manifests without binaries. The original916 public
external executions are explicitly authenticated reuse. The export does
not claim a fresh full1613 aggregate, a physical representative, universal
native-code correctness, or verified remote publication.

The final export also requires the frozen guard implementation and exact
900-second wall/600-second CPU, 5 GiB virtual/4 GiB physical, 1 GiB file,
8 GiB disk-reserve and 1 GiB RAM-reserve profile. Seven bounded rejection
and ledger-integrity tests passed in `evidence/final-gate-tests-v3`; their
stdout binds the executed Python source hashes. The earlier repair-pin file
is historical; `evidence/FINAL-GATE-REPAIR-PINS-v3.json` is its successor.
These Python tests do not establish the pending Lean interface or final
Lake execution.

At 18:57 UTC, the reconnected workspace retained batch 042 stdout with all
32 successful compiler events (indices 2499–2530), but no original outer
guard receipt or terminal capture. The original directory and pending
ORCHESTRATOR-040 record remain unchanged. `recover_batch_042.py` authenticated
the full 2,531-module prefix, current source/import selections, artifacts, logs,
unchanged pre-batch inventory and prior 040/041 captures without launching Lean.
Its new guard passed in 7.007 seconds with 32.46 MB peak child RSS, under a 1 GiB
virtual/4 GiB physical readback profile. That is a fresh authentication receipt,
not a reconstructed successful 042 guard; the original outer exit status,
elapsed time, resource maxima and interruption cause remain UNKNOWN.

The append-only evidence is `evidence/recovery042-auth-v1/`;
`evidence/RECOVERED-042-RESUME-PROPOSAL.json` binds its guard and file manifest.
Next proposed work is index 2531, using batch 043 with the existing 32-module
serial policy, only after public checkpointing and coordinator release.
The new adapter and explicit interface audit remain uncompiled.

## Later thread-headroom diagnostic and adoption

Batch054 failed at selected module2860 with `failed to create thread` under
5 GiB virtual /4 GiB physical controls. The original failed receipt and logs
remain archived. Diagnosticv1 compiled the unchanged source but returned2
because an optional procfs children interface was unavailable. A narrowly
repaired read-only monitor then passed diagnosticv2, including375 samples and
25 child-limit snapshots, at6 GiB virtual /unchanged4 GiB physical.
The sampled virtual peak was6,039,928,832 bytes; the failure's exact cause
remains unknown. These outcomes are separate in
`evidence/thread-headroom-2860-v1/` and `evidence/thread-headroom-2860-v2/`.

The reviewed zero-compiler adoption archived the original2860 receipt/logs and
installed the authenticatedv2 result, recorded in
`evidence/THREAD-HEADROOM-2860-ADOPTION.json`. One-fresh-module batch055 passed.
`evidence/EXTERNAL-6GIB-VIRTUAL-POLICY.json` and the separate
`run_external_batches_6g.py` govern further external continuation; the old
5 GiB launcher stays byte-exact. Time, disk, RAM, physical-memory, source and
shared compiler-helper controls remain unchanged. Provider/final Lake profiles
are not changed by this external-only policy. No adapter completion follows
from the dependency repair.

## Recovery after the interrupted 057 orchestration

Batch056 has a successful original guard and capture. Batch057 retained32 successful module receipts and objects through index2925, but its original outer guard and capture are absent. Original057 exit status, elapsed time, resource maxima and interruption cause remain UNKNOWN. The pending ORCHESTRATOR-056 and original logs remain unchanged;058 was not started.

`recover_batch_057.py` authenticated the entire2926-module prefix without launching Lean. Its first readback failed during Git’s threaded index scan; a command-local serial Git scan then passed in9.008 seconds with33.07MB peak child RSS under the same512MiB virtual/4GiB physical readback limits. Both attempts are retained in `evidence/recovery057-auth-v1/` and `evidence/recovery057-auth-v2/`. The successful readback authenticates present evidence; it does not reconstruct the original057 guard. Original042 outer status also remains UNKNOWN.

`evidence/RECOVERED-057-RESUME-PROPOSAL.json` binds the new guard, exact file inventory and resume point2926 (`Mathlib.RingTheory.Polynomial.Subring`). After the verified public checkpoint and independent readback, batch058 will admit one fresh module under the reviewed6GiB virtual/4GiB physical external policy; ordinary serial continuation follows a successful narrow step. The accepted provider, new positive-support adapter and explicit interface audit remain uncompiled.

## Four additional literal base proofs verified

The separate actual Lake test in `evidence/lake-additive-base-v1/` passed unchanged endpoint-linear, zero-constant, level-four-square and level-eight-padding proof sources. Kernel/aggregate and four new literal modules were freshly compiled;916 external modules were authenticated reuse. The explicit24-head axiom audit and28-file text export passed `capture_additive_base.py`. Three older base proofs remain separately reused. The seven support-bound wrappers and this packet’s selected provider/adapter/interface are still uncompiled. See the literal guarded command and `authenticated-export/SUMMARY.json` for the exact scope.
