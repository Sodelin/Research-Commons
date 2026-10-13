# Exact positive-support adapter — source and dependency checkpoint

Contributor: Astra integration lane, 2026-10-13. Status: **new adapter uncompiled**.
This sibling packet preserves the published unified package unchanged. It follows
[dot's coordination request](../2026-10-13-dot-coordination-0823z/README.md).
That request's older statement that new Lean compilation was unverified is
superseded by the published unified packet's actual kernel and certificate
[receipts](../2026-10-13-astra-unified-solver-0645z/LEAN-INTEGRATION.md).

The target is a conditional bound on the number of **distinct values with
positive mass**, at most L-1, from an exact supplied certificate. It is not source
existence, a physical representative/hybrid budget, or arbitrary-input G3 closure.
Zero-weight values are excluded from the support set and unconstrained in the
general theorem; repeated values count once. The survival domain remains `(0,1]`.

The closed execution checkpoint after batch 055 authenticates the selected
external prefix through index 2861. Batch 054 remains failed; separate diagnosticv2 and explicit adoption recovered
its module2860 result. The other closed guards retain their literal outcomes;
their literal receipts and remote publication readbacks distinguish execution
from reuse. The [055 handoff](evidence/LEAN-LANE-055-HANDOFF.json) records
the independent terminal readback and no-active process observation at its cutoff.
The accepted provider, new adapter and separate interface audit remain uncompiled.
Original 042's missing outer guard remains UNKNOWN despite successful later
authentication of its retained module results.

Incoming hand-reviewed work is routed by the
[exact-source integration catalogue](../../communications/astra-incoming-integration-registry-2003.md)
and its JSON registry, with additive later intake receipts. It preserves calibrated-target BOTH forcing, distinct
INDEPENDENT diagnostics, precise inherited hypotheses and remaining formalization,
physical and effective-decision obligations. This catalogue does not enlarge
compiled Lean or native solver results.

## Exact accepted provider

`DotG4.ActualPositiveGridUniqueness.positiveCertificateGrid_card_lt` is in the
selected `G4ActualPositiveGridUniqueness` body SHA256
`ee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787`.
It assumes that `sparsePolynomial (momentLevels L) c` is nonzero and concludes
that `positiveCertificateGrid L c` has cardinality strictly less than L.
`momentLevels L` consists of levels 1 through L; level k has exponent `k.choose 2`.

[PROVIDER-SELECTION.json](PROVIDER-SELECTION.json) preserves the complete exact
accepted1613 dependency selection: 319 source bodies, including seven selected
Mathlib bodies. All are present. No missing physical1614 provider occurs in this
closure. Fresh compilation is needed to obtain unavailable compatible objects;
it does not mean G2 was missing or its accepted statements changed. The adapter imports the complete original provider; no truncated body,
synthetic replacement, axiom or requested cardinality conclusion is an input.

The new [adapter](lean/Astra/PositiveSupportAdapter.lean) binds the emitted
polynomial pointwise to the exact coefficient/level polynomial, derives its
nonzeroness from a concrete nonzero evaluation and applies the accepted grid
bound to the image of positive-mass atoms. A direct certificate theorem derives
roots from nonnegativity and exact zero weighted expectation. The
[literal wrappers](lean/Astra/EmittedSupportExamples.lean) reuse the actual emitted
proofs for moments at 1/4, 1/2 and 1, with levels 1, 2, 3 and exponents 0, 1, 3. Those copied
proofs and the arithmetic kernel retain their exact published bytes.

## Execution plan and resource boundary

[EXTERNAL-PLAN.json](EXTERNAL-PLAN.json) is the actual official-compiler import
closure: 3591 external modules, 916 authenticated existing source/object receipt
pairs, and 2675 additional sources (39.27 MB) uncompiled at the planning cutoff. Its SHA256 is
`ef775a7223500314359a9ed02a87d207b18eacda9cddfa5a8990c5e1a8e43f10`.
[The import-query receipt](evidence/external-import-plan/RECEIPT.json) passed in
93.6 seconds and did not compile these sources. After the external closure,
312 selected research modules remain to compile; the seven owned Mathlib bodies
match the exact selected upstream bytes and can reuse their authenticated builds.

This is hours of serial compilation at observed prior rates. Source and receipt
checkpoints precede expensive work. Current compilation uses 32-module batches,
one compiler at a time, a 4 GiB physical cgroup stop, 6 GiB per-process virtual
ceiling, 8 GiB disk floor and 1 GiB available-RAM floor. The measured virtual-only
adjustment and earlier failures are preserved below. Actual failures and resource
stops must be preserved and diagnosed before resuming. No desktop build, firmware
change, network-policy change or unrelated-file deletion is involved.

The missing physical-provider obligation remains exactly as documented in the
[published integration handoff](../2026-10-13-astra-unified-solver-0645z/INTEGRATION-HANDOFF.md).
Freshly proving this support adapter will not discharge that obligation.

## Reproduction entry points

`plan_external.py` reauthenticates the previous 916 object/source receipts, then
queries official Lean for the extra import closure. `run_external_batches.py`
allows at most three guarded batches of up to 64 modules per invocation; current
invocations explicitly select `--batch-size 32` and stop on any failure. A `PAUSE-BUILDS` file in this packet prevents the next batch from
starting. Completed batches retain full per-module text receipts without binaries.
The execution remains incomplete: completed batches are evidence of those exact
dependency invocations, not completion of the mathematical adapter. Batches
001 through 012 passed. Batch 013 stopped at an unchanged Mathlib source with
an internal memory failure. That source subsequently passed with synchronous
elaboration under the original 4 GiB virtual and physical limits; batch 014
then passed a one-module continuation. Batches 015–017 were running serially
at the 10:28 UTC checkpoint. The complete failure, bounded diagnostic probes
and exact receipt repair are preserved in
`evidence/SYNCHRONOUS-ELABORATION-REPAIR.json`. Invocations at that cutoff used
`-DElab.async=false`; no mathematical source was changed for this repair.

At the 11:05 UTC checkpoint, batches 015 and 016 had passed. Batch 017 stopped
on the unchanged physical-memory threshold during index 1895. Its unchanged
source later passed with per-child `MALLOC_ARENA_MAX=1` and advisory release of
completed read-only input-cache pages, with both original 4 GiB limits retained.
`evidence/ARENA-AND-INPUT-CACHE-REPAIR.json` preserves the failed probes and exact
successful receipt. Batch 018 passed a one-module continuation; batches 019–021
were starting serially. `serial_compile.py` records cache-advice begin/end events
in the outer guarded log. Its sampler pauses during a sweep; sampled peaks do
not establish unsampled peaks. Four bounded non-Lean helper tests passed,
including child cleanup when logging itself fails.

At 11:18 UTC, batch 019 had passed. Batch 020 exposed a separate compatibility
failure: `Mathlib.Topology.UnitInterval` could not resolve its private helpers
under forced synchronous elaboration. The exact unchanged source passed with
the original compiler elaboration mode and the same resource controls. Future
builds restore that original mode; earlier successful objects remain authenticated
reuse. `evidence/ORIGINAL-ELABORATION-REPAIR.json` preserves both executions.
Batch 021 is the narrow continuation check. The new adapter is still uncompiled.

At 11:29 UTC, batch 021 had passed. Batch 022 then hit the virtual-address
allowance at index 2056. The unchanged source passed with a 5 GiB virtual
allowance while retaining the 4 GiB physical stop; sampled cgroup use was
3.19 GB. Future orchestration uses this measured virtual-only adjustment.
`evidence/VIRTUAL-RESERVATION-REPAIR-v2.json` preserves both executions and
distinguishes observed reservations from inferred runtime attribution. Batch
023 passed a one-module continuation; batches 024–026 are starting serially.

`materialize_support.py --out FRESH_DIRECTORY` emits and reads back the entire
original1613 source graph, unchanged original entry points, the new sources,
`AstraPositiveSupport` and the combined source entry `AstraSupportUnified`.
The original and additive source manifests remain distinct. The current
materialization/readback receipt is `evidence/materialize-source-v2/`; later
source repairs require a new materialization receipt.

After the external closure is complete, `build_support.py --prepare-provider
--batch 16 ...` prepares only the exact accepted-provider dependencies, with
authenticated reuse of the seven identical owned Mathlib modules and the
published arithmetic kernel/emitted proofs. Each original research source is
compiled with its exact selected body and imports. A final native `lake build
adapter` requires every selected receipt and the explicit theorem audits; a
partial preparation cannot report adapter completion. Set `ASTRA_SUPPORT_SOURCES`,
`ASTRA_SUPPORT_EXTERNAL_STATE`, `ASTRA_SUPPORT_STATE`, `ASTRA_MATHLIB_ROOT` and
`ASTRA_LEAN_BIN`, and run the Lake command under the previous packet's guard.
`lake build provider_batch` is explicitly only one preparation batch; `lake
build materialize` requires a fresh source-output directory. Native Lake
loaded the configuration successfully in `evidence/package-config-v1/`; that
check did not compile the adapter. Actual provider and adapter targets remain
unverified until their execution receipts appear.

The independent [runner review](reviews/BUILD-RECEIPT-REVIEW.md) identified
receipt-authentication and interrupted-log preservation gaps. The reviewed
versions are preserved in `evidence/REVIEWED-*.py`; the repaired runners reject
unrecorded objects in the owned import path, rehash and re-audit resumed compiler
logs, pin the published previous receipt, and reconcile captures against guard
output hashes. New orchestrations save a pre-batch inventory and preserve
eventless or partial receipts as unverified evidence after a stop. Seven bounded
malformed-evidence tests passed in `evidence/receipt-integrity-tests-v1/`; they
invoke no Lean compiler and do not verify the mathematical statements.

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
