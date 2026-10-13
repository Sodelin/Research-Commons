# Lean source selection and execution contract

Verified status: the complete accepted1613 source selection and final new
kernel have been materialized and independently read back. The final kernel,
its aggregate and all three emitted certificate proofs have freshly compiled
through native Lake targets. The full `AstraUnified` source aggregate has not
been freshly compiled. No missing physical provider has been replaced by an
axiom, a weaker theorem, or a presumed recovery.

`materialize.py` authenticates the immutable accepted1613 dependency graph
(`768e587ffb189b3700aa4acc82853dcced49477b80c028d70e055d40cf65ff13`),
then every selected body. It retains exact module names, original import rows,
all original roots, and the eleven owned `Mathlib.*` source paths. Those eleven
bodies also match the pinned upstream Mathlib source byte for byte. It emits:

* `Accepted1613.lean`, with original aggregate SHA256
  `bb2e98be6151f3ee9379f247cc8e8f2e47bfcbaaff991c331ef6d3298a49bf19`;
* `AstraKernel.lean`, importing the newly supplied semantic kernel;
* `AstraUnified.lean`, importing both aggregates;
* an ordinary Lake source package and complete `SOURCE-SELECTION.json`.

Every current G2 source is retained with its original selected imports. G1,
binary-M3 G5, and all older selected work remain in the original aggregate.
`verify_sources.py` reads back every materialized source and rejects extra Lean
modules outside Lake's build directory. Source integration does not certify a
fresh build of the combined aggregate or mathematical completion of the masters.

## The new proof component

`Astra.CommonCertificateKernel` proves nonnegativity of weighted square terms
on `[0,1]`, exact zero-expectation restriction of positive-mass atoms, and its
joint-configuration/positive-bank consequence. Zero-mass configurations remain
unconstrained. Joint coordinates need not be independent. It also proves the
specific singleton acquisition polynomial's identity, nonnegativity,
annihilation and nonzeroness. This is a bounded sufficient acquisition rule.

The original actual-source, sparse positive-root cardinality, and physical
reduction statements remain the responsibility of their exact accepted
providers. The kernel does not assume or prove that a source exists, supply a
physical representative, validate a graph parser, or classify an arbitrary G3
input. Generated per-certificate Lean files can instantiate the kernel with
literal rational coefficients and moments. Their compiler acceptance is a
separate receipt from Python/Rust acceptance.

## Lake targets and reproduction

The packet's Lake file has four distinct targets:

| Target | Meaning |
| --- | --- |
| `kernel` | Fresh serial compilation and axiom audit of the new kernel/aggregate. Requires exact prepared external objects. |
| `materialize` | Authenticate and materialize the complete original graph plus new sources; no compiler. |
| `accepted_baseline` | Rerun the public1613 packet's original verifier. Preserves the distinction between fresh aggregate and historical authenticated component reuse. |
| `full_replay` | Refuse before invoking the historical adapter: its compatible accepted object/native closure is unavailable and its original resource prerequisites exceed this run's conservative policy. |

Set `ASTRA_LEAN_BIN`, `ASTRA_MATHLIB_ROOT`, `ASTRA_MATHLIB_STATE`, and a fresh `ASTRA_LEAN_OUTPUT` for
`kernel`; set a fresh `ASTRA_SOURCE_OUTPUT` for `materialize`. Run commands
through `guard.py` with serial compiler scheduling. The generated ordinary Lake
source package also exposes `AstraKernel`, `Accepted1613` and `AstraUnified`
libraries; a broad unguarded downstream build has not been executed here.

The exact toolchain is `leanprover/lean4:v4.33.1`, binary SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib is pinned at `0df444a360eaa60ab8c11dca51a86af692955474` and its eight
manifest dependencies are pinned individually. `build_mathlib_serial.py` asks
the official compiler for actual source imports, creates a dependency-first
plan, and builds only the requested narrow closure. Each source compilation
has source, command, output and artifact hashes. Resume accepts only unchanged
successful receipt/artifact pairs. It does not reuse unreceipted objects.
The kernel build reauthenticates every external source/object receipt and
rejects object shadowing before importing the prepared closure.

For a fresh machine, provision the official compiler using `provision_lean.py`,
clone Mathlib at the exact revision above, then run
`bootstrap_mathlib.py MATHLIB_ROOT LEAN_BIN FRESH_LOG_DIR --sources-only`.
This prepares the eight pinned source dependencies without requiring cache
access. Run `build_mathlib_serial.py --mathlib-root MATHLIB_ROOT --lean-bin
LEAN_BIN --state STATE_DIR --batch 128` repeatedly under the guard, retaining
each distinct outer receipt. The final `complete: true` reports a complete
selected external import closure. Inspect and preserve any failure before
resuming; the runner deliberately refuses failed or altered receipt pairs.
`capture_lean_receipts.py` packages the complete text evidence without binaries.

For each source-build batch and kernel/test invocation, the successful resource
configuration is `guard.py --out FRESH_RECEIPT_DIR --cwd PACKET_DIR --wall 900
--cpu 600 --memory-mib 4096 --file-mib 1024 -- COMMAND ...`. Here 4096 MiB is
the per-process **virtual address** ceiling; the separate physical cgroup stop
remains 4 GiB, disk floor 8 GiB and available-RAM floor 1 GiB. Do not run another
compiler concurrently. Set `MIMALLOC_ARENA_RESERVE=16384`, `LEAN_NUM_THREADS=1`,
`LEAN_STACK_SIZE_KB=8192`, and `LEAN_IMPORT_WORKERS=1` before invoking native
Lake. The source compiler always receives explicit `-j 1 -s 8192`.

With the prepared state, `lake build kernel` runs the default audited kernel
check. `lake test -- --extra-source CERTIFICATE_1 --extra-source CERTIFICATE_2
--extra-source CERTIFICATE_3` runs the audited kernel and all three explicit
certificate proofs in one serial job. Each command requires a different fresh
`ASTRA_LEAN_OUTPUT`; it copies the exact compiled sources beside command,
output, source/object hash and axiom receipts. Compiler binaries stay in scratch.

The complete successful execution chain is:

| Evidence | Actual result |
| --- | --- |
| `evidence/MATHLIB-SOURCE-EXECUTION.json` | All916 selected external sources compiled serially; exact source/import graph, command, stdout/stderr, artifact hashes, prior plans and failures preserved. |
| `evidence/lake-kernel-final/` | Native `lake build kernel` passed; final kernel and aggregate freshly compiled, all eight theorem axioms printed. |
| `evidence/lake-generated-certificates-real-repair/` | Native `lake test` passed for final kernel/aggregate and the three unchanged emitted proofs from `unified-emitter-real-repair-cases/correlated-menu/`. Twelve additional certificate theorem audits passed. |
| `evidence/lake-materialize-final/`, `evidence/source-config-readback-final/` | Entire source selection and build configuration materialized, then independently authenticated. |
| `evidence/final-source-selection/` | Exact source manifest, Lake configuration, entry points, toolchain and new source copies; original bodies remain in the immutable accepted source store. |
| `evidence/materialized-lake-config-loader-repair/` | Official native Lake loaded the generated configuration with `check-build`; no aggregate/library build is implied. |
| `evidence/lake-accepted-baseline/` | Original public1613 verifier passed; historical receipts reauthenticated. |
| `evidence/lake-full-replay-blocked/` | Expected failure before original adapter invocation; no accepted packet modified. |

The eight kernel plus twelve emitted theorem audits contain only `propext`,
`Classical.choice` and `Quot.sound`. There are no owned axioms or placeholder
axioms in the successful results. Failed elaborations that printed `sorryAx`
were rejected and preserved. Each compilation directory includes the exact
compiled source copies, command, object hashes and full compiler output; binary
objects remain in scratch. The three certificates are for exact rational
moments at 1/4, 1/2 and 1, including the `(0,1]` endpoint case.

`full_replay` deliberately does not launch the original supervisor in place:
it writes replay logs into its own packet and preserves historical 6 GiB
compiler allowances. The current run uses a 4 GiB conservative physical stop.
A future full replay must first authenticate the compatible accepted
component/native closure, prepare an isolated packet and select a justified
resource policy. The unchanged original adapter is preserved at
`../2026-10-12-dot-accepted-connected-union1613-1737z/scripts/run_current.py`.
Its existence is not evidence that a replay occurred.

The first native Lake/bootstrap attempts failed to create a thread under the
3 GiB virtual-address limit. Setting `MIMALLOC_ARENA_RESERVE=16384` corrected
the allocator reservation while retaining the original physical/resource
ceilings. The cache utility then compiled, but the official Azure cache
requests were denied by the configured proxy (CONNECT 403). No network policy
or security settings were changed. The fallback is serial compilation from
the exact pinned sources. Failed attempts and each repair are retained under
`evidence/`. Later, one unchanged upstream module hit the 3 GiB virtual limit
at about826 MB resident memory. A sampled diagnostic and exact-source retry
established that 4 GiB **virtual** headroom sufficed; the physical stop stayed
4 GiB (`evidence/lean-virtual-limit-repair.json`). Missing product/tactic imports
were then repaired without altering theorem statements. The emitter's real
polynomial definition needed `noncomputable`; the full real-backend/native test
chain regenerated the three proofs before their successful Lean compilation.

## Remaining physical integration obligation

The supplied-certificate physical consumer remains the exact dot source in
`../2026-10-13-dot-g3-certified-consumer-0631z/`. Its required
`G4ProtectedCommonRepresentative` body, SHA256
`0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04`, is absent.
The materialized package deliberately does not import that uncompiled
consumer. Its other selected dependencies match accepted1613. Integrating the
full hand-reviewed consequence still requires authenticated physical-provider
source, compilation of the actual consumer, and the fixed external encoding
and physical admission bridge with one representative before all future rows.
No fresh arithmetic/support compilation can discharge those missing claims.

Trusted boundaries remain the Lean kernel and official toolchain, the pinned
external library objects according to their actual build receipts, host/OS
execution, repository/hash authentication, and the unproved native parser and
arithmetic refinement. Finite native tests are not universal correctness.
