# Lean source selection and execution contract

Status at the first checkpoint: the complete accepted1613 source selection has
been materialized and independently read back. The new kernel is source only
until its actual compiler receipt is added. No missing physical provider has
been replaced by an axiom, a weaker theorem, or a presumed recovery.

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
| `full_replay` | Invoke the original guarded replay adapter. It still requires its compatible accepted object/native closure and blocks if absent. |

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

The first native Lake/bootstrap attempts failed to create a thread under the
3 GiB virtual-address limit. Setting `MIMALLOC_ARENA_RESERVE=16384` corrected
the allocator reservation while retaining the original physical/resource
ceilings. The cache utility then compiled, but the official Azure cache
requests were denied by the configured proxy (CONNECT 403). No network policy
or security settings were changed. The fallback is serial compilation from
the exact pinned sources. Failed attempts and each repair are retained under
`evidence/`.

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
