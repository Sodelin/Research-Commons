# Unified source solver and supplied COMMON certificates

The [native acquisition successor](../2026-10-13-astra-native-acquisition-0815z/README.md)
adds Rust certificate generation with explicit `--native-generation` agreement,
158 acquisition controls and a fresh 19-case unified run. Earlier receipts below
retain their original source versions; the successor supplies current pins.

This integration increment extends the existing exact original-source solver
and adds an exact rational supplied-certificate path. It does not replace G1,
G2, binary-M3 G5 or any selected older proof. General G3 remains open.

**Verified integration increment; full physical consequence remains blocked.**
The unified solver passes 19 end-to-end cases. The new Lean kernel, its `AstraKernel` entry point
and three exact emitted certificate proofs compile through the actual Lake
targets with only standard axioms and no placeholders or added axioms. Original
accepted1613 is fully selected and authenticated; its components were not all
rebuilt from scratch. The missing physical1614 provider is still required for
the complete hand-reviewed bounded-representative consequence.

| Evidence | Verified result |
| --- | --- |
| `evidence/unified-emitter-real-repair-tests` and matching `*-cases` | 19 real-backend/native integration cases; final executed source pins. |
| `evidence/lake-generated-certificates-real-repair` | Final kernel, `AstraKernel` and three unmodified emitted proof sources compiled; actual axiom audit. |
| `evidence/END-TO-END-CORRESPONDENCE.json` | Exact emitted-source hashes equal the compiled-source hashes; no hand-patched proof samples. |
| `evidence/rust-differential` | 556 expected exact native accept/refuse outcomes. |
| `RECOVERED-PARITY.md` | Fresh recovered decoder, serial-history and population controls with complete provenance. |
| `LEAN-INTEGRATION.md` | Selected import graph, actual Lake targets, dependency execution and source readback. |

`PACKET-MANIFEST.json` and `verify_packet.py` provide complete artifact integrity
checking. Integrity and finite execution evidence do not establish universal
native correctness or the missing physical theorem.

The combined `AstraUnified` source aggregate is materialized and authenticated,
but has not been freshly compiled here. Original1613's successful historical
aggregate execution remains separately authenticated evidence.

The starting evidence is [the verified integration preflight](../2026-10-13-astra-integration-preflight-0630z/README.md).
The [integration handoff](INTEGRATION-HANDOFF.md) identifies the exact selected
baseline, missing physical provider and remaining composition obligations.
Full1613 is publicly delivered with all68 current G2 sources. The subsequent
physical1614 provider was accepted and exactly recovered historically, but its
complete body remains unavailable here.1615 has historical acceptance without
its complete recovered packet. These statuses are not interchangeable.

`intake/` indexes the whole tracked Commons snapshot and exact selected Lean
versions, with additive G4/G3 successor reviews. New G4 hand-reviewed findings
retain their stated conditions and unresolved obligations; this packet does not
mislabel their indexing as completed Lean formalization. The exposure correction
and later mixed-source/paired-gap boundaries are recorded explicitly.

`solve.py` provides five explicit tasks:

* `source_search` calls the pinned existing `certified_bounds.py`, its original
  architecture census, shared-parameter solver and semantic certificate checker.
  It can certify an actual source witness or exclusion within a declared
  complete finite registry. Exhaustion of an incomplete registry is UNKNOWN.
* `check_certificate` verifies rational coefficients at exponents
  `k*(k-1)/2`, k=1,...,L, a nonzero polynomial, an exact weighted-square
  nonnegativity identity on [0,1], and exact annihilation of normalized moments.
* `generate_singleton` derives the cubic `(x-a)^2*(x+2a)` solely from supplied
  moments `(1,a,a^3)`, and rechecks the generated certificate. Other data returns
  UNKNOWN; no unprovided moment or latent target is requested.
* `common_menu` fixes external taxon/protected IDs and the complete joint
  configuration PMF, checks every ordered pair's certificate, and computes the
  conditional support/hybrid budget. Its source-existence answer remains UNKNOWN.
* `native_rc1` delegates literal RC1 requests to the recovered exact Rust
  affine solver or complete formal joint forward-law compiler. Successful
  outputs are checked against the same request. Matrix decisions and formal
  tables do not establish physical source admission. See [the native bridge](NATIVE-BRIDGE.md).

The new rational certificate language supports sums of nonnegative rational
weighted squares multiplied by 1, x, 1-x, or x(1-x). It is a supported exact
subset, not a complete decision procedure for real-coefficient certificates.
Survival1 remains allowed; survival0 is excluded by the physical theorem's
premises. Zero-weight configurations are removed without renormalization.

The first source-solver integration run exercised the real inherited producer
and checker. All13 cases passed, including two positive sources, two scoped
exclusions, bounded exhaustion, unsupported conditional count, exact generation,
correlated joint configurations and malformed/unencoded input controls.
These tests do not prove universal native-code correctness.

The final 19-case unified run also checks native agreement and emits exact
Lean certificate proofs and fixed padded-comb observation descriptions. The
native differential corpus passed556 cases. The recovered public Rust core
matches all25 historical decoder parent-file pins; fresh decoder3/3,
serial-history1/1 and population6/6 controls passed. See
[the native recovery](RECOVERED-PARITY.md) and [correspondence](RUST-CORRESPONDENCE.md).

For a checked certificate generated from supplied moments, run:

```sh
python3 -B research/2026-10-13-astra-unified-solver-0645z/solve.py \
  --request research/2026-10-13-astra-unified-solver-0645z/examples/singleton-generator.json \
  --output /tmp/common-certificate-new-run
```

For the existing exact source engine, use `examples/finite-witness.json` and
`--backend-python /path/to/python` with the inherited pinned SymPy1.14.0,
NetworkX3.5 and Z3-solver4.15.3.0. The output directory must be absent.
`--rust-binary /path/to/common-certificate-checker` additionally checks exact
native agreement on certificate tasks. Generated Lean files carry
`compiled=false` at generation time. The separate compiler receipt and exact
hash correspondence above certify the three final test outputs; future outputs
require their own compiler execution.

For the recovered native engine, select an `examples/native-*.json` request and
provide `--parity-binary /path/to/parity-solver` and
`--parity-sources /path/to/authenticated-restored-tree`. The bridge verifies the
selected source inventory, actual build receipts and observed executable hash.
The native affine examples cover a joint witness, a scoped contradiction and
budget UNKNOWN; the law examples retain parallel edge occurrences and COMMON
versus INDEPENDENT mechanism distinctions. `operation: "check"` independently
submits a supplied result to the existing request-bound native checker.

## Reproducible components

Source lives in `solve.py`, `certificates.py`, `rust/`, and `lean/`.
The Lean kernel formalizes the weighted-square, supported-bank and cubic
generation mathematics. Its compiled claim is separate from a refinement proof
of the Python/Rust implementations and from the missing physical reduction.
The Rust component reuses the established exact-count rational parser and
arbitrary-precision libraries after enforcing a narrower wire grammar.

Toolchains are installed only in fresh cloud scratch. `guard.py` preserves
commands, resource observations, outputs and failures. Defaults: serial jobs,
3-GiB address-space cap per process,4-GiB cgroup stop,1-GiB available-RAM floor,
8-GiB disk floor and explicit CPU/wall limits. Existing source-backend children
add their own tighter limits. No desktop build or system-setting change occurs.

The first Lean extraction stopped at the cgroup guard because dirty file cache
accumulated. The preserved archive matched the official checksum. Extraction
was repaired by flushing and releasing only completed files in owned scratch;
the same guard then passed. The official compiler binary matches the historical
accepted Lean4.33.1 identity. The Mathlib utility's initial thread-creation
failure was repaired by reducing allocator virtual-address reservation under
the same physical limits. Its utility modules compiled, but the official
cache endpoint is unavailable through this executor's proxy. The exact pinned
dependency closure was compiled serially from source, with resumable per-module
receipts; no broad parallel build was launched.

A later dependency reached the 3-GiB virtual-address ceiling with roughly
0.83 GiB resident memory and failed with `std::bad_alloc`. A sampled replay
confirmed that limit. The same source/compiler then passed with 4 GiB of
virtual-address space, using about 0.84 GiB resident memory. Subsequent narrow
compilations retain that virtual allowance and the original 4-GiB physical
cgroup stop, disk floor and time limits. Failed receipts and the measured repair
are preserved; this does not attribute any cause to the desktop incident.

Actual proof compilation also exposed missing explicit library imports and
the emitter's missing `noncomputable` annotation for real division. Their failed
runs were rejected and preserved. The imports were corrected without changing
the theorem statements; the emitter was repaired and all 19 cases rerun before
the three regenerated files were compiled. The final axiom audit is clean.

## Outstanding master obligations

The complete supplied-certificate-to-physical-representative consequence is
not certified by a numeric budget or a successful certificate check. It still
needs the exact physical provider
`0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04`,
the fixed external copy/readout and protected-coordinate wrapper, and a
source-faithful finite-code admission/parameter-feasibility bridge.

The received [dot consumer](../2026-10-13-dot-g3-certified-consumer-0631z/G3CertifiedCommonBoundedWitness.lean)
is retained unchanged and is still uncompiled in this delivered increment. Its
mathematical existential representative must precede all future permitted rows.
No axiom or conclusion-shaped provider is inserted to make it compile.
The new executable menu refuses protected parameter constraints that it cannot
encode, and never applies the conditional hybrid budget as a search-completeness
bound. Missing/unsupported mathematics retains UNKNOWN.

The remaining trusted boundary includes official compiler/dependency artifacts,
Lean's kernel and standard axioms, Python/Rust arithmetic libraries and runtimes,
the parser/checker implementations, and the inherited SymPy/Z3 source engine.
The mathematical kernel and finite differential corpus do not constitute a
formal native-code refinement or an effective original-class outer-admission
oracle. Approximate numerical diagnostics retain their original separate scope.
