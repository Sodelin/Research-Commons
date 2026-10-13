# Unified source solver and supplied COMMON certificates

This integration increment extends the existing exact original-source solver
and adds an exact rational supplied-certificate path. It does not replace G1,
G2, binary-M3 G5 or any selected older proof. General G3 remains open.

**Working checkpoint.** The source/backend tests, new Rust checker, recovered
native decoder/history checks and complete selected-source materialization
have passed. Fresh Lean verification, the final integration manifest and final
publication readback are still being assembled. Consult actual execution
receipts rather than treating this checkpoint as final acceptance.

The starting evidence is [the verified integration preflight](../2026-10-13-astra-integration-preflight-0630z/README.md).
Full1613 is publicly delivered with all68 current G2 sources. The subsequent
physical1614 provider was accepted and exactly recovered historically, but its
complete body remains unavailable here.1615 has historical acceptance without
its complete recovered packet. These statuses are not interchangeable.

`solve.py` provides four explicit tasks:

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

The final version of that run also checks native agreement and emits exact
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
`compiled=false` until an actual compiler receipt proves otherwise.

## Reproducible components

Source lives in `solve.py`, `certificates.py`, `rust/`, and `lean/`.
The Lean kernel formalizes the weighted-square, supported-bank and cubic
generation mathematics. Its intended claim is separate from a refinement proof
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
dependency closure is now being compiled serially from source, with resumable
per-module receipts; no broad parallel build was launched.

## Outstanding master obligations

The complete supplied-certificate-to-physical-representative consequence is
not certified by a numeric budget or a successful certificate check. It still
needs the exact physical provider
`0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04`,
the fixed external copy/readout and protected-coordinate wrapper, and a
source-faithful finite-code admission/parameter-feasibility bridge.

The received [dot consumer](../2026-10-13-dot-g3-certified-consumer-0631z/G3CertifiedCommonBoundedWitness.lean)
is retained unchanged and is still uncompiled at this checkpoint. Its
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
