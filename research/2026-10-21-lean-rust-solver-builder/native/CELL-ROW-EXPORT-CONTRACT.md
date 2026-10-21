# Typed access to the existing native CHART row compiler

SOURCE ONLY; the adapter and five staged tests have not compiled or run.
native/cell_row_export.rs calls the existing protocol::parse and
natural_cell::compile. It preserves CHART32coordinates/128rows, the exact
captured request, original registry/port order and every emitted matrix row.
It invokes no solver and exposes no CLI, serializer, file/log/network writer,
canonical task, source-admission flag or new word grammar.

compile_request returns a CompiledCellRows whose fields are private.
Read-only accessors expose the captured original request, chart, rows,
dimension, bank names and projection cap. Coordinate helpers delegate to the
original native source index functions. There is one ancestral inverse-rate
slot shared by all exposures. RATE labels hold u, with actual rho=1/u only
after positivity; native COIN indices alone do not authenticate parent1 meaning.
Errors refuse/unavailable export, never assert mathematical NO.

The original parser already validates CHART through its row compiler. Its
public Request::Chart stores the chart, so obtaining Compiled uses the same
public call as original execute. No alternative compiler implementation is
introduced. The existing CHART result wire already includes BANK/MATRIX;
this adapter adds typed ownership/coordinate access without a competing wire.

## Reuse and build input

The frozen parity source is at4e556c4ae6225d18fabf30bc7d3347a468749ebc,
not at its path in baseline1138a5. Four exact baseline Contents reads
returned404. Do not introduce a Cargo path that is absent from this branch.

Reuse the EXISTING51-file/488056B restored source contract, inventory SHA256
c5c84b5fa1755ae05830059353c184a77c52bd236b4053fe2668e6e30f066da6,
and lockd1ca669fa3fbfb62810cd5653682e65c0548b31e5c957b81c2c3a4b2d524d4fb.
restore_parity.py and run_recovered_controls.py were read and source-pinned,
not invoked. Their raw writers remain held. Recover source through the existing
authorized ONLINE provider; no phone checkout, Git fetch, replacement crate,
new identity or historical object is supplied by this proposal.

The disjoint native/source-inputs tree NOW contains all51 exact public inputs,
488056B, independently read/hash-checked against the unchanged frozen inventory.
Fifty existing Git blobs are reused; the one old serial-control path relocation
is reproduced exactly. Original Cargo paths/locks and all relative dependencies
are preserved. No old restore runner, Git process, compiler or test was invoked.
The eventual core manifest is
native/source-inputs/research/2026-10-10-codex-lean-rust-parity/rust/Cargo.toml.
This resolves source availability, not the writer, toolchain or object boundary.

After actual writer/controller admission, the original locked offline core
build supplies a FRESH parity_solver rlib and its FRESH dependency directory.
The adapter can then be compiled as a library with Rust1.90.0, edition2021,
crate-name common_cell_row_export, --extern parity_solver=that exact rlib and
-L dependency=that same fresh directory. Compile its --test target likewise
and run serial --test-threads=1. These are build-input obligations, not commands
executed here or proof that an installed rlib matches the source.

The source proposal retains the existing serial guard/resource design:
core build2GiB/180wall/120CPU; adapter/test compile512MiB/60wall/45CPU and
serial tests512MiB/30wall/20CPU, subject to the original actual admission,
cgroup/pressure/cleanup controls. No old held/consumed job is replayed.
Actual source/toolchain/library/dependency/object hashes and COMPLETE outcomes
must be retained through the real encrypted writer before first persistence.

## Meaningful staged verification

Five UNEXECUTED controls reuse the exact ORDINARY/PARALLEL constants and
literal expected exposure coefficients from original tests/chart.rs:
inverse slot/row semantics; parallel edges and12-dimensional preservation;
cap0 matrix export; ownership after input mutation; unsupported/noncanonical
request refusal. This is new adapter verification, not a claim that historical
controls tested these new bytes. No additional small Lean suite is requested.

The result is a native finite mathematical cell matrix. Original typed
RootedBinary construction, effective complete registries, one bijective
layout, port/routing meaning and exact emitted.toFinset=compileCell remain
mandatory separate Lean premises. Rust/compiler/parser refinement, authentic
runtime origin, canonical CHART adoption, nonlinear source/readouts and full
G6/G7/original master closure remain open.
