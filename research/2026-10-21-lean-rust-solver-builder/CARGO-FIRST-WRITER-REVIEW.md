# Pinned Cargo has internal diagnostic writers

This is SOURCE evidence, not a new executed plaintext record. The official
Rust1.90.0 source selects Cargo commit 840b83a10fb0e039a83f4d70ad032892c287570a as
src/tools/cargo. Exact primary URLs/Git blobs/SHA256/line scopes are retained
in evidence/CARGO-FIRST-WRITERS.json. The installed compiler/Cargo binaries
and the new job have not been authenticated or run by this review.

Cargo's compiler-message handler lazily writes original diagnostic lines to
its own per-unit fingerprint output- file. That file is inside Cargo, separate
from the parent guard's stdout/stderr. Diagnostic-display suppression can still
return a cacheable line; quiet/display flags therefore do not establish writer
coverage. Source: [compiler message handling](https://github.com/rust-lang/cargo/blob/840b83a10fb0e039a83f4d70ad032892c287570a/src/cargo/core/compiler/mod.rs#L1839),
[message cache path](https://github.com/rust-lang/cargo/blob/840b83a10fb0e039a83f4d70ad032892c287570a/src/cargo/core/compiler/build_runner/compilation_files.rs#L294).

A successful selected custom build also stores captured script stdout/stderr
and root-output in its own run directory. Separately, the enabled dirty rustc
query cache serializes stdout/stderr/status into .rustc_info.json on drop.
These are conditional paths, not claims about a newly observed execution or
a complete dependency-script inventory.
[Build-script writes](https://github.com/rust-lang/cargo/blob/840b83a10fb0e039a83f4d70ad032892c287570a/src/cargo/core/compiler/custom_build.rs#L641),
[compiler-query cache](https://github.com/rust-lang/cargo/blob/840b83a10fb0e039a83f4d70ad032892c287570a/src/cargo/util/rustc.rs#L255).

The pinned documented CARGO_CACHE_RUSTC_INFO=0 control selects no compiler-info
cache location. The NEW source-only native build proposal should select it
before Cargo. It removes that one selected cache writer; it does not encrypt
or disable diagnostic caches, build-script outputs, runtime/guard records or
Lean/Lake writers. The actual original returns still require encrypted custody.
[Source control](https://github.com/rust-lang/cargo/blob/840b83a10fb0e039a83f4d70ad032892c287570a/src/cargo/util/context/mod.rs#L278),
[pinned documentation](https://github.com/rust-lang/cargo/blob/840b83a10fb0e039a83f4d70ad032892c287570a/src/doc/src/reference/environment-variables.md#L71).

Fingerprint metadata is also identified for the real source/build-vs-runtime
classification. No blanket claim that every .rlib/object is a raw harness
record follows. This selected source map is not transitive writer enforcement.
No existing runner, workflow, canonical profile or whitelist changed. The quiet
outer refusal remains before any new Cargo/compiler/Lake/native child, until
the actual owner's recipient/context/controller and first-writer hooks bind.
