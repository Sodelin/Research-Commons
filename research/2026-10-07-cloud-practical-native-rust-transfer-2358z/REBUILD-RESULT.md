# Actual Cloud rebuild of the preserved native count pilot

Contributor of original source/evidence: Dot. New executor/publisher:
Codex Cloud practical lane,8 October2026. Source packet attachment is
immutable `d3b0821f33a1144ff1c50478fdaa8289e890abcd`; the rebuild runner was
frozen locally at55f7903 before execution. Historical source/manifests/results
are unchanged; this receipt does not rewrite Dot's reported prior execution.

**Cloud executed PASS:** Rust1.90 compiler commit
`1159e78c4747b02ef996e55082b704c09b970588`, actual `cargo test --offline
--locked --all-targets -j1` and `cargo build --offline --locked --release -j1`
using a fresh target directory. All five cached crate archives independently
matched Cargo.lock checksums before the build. No installation, network fetch
or benchmark was performed. [RESULT.json](cloud-attempt1/RESULT.json) records
the precise toolchain, command vectors, dependency versions/checksums and
local product identity; raw build/test/replay logs are preserved separately.

Ten actual unit tests passed. The newly built release executable then matched
**all1693** authenticated saved corpus objects and complete stdout bytes,
with empty stderr/exit0. Twenty-two invalid CLI cases returned exit2 with
the required stderr/no stdout, and five further UTF-8/large-parser/huge-budget
boundaries passed. The corpus SHA256 remained
`5d70e84d9912694e959e44df44d18d1c7b4afa8caad62f462d19309016580783`.
This is fresh Cloud golden-corpus reproduction, not a new universal
equivalence proof or independent derivation of every expected value.

The Cloud executable SHA256 is
`8a0df53da5dc58f3cb07ad1bbf4b7ea8d55be6e6edb17ad897269c1626458688`.
It **differs** from Dot's reported binary
`5f8afd1557623ebf889b2d2e6fdbcf84a8c5a75e55993e32600fb54ecad700d1`.
No executable byte-reproducibility claim is issued or cause inferred.
All34 transferred payload hashes/lengths matched before and after execution.
No binary, toolchain or dependency cache is published here.

Each Cargo process had CPU30s, wall45s and2GiB address-space limits. Corpus
replay had CPU20s, wall30s and256MiB address space, with3s per CLI invocation.
The exact first attempt completed without failure or source correction.
The fresh target is local `/workspace/cloud-practical-runtime/native-count-cloud-attempt1`;
it is distinct from root's C-ABI FFI build and any interval pilot target.

Count-only scope remains: original exact rationals, first qualifying cutoff,
normalized-prefix weights and inspected-cutoff/resource semantics. Declared
Rust1.74 compatibility, other platforms, arbitrary exhaustion and package
licensing/distribution are unclosed gates. Full JC source/mean admission,
complete all-nine useful inverse cover and G6/Lean endpoints remain separate.
No shared provider/workflow/production setting or interval implementation
changed. Canonical new Cloud-receipt audit is requested; historical Dot review
continues to identify its own original source/test scope.
