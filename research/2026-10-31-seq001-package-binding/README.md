# CB-SEQ-001 package binding

The parent-reviewed exact owner/type export join is adopted in the existing package. It reuses the original ThueMorseMAP proofs and definitions. This adds no mathematics or executable first-occurrence algorithm.

The actual package target build reused seven verified retained modules and compiled only the new wrapper. The Rust `check-exports --target ResearchCommons.Claims.SequenceFirstOccurrence --claim CB-SEQ-001` command then passed all six names/owners and the complete eight-module owned context. The full owned payload remains local; the public record gives its hash and summary.

Mappings rise from 48 to 49 and named requests from 520 to 526; 69 IDs remain unbound. Strict coverage still exits 2, with 116 claims incomplete for full package integration. The native runtime row remains pending. All 118 canonical scientific statuses are unchanged.

Plus uses n >= 2; even-minus n >= 1; odd-minus n >= 0. The original i(3)=45 exclusion is retained as a note, not a newly checked numeric theorem. Prior work and authorship remain in CARD-CORRESPONDENCE.json. The old 70-ID inventory is a dated pre-adoption snapshot; this packet is its additive successor for CB-SEQ-001 only.

The selected source catalogue now contains 1,834 modules. Only this eight-module target was checked after the addition; the earlier completed 1,833-module ContextB run remains an immutable historical receipt. The enlarged aggregate import is not claimed rebuilt.

Reproduce from packages/research after installing the pinned toolchains and locked dependencies:

```sh
cargo run --locked -p research-commons-package -- build --target ResearchCommons.Claims.SequenceFirstOccurrence
cargo run --locked -p research-commons-package -- check-exports --target ResearchCommons.Claims.SequenceFirstOccurrence --claim CB-SEQ-001
cargo run --locked -p research-commons-package -- coverage --strict
```

The last command is expected to fail truthfully until every actual package obligation is met. An exact retained cache may reduce the first command to one fresh wrapper compilation with `--reuse-retained`.
