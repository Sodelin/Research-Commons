# Research Commons: portable Lean and Rust

This is the user-requested end-to-end research package, not a phone application. Its canonical input is the pinned 93-claim registry. The subjective reuse overlay orders 75 claims; the remaining 18 are included without invented rankings.

## Actual code

- Rust workspace: a package assembler/integration checker and a facade over the existing exact arithmetic, supplied-cell and G7 formula/word/readout engines. The retained sources and their complete local dependencies are included as exact immutable trees.
- Lean: pinned Lean4.33.1/mathlib0df444, the complete retained 1,613-module source graph, deterministic module preparation, the coherent aggregate entrypoint, and the registry IDs. No historical native objects are imported.
- Per-claim bindings: `integration/claims.json` tracks actual declarations, source modules, Rust interfaces and verification separately. A missing binding remains missing; a hand proof is not demoted to open mathematics.

## Reproducible commands on a normal development host

```sh
cd packages/research
cargo test --workspace
cargo run -p research-commons-package -- check
cargo run -p research-commons-package -- coverage --strict
cargo run -p research-commons-package -- prepare
cd lean
lake update
lake exe cache get
cd ..
cargo run -p research-commons-package -- build
```

The strict coverage command intentionally exits2 until every required integration has its named verified bindings. The regular check verifies accounting and emits the actual incomplete frontier. A successful registry count does not certify scientific results. The source assembler verifies graph/body hashes and dependency order before it writes generated Lean files. A capped build is explicitly partial and cannot emit complete-profile acceptance.

The source-only state of the retained G7 Rust proposal is preserved in its original comments. Fresh package compiler/test results must be recorded separately. G7 queries do not run a QE provider, authenticate transcripts or manufacture physical source coverage. The affine engine's finite matrix decision is not unrestricted G3 source NO.

This initial package does not yet claim all93 mathematical statements formalized. The strict gate prevents that false conclusion. Original unresolved questions and empirical-only records require their appropriate statement/data interfaces; they are not fabricated theorems. See GOAL.md and source-lock.json for scope/provenance.
