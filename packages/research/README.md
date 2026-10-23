# Research Commons: portable Lean and Rust

This is the user-requested end-to-end research package, not a phone application. Its canonical input is the pinned 116-claim registry. The subjective reuse overlay orders 75 claims; the remaining 41 are included without invented rankings.

## Actual code

- Rust workspace: a package assembler/integration checker and a facade over the existing exact arithmetic, supplied-cell and G7 formula/word/readout engines. The retained sources and their complete local dependencies are included as exact immutable trees.
- Lean: pinned Lean4.33.1/mathlib0df444, the complete retained 1,613-module source graph, deterministic module preparation, the coherent aggregate entrypoint, and the registry IDs. No historical native objects are imported.
- Concrete reuse: typed G1/G2/G5/G6/G7 endpoint exports, the existing CM-T02 separation proof, the retained grouped-rational-law receiver and a Rust emitter producing a complete Lean moment certificate. New-context checking remains separate from historical acceptance.
- Per-claim bindings: `integration/claims.json` tracks actual declarations, source modules, Rust interfaces and verification separately. A missing binding remains missing; a hand proof is not demoted to open mathematics.

## Reproducible commands on a normal development host

```sh
cd packages/research
cargo test --workspace --locked
cargo run --locked -p research-commons-package -- check
cargo run --locked -p research-commons-package -- coverage --strict
cargo run --locked -p research-commons-package -- prepare
cd lean
lake update
lake exe cache get
cd ..
cargo run --locked -p research-commons-package -- build
cargo run --locked -p research-commons-package -- check-callers
```

The strict coverage command intentionally exits2 until every required integration has its named verified bindings. The regular check verifies accounting and emits the actual incomplete frontier. A successful registry count does not certify scientific results. The source assembler verifies graph/body hashes and dependency order before it writes generated Lean files. A capped build is explicitly partial and cannot emit complete-profile acceptance.

The source-only state of the retained G7 Rust proposal is preserved in its original comments. Fresh package compiler/test results must be recorded separately. G7 queries do not run a QE provider, authenticate transcripts or manufacture physical source coverage. The affine engine's finite matrix decision is not unrestricted G3 source NO.

This initial package does not yet claim all116 mathematical statements formalized. The strict gate prevents that false conclusion. Original unresolved questions and empirical-only records require their appropriate statement/data interfaces; they are not fabricated theorems. See GOAL.md and source-lock.json for scope/provenance.

The package now pins canonical registry d71ea2f (116 cards, board1.17). The 23 additions remain unranked alongside 18 earlier unranked entries. No subjective rating or canonical proof status is invented.

Generate the actual exact-arithmetic caller example with `cargo run --locked -p research-commons-runtime --bin cm-certificate`. The Linux workflow elaborates that emitted source after building the theorem modules. This tests a literal caller; it does not prove every native grouping implementation or physical-source adapter correct.

The second certificate caller reuses the retained strict affine solver and both existing Lean checkers. `cargo run --locked -p research-commons-runtime --bin affine-certificate -- sat` emits the weak-boundary rational witness; `-- unsat` emits the complete nonnegative original-row multiplier certificate for the strict boundary. Duplicate row positions stay distinct. The emitted proofs establish real feasibility/infeasibility of that supplied matrix, not original graph admission or a universal native refinement. A rendering/resource refusal produces no negative theorem.

For rapid independent certificate verification, `cargo run --locked -p research-commons-package -- prepare-certificates`, then run `lake update` and `lake exe cache get` inside `certificates`, followed by `cargo run --locked -p research-commons-package -- build-certificates` from the package root. This separate source/object context uses the unchanged abstract CM component and retained affine checkers. It compiles the emitted proofs and audits all selected core/caller declarations. It does not certify the full1613-module physical profile or all116 claim bindings; those retain their separate build/gate.

Actual end-to-end caller verification passed at source7898af0a/run39947518267: all three Rust-generated proof documents compiled in Lean4.33.1, and the selected core/export/caller owned-axiom audit passed. Rust had44 passing tests. See integration/certificate-verification.json for exact source hashes and limits. The full-library build and whole116-claim integration remain separate and incomplete.

The integration gate follows each canonical claim kind. Open questions need checked formal statements/obligation bindings; empirical/software records need checked evidence interfaces. Neither is converted into a fabricated proved theorem. Labels without actual module/declaration and verification records cannot close a row.

The original-source emitter reuses the public immutable cell snapshot API and the six existing Code/layout/field/physical receiver modules. `source-certificate tree|parallel|infeasible` parses a public four-taxon CHART, retains every captured field and ordered parent occurrence, and emits the literal Code plus its admission/field/certificate proof obligations. The positive case constructs the actual shared physical bank from the same returned vector; the negative case excludes only that supplied source cell. Full-profile `check-callers` kernel-checks all three documents and audits their declarations. Rendering is not acceptance; these new full-context outputs remain unverified until that check succeeds. See integration/SOURCE-CERTIFICATE-PREFLIGHT.md.

Compile the original source receiver without waiting for unrelated modules using `cargo run --locked -p research-commons-package -- build --target OriginalCodeChartReceiver`, then `cargo run --locked -p research-commons-package -- check-source-callers`. This selects the actual transitive dependencies from the same complete source graph and same pinned context; it creates no replacement source model or isolated admission factory. Its scoped receipt includes all compiled object hashes and cannot report full-profile completion. The whole-library build and per-claim gate remain required.

For subsequent hosted builds, `build --reuse-retained` reuses only original immutable graph objects with matching compiler/dependency/source/object identities. Added modules and all literal callers are rebuilt. Receipts distinguish compilation from cache reuse; the full axiom audit still runs. See integration/RETAINED-OBJECT-REUSE.md. The first already-running cold build is unchanged.

To use your own original request, pipe an RC1 CHART into `cargo run --locked -p research-commons-runtime --bin source-certificate -- --stdin MySource`. The CLI reads at most the original65536-byte request frame, retains it in memory, and writes the complete proof document to stdout only after successful capture/solve/render. The document includes literal BinaryValid, RegistryValid and CutChild obligations; actual acceptance requires compiling that whole document against OriginalCodeChartReceiver and auditing its declarations. A source render or native decision is never a Lean PASS. No new on-phone application is created.
