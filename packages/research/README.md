# Research Commons: portable Lean and Rust

A reproducible research package built from the canonical claim registry and the dated reuse ratings. Completed results are reused. Unresolved questions retain exact statements and obligations. Phone deployment is not a deliverable.

The package pins canonical118 at447e188, with75 ranked and43 unranked claims; no rating or scientific completion field is invented. Its Lean context contains the exact retained1613-module graph plus22 added modules. Rust reuses the retained exact arithmetic, affine, source/calendar/word/readout and G7 formula engines.

## Build on a development host

Use Rust1.90.0 and Lean4.33.1. Compiler/dependency identities and the Linux release checksum are in source-lock.json.

```sh
cd packages/research
cargo test --workspace --locked
cargo run --locked -p research-commons-package -- check
cargo run --locked -p research-commons-package -- prepare
cd lean
lake update
lake exe cache get
cd ..
cargo run --locked -p research-commons-package -- build --reuse-retained
cargo run --locked -p research-commons-package -- check-callers
cargo run --locked -p research-commons-package -- coverage --strict
```

The full coherent build is still running; no complete-library PASS is claimed. The strict per-claim gate intentionally exits2 until every required binding has actual verification. Registry accounting, successful source assembly and an accepted smaller target do not close that gate.

The retained-object cache validates the exact compiler, source/dependency context and every object companion. Added modules and literal callers are always rebuilt. Receipts distinguish compilation and reuse, and the owned-axiom audit remains required. See integration/RETAINED-OBJECT-REUSE.md.

## Actual end-to-end paths

| Caller | Input and checked conclusion | Actual evidence |
| --- | --- | --- |
| cm-certificate | Exact grouped positive laws; literal sparse-moment separation | certificate-verification.json |
| affine-certificate sat/unsat | Supplied ordered rational matrix; real witness or full external multiplier exclusion | certificate-verification.json |
| source-certificate tree/parallel/infeasible | Captured original Code/admission/ordered fields; SAME returned positive physical bank, or exclusion of only that supplied cell | source-cell-verification.json |
| population-certificate edge/ancestral/path | Actual ordered-copy native row; total coefficient fibres including zero on absence, original validity/colocation, SAME returned bank | population-caller-verification.json |
| residual-certificate | Complete supplied rational ensemble; strict top-k SET and residual conservation | rna-caller-verification.json |

Run a binary through `cargo run --locked -p research-commons-runtime --bin NAME -- ARG`. Each emitter holds its input in RAM and returns a complete proof document or refuses; rendering is not acceptance. A resource failure or failed sufficient certificate is UNKNOWN/INCONCLUSIVE, never an unrestricted negative theorem.

The source caller also accepts a user request through `source-certificate --stdin MySource`, bounded by the original65536-byte RC1 frame. Its entire emitted module must compile and pass the owned audit before acceptance. No universal parser/native refinement is asserted.

## Independent target verification

The isolated CM/affine context uses its own namespace/object directory:

```sh
cargo run --locked -p research-commons-package -- prepare-certificates
cd certificates
lake update
lake exe cache get
cd ..
cargo run --locked -p research-commons-package -- build-certificates
```

Other commands select actual transitive dependencies from the SAME complete source graph:

```sh
cargo run --locked -p research-commons-package -- build --reuse-retained --target OriginalCodeChartReceiver
cargo run --locked -p research-commons-package -- check-source-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Population
cargo run --locked -p research-commons-package -- check-population-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Menu.FiniteForcing
cargo run --locked -p research-commons-package -- audit-target ResearchCommons.Menu.FiniteForcing
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Claims.RNA
cargo run --locked -p research-commons-package -- check-residual-callers
```

At47ea5dcd/run39970715643,65 Rust tests passed. The complete population caller audit passed4137 declarations/2363 theorems with zero owned axioms/nonstandard rows/missing modules. The qualified-menu finite-original-index component passed its4-theorem audit; actual original-source size/shape/joint-response instantiation and effective selection remain separate. The20-module RNA schema/grid/certificate context passed1333 declarations/818 theorems; the repaired residual caller passed atcc97572e/run39971838230 with the complete1348-declaration/830-theorem audit. The later expanded exports of all six RNA groups require their own new context check.

## Claim integration and remaining work

integration/claims.json maps canonical IDs to exact Lean declarations, Rust interfaces and actual verification. integration/retained-endpoints.json retains the owner-curated source hypotheses. Typed G1/G2/G4/G5/G6/G7/Wong/RNA exports do not claim new mathematical discoveries.

The RNA aliases preserve global-positive partition hypotheses, exact conditional random inputs, literal schema guards and BE origins. A schema tree is not an executed/generated trace admission. The residual caller owns the full ensemble, including repeated class rows and zero weights; it does not assert complete RNA support, a sampler law or concentration.

Whole-epoch/word and raw-root/completion/readout refinement, full physical source/target/action coverage, AST/history/QE/selector/result-origin joins and other claim applications remain explicit. Open claims need appropriate checked statements; empirical records need evidence interfaces. Completed hand mathematics is not reopened by missing formal or native work.

Exact accepted component receipts are under integration/. Failed attempts and their corrections remain in VERIFICATION.md and Git history. A complete end-to-end package requires the full build and the complete per-claim gate as well as these scoped successes.
