# Research Commons: portable Lean and Rust

A portable research package built from the canonical claim registry in reuse and dependency order. Completed results are reused; unresolved questions retain their exact statements and obligations.

The pinned registry contains **118 claims**, with 75 reuse-rated and 43 unranked claims, at `447e188def18d91133260f14baf9bdc8ffd5b4df`. No rating or scientific completion field is invented. The Lean package combines the retained 1,613-module graph with 25 integration modules. Rust reuses the retained exact arithmetic, affine, source/calendar/word/readout and G7 formula engines.

## Build on a development host

Use Rust 1.90.0 and Lean 4.33.1. Compiler and dependency identities, including the Linux release checksum, are in [source-lock.json](source-lock.json).

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

The coherent package at [67ef70da](https://github.com/Sodelin/Research-Commons/commit/67ef70da6fe13bce5e43faf028f864b33c2d56e7) **passed**: 1,638 source modules, registry/aggregate, the complete 104,712-declaration owned audit, and all eleven Rust-generated proof documents. The audit found zero owned axioms, nonstandard rows or missing modules. All 67 Rust tests passed in the same [Linux CI run](https://github.com/Sodelin/Research-Commons/actions/runs/39981685853). See [the full receipt](integration/full-profile-verification.json).

The **per-claim integration gate remains incomplete** and intentionally exits 2 until every required binding has actual verification. A coherent build and accepted component callers do not establish every claim's application or the original full scientific endpoints.

The retained-object cache validates the exact compiler, source/dependency context and every object companion. Added modules and literal callers are always rebuilt. Receipts distinguish compilation from reuse, and the owned-axiom audit remains required. See [RETAINED-OBJECT-REUSE.md](integration/RETAINED-OBJECT-REUSE.md).

## Actual end-to-end paths

Each listed path has produced a complete proof document from actual Rust output and passed Lean checking.

| Caller | Input and checked conclusion | Receipt |
| --- | --- | --- |
| `cm-certificate` | Exact grouped positive laws; literal sparse-moment separation | [CM/affine](integration/certificate-verification.json) |
| `affine-certificate sat/unsat` | Supplied ordered rational matrix; real witness or full external-multiplier exclusion | [CM/affine](integration/certificate-verification.json) |
| `source-certificate tree/parallel/infeasible` | Captured original Code/admission/ordered fields; SAME returned positive physical bank, or exclusion of only the supplied cell | [Source/cell](integration/source-cell-verification.json) |
| `population-certificate edge/ancestral/path` | Actual native population row; total coefficient fibres including zero on absence, original validity/colocation and SAME returned bank | [Population](integration/population-caller-verification.json) |
| `epoch-certificate` | Four current copies in two original populations; all nine selected endpoint rows, raw witnesses, total coefficients and SAME shared bank | [Mixed epoch](integration/epoch-caller-verification.json) |
| `residual-certificate` | Complete supplied rational ensemble; strict top-k set and residual conservation | [RNA](integration/rna-results-verification.json) |

Run a binary through `cargo run --locked -p research-commons-runtime --bin NAME -- ARG`. Each emitter keeps its input in RAM and returns a complete proof document or refuses. Rendering alone is not acceptance. Resource failure and failed sufficient certificates remain UNKNOWN or INCONCLUSIVE.

The source caller also accepts a request through `source-certificate --stdin MySource`, bounded by the original 65,536-byte RC1 frame. Its entire emitted module must compile and pass the owned audit before acceptance. No universal parser/native refinement is asserted.

The mixed-epoch caller checks the actual selected genealogy/population/register fields and compares complete rational coefficient fibres against the existing constructive `fullRows` recurrence. It proves a conditional endpoint law at positive rates and nonnegative duration, including the returned original bank. It does not construct a legal global initialization/calendar prefix or a timed path law. External Copy/menu/readout transport remains a separate obligation.

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

Other commands select actual transitive dependencies from the same complete source graph:

```sh
cargo run --locked -p research-commons-package -- build --reuse-retained --target OriginalCodeChartReceiver
cargo run --locked -p research-commons-package -- check-source-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Population
cargo run --locked -p research-commons-package -- check-population-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Epoch
cargo run --locked -p research-commons-package -- check-epoch-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Menu.FiniteForcing
cargo run --locked -p research-commons-package -- audit-target ResearchCommons.Menu.FiniteForcing
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Claims.RNA
cargo run --locked -p research-commons-package -- check-residual-callers
```

The qualified-menu component checks finite-original-index algebra. Its actual original-source size/shape/joint-response instantiation and effective selection remain separate. All six RNA groups have checked conditional exports; their exact source hypotheses are retained. Target and caller receipts are under [integration/](integration/), with failures and corrections retained in [VERIFICATION.md](VERIFICATION.md).

## Claim integration and remaining work

[claims.json](integration/claims.json) maps canonical IDs to Lean declarations, Rust interfaces and verification. [retained-endpoints.json](integration/retained-endpoints.json) preserves owner-curated hypotheses. Typed G1/G2/G4/G5/G6/G7/Wong/RNA exports reuse existing mathematical results.

RNA aliases retain global-positive partition hypotheses, exact conditional random inputs, literal schema guards and BE origins. A schema tree is not executed trace admission. The residual caller owns the full ensemble, including repeated classes and zero weights; it does not assert complete RNA support, a sampler law or concentration.

Whole-word output, raw-root/completion/readout refinement, full physical source/target/action coverage, AST/history/QE/selector/result-origin joins, and other claim applications remain explicit. Open claims need checked statements; empirical records need evidence interfaces. Completed hand mathematics is not reopened by missing formal or native work.

The next G7 use-site is the immutable whole-word table to the already retained `wordRows`/controlled/natural/completed receivers. The accepted sparse coefficient/key-union checker and mixed-epoch caller are reused. See [SPARSE-EPOCH-PREFLIGHT.md](integration/SPARSE-EPOCH-PREFLIGHT.md). The explicit renderer API variant is recorded in source-lock.json; the canonical stochastic engines are unchanged.
