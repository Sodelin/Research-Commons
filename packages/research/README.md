# Research Commons: portable Lean and Rust

A portable research package built from the canonical claim registry in reuse and dependency order. Completed results are reused; unresolved questions retain their exact statements and obligations.

The pinned registry contains **118 claims**, with 75 reuse-rated and 43 unranked claims, at `447e188def18d91133260f14baf9bdc8ffd5b4df`. No rating or scientific completion field is invented. The current checked Lean library combines the retained1,613-module graph with36 integration modules. Rust reuses the retained exact arithmetic, affine, source/calendar/word/readout and G7 formula engines.

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
cargo run --locked -p research-commons-package -- check-exports
cargo run --locked -p research-commons-package -- check-callers
cargo run --locked -p research-commons-package -- coverage --strict
```

The checked coherent library at [3b90ffa3](https://github.com/Sodelin/Research-Commons/commit/3b90ffa34188f631ff7a08bf43f92f883acf3ee0) **passed**:1,649 source modules plus registry/aggregate, and the complete104,850-declaration/94,569-theorem owned audit. It found zero owned axioms, nonstandard rows or missing modules. All81 Rust tests passed in the same [Linux run](https://github.com/Sodelin/Research-Commons/actions/runs/40011993974). [Exact library receipt](integration/coherent-library-verification-v2.json). The larger14-caller sequence remains incomplete after hosted shutdown during the unchanged hybrid word; library acceptance and actual caller acceptance are separate.

The earlier [67ef70da](https://github.com/Sodelin/Research-Commons/commit/67ef70da6fe13bce5e43faf028f864b33c2d56e7) baseline passed all eleven Rust-generated proof documents and its complete1,638-source library/audit. [Earlier full receipt](integration/full-profile-verification.json). These are source-specific results.

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
| `completion-certificate` | Complete conditional ancestral input; all12 ordered constant rows, SAME returned rates and passive comb probability1/3 | [Completion/observer](integration/completion-caller-verification.json) |
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

[claims.json](integration/claims.json) maps every canonical ID to its exact Lean/Rust scope and evidence. The current [export receipt](integration/claim-export-verification-v3.json) **passed** at3b70210d/[run40003057044](https://github.com/Sodelin/Research-Commons/actions/runs/40003057044):91 named declarations and real imported-module owners in20 claim bindings,897 source modules and a clean21050-declaration/14358-theorem audit. All75 Rust tests passed.98 claims still lack named exports; other component/native obligations remain explicit.

G3's new fixed-source polynomial and supplied-certificate bank/grid bindings reuse completed hand results. They do not supply the full RCF/enumerator or physical reduced-witness/count/protected-ID assembly. G4's observer exports retain original opaque-root/register/history hypotheses; they do not prove the full finite determining-test/tomography theorem. [Retained endpoints](integration/retained-endpoints.json) and each preflight preserve the original hypotheses.

The actual `completion-certificate` caller **passed**:12 complete ordered native constant rows at a nonempty original ancestral-root input, total coefficient fibres, the genuine infinite ancestral limit, SAME returned rates and passive unranked comb probability1/3. [Exact receipt](integration/completion-caller-verification.json). It does not construct a legal global prefix or the four-taxon tester wrapper.

The indexed `ResearchCommons.Integration.Word` receiver and its174-source owned audit passed5213 declarations/3104 theorems. It checks complete finite-position coefficient fibres and uses a proved original-variable/native-bank LeftInverse with the SAME physical bank. [Generic receipt](integration/word-core-verification-v2.json). The larger257517-byte NaturalIndependentWord caller at3b70210d ended in hosted shutdown without a coefficient result. Its literal outcome remains UNKNOWN; COMMON and full coherent14-caller closure are not inferred. See [the word preflight](integration/WORD-CERTIFICATE-PREFLIGHT.md).

NANUQ retains its twelve source/drawing/distinct-set/mean typed exports, without extending CB-NANUQ-001 to the broader all-level CB-NANUQ-002. RNA exports retain positivity, exact conditional random inputs, literal schema guards and BE origins; schema trees are not executed-trace admission.

The Rust `check-exports` interface rejects missing dependencies, revalidates source/object digests, runs the complete selected owned audit and checks every actual type/owner. It retains canonical completion and original integration scope. The older17/73 and18/80 receipts remain available; they are not current pending work.

Whole-word/raw-root/completion/readout refinements, full physical source/target/action coverage, exact AST/history/QE/selector/result origin and the other claim applications remain. Open claims require checked statements; empirical/software records require evidence interfaces. Missing formal/native work does not reopen completed hand mathematics. The strict full-package gate remains incomplete.

Accepted records always name their actual checked source; a documentation-only publication does not create a fresh CI result. Earlier sources and rejected/UNKNOWN caller history remain retained.

The current `word-cache-certificate independent/common` path emits bounded source modules for the SAME larger hybrid word. `check-word-callers` checks the entire bundle through `ResearchCommons.Integration.WordCache`. Source3b90ffa3's generic175-source cache context and5308/3142 owned audit passed; its actual caller still interrupted at the first interval primitive. [Generic cache receipt](integration/word-cache-core-verification.json).

The active9f3f3466 candidate reuses the existing `fullRows` law for a checked complete active population list, with the existing single-epoch polynomial uniqueness theorem. Every cache input proves `ActiveIn`; all original coordinates, full selected keys/registers, operations, initial/final checks and fallback remain. Its generic target now compiles and the actual bundle is under verification. BOTH entire same3-copy words and the final owned audit remain required. Original direct emission stays available. No literal acceptance follows from the generic or completion receipts. [Exact reuse/scope](integration/WORD-CACHE-PREFLIGHT.md).
