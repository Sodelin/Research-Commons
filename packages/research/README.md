# Research Commons: portable Lean and Rust

A portable research package assembled from the canonical claim registry in reuse and dependency order. Existing mathematics and engines are reused; unresolved claims keep their exact statements and obligations.

The pinned registry has **118 claims:75 reuse-rated and43 unranked**, at `447e188def18d91133260f14baf9bdc8ffd5b4df`. The candidate source graph contains1,613 retained modules plus38 integration modules. Exact compiler, dependency and source identities are in [source-lock.json](source-lock.json).

## Build on a development host

Use Rust1.90.0 and Lean4.33.1.

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

The **full per-claim gate remains incomplete** and exits2 until every required binding has actual verification. The last accepted complete library is source[3b90ffa3](https://github.com/Sodelin/Research-Commons/commit/3b90ffa34188f631ff7a08bf43f92f883acf3ee0):1,649 source modules plus generated roots,104,850 declarations/94,569 theorems audited, zero owned axioms/nonstandard rows/missing modules. [Exact receipt](integration/coherent-library-verification-v2.json). This is library acceptance; its later whole-caller sequence interrupted.

The earlier source[67ef70da](https://github.com/Sodelin/Research-Commons/commit/67ef70da6fe13bce5e43faf028f864b33c2d56e7) passed all eleven then-selected Rust-generated proof documents and its1,638-source complete library/audit. [Receipt](integration/full-profile-verification.json). These source-specific results do not transfer automatically to changed code.

The current source[917d49ef](https://github.com/Sodelin/Research-Commons/commit/917d49ef38f2b9eb9a70927eb3d3f0e182381c4e) passed **85 Rust tests** and its899-source named-export context: **21 claim bindings/96 actual declaration names and owners**, with21059 declarations/14366 theorems audited.97 claims still lack named exports. [Exact export receipt](integration/claim-export-verification-v4.json). This includes the new positive atomic-law component; it does not establish complete applications for all21 claims.

Retained-object reuse checks the exact compiler, dependencies and every object companion. Added modules and literal callers are checked; the complete owned audit is mandatory. [Reuse contract](integration/RETAINED-OBJECT-REUSE.md).

## Actual end-to-end callers

Each path below produced a complete proof document from Rust output and passed Lean checking at its recorded source.

| Caller | Checked input and conclusion | Evidence |
| --- | --- | --- |
| `cm-certificate` | Grouped rational positive laws; literal sparse-moment separation | [CM/affine](integration/certificate-verification.json) |
| `moment-signature-certificate` | Complete seven-coordinate signature of one three-atom law; total mass identification against EVERY finite positive rival, then every further moment | [Signature](integration/moment-signature-verification.json), [exact input](examples/PositiveMomentSignature.lean) |
| `affine-certificate sat/unsat` | Ordered rational matrix; real witness or full external-multiplier exclusion | [CM/affine](integration/certificate-verification.json) |
| `source-certificate tree/parallel/infeasible` | Actual original Code/admission/ordered fields; SAME returned positive physical bank, or only supplied-cell exclusion | [Source/cell](integration/source-cell-verification.json) |
| `population-certificate edge/ancestral/path` | Actual native population row; total coefficients including zero on absence, original validity/colocation and SAME bank | [Population](integration/population-caller-verification.json) |
| `epoch-certificate` | Four copies/two original populations; all nine selected endpoint rows, raw witnesses, total coefficients and SAME bank | [Mixed epoch](integration/epoch-caller-verification.json) |
| `completion-certificate` | Conditional ancestral input; all12 ordered constant rows, true infinite ancestral limit, SAME rates and passive comb probability1/3 | [Completion](integration/completion-caller-verification.json) |
| `residual-certificate` | Complete rational ensemble; strict top-k set and residual conservation | [RNA](integration/rna-results-verification.json) |

Run a binary through `cargo run --locked -p research-commons-runtime --bin NAME -- ARG`. Emitters retain inputs in RAM and return a complete document or refuse. Rendering alone is not acceptance. Resource failure and insufficient certificates remain UNKNOWN or INCONCLUSIVE.

The signature component reuses the existing strict sparse separator and positive-grid interpolation. It identifies the atomic-law intermediary from2r+1 distinct sparse or consecutive moments without a rival-size bound. Reaction coefficients, stopped-law/shifted-Euler observables, derivative acquisition and universal native refinement are separate. The completed CB-RXN-001 hand proof is retained at its original scope. [Predecessor/successor comparison](integration/POSITIVE-MOMENT-REUSE-PREFLIGHT.md).

The source caller also accepts `source-certificate --stdin MySource` within the original65,536-byte RC1 frame. The mixed-epoch and completion callers retain their explicit valid conditional inputs; they do not construct a legal global initialization/calendar prefix or the external four-taxon tester.

## Independent targets

Targets select the actual transitive dependencies from the same source graph.

```sh
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Exports
cargo run --locked -p research-commons-package -- check-exports
cargo run --locked -p research-commons-package -- check-moment-callers --in-exports
cargo run --locked -p research-commons-package -- build --reuse-retained --target OriginalCodeChartReceiver
cargo run --locked -p research-commons-package -- check-source-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Population
cargo run --locked -p research-commons-package -- check-population-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Epoch
cargo run --locked -p research-commons-package -- check-epoch-callers
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Claims.RNA
cargo run --locked -p research-commons-package -- check-residual-callers
```

The isolated CM/affine target remains available through `prepare-certificates` and `build-certificates`, with its own namespace/object directory. Qualified-menu and RNA exports retain actual source/shape/joint-response, positivity, random-input and BE-origin premises. No wrapper turns those premises into implementation evidence.

## Remaining integration

[claims.json](integration/claims.json) records every canonical ID, reuse rank, actual Lean/Rust scope and evidence. [FRONTIER.md](integration/FRONTIER.md) identifies the next exact work; [VERIFICATION.md](VERIFICATION.md) retains failures and corrections.

The generic176-source `WordCache` receiver and5371/3175 owned audit passed at sourcef7f8a356. Its actual three-copy hybrid word checked the initial table and every supplied primitive, then **failed its final composition reduction and parent-order proof**. [Exact rejection](integration/word-cache-literal-rejection-v3.json). Neither whole word is accepted. The point retains the full original genealogy/population/register, both modes, one natural register draw and SAME bank; no smaller experiment or observed-forest quotient replaces it. [Reuse preflight](integration/WORD-CACHE-PREFLIGHT.md).

G3 fixed-source polynomial and supplied-bank/grid bindings reuse completed hand results; the original all-input RCF/enumerator and physical reduced-witness/protected-ID assembly remain separate. G4 observer exports preserve opaque roots/register/history and do not supply the full finite determining-test/tomography endpoint. NANUQ001 is not broadened to NANUQ002. RNA schema statements do not admit actual executed traces automatically.

The exact remaining joins include every unnamed claim's declarations, whole-word/raw-root/readout refinement, complete physical source/target/action coverage, AST/history/QE/selector/result origin and the original unresolved scientific endpoints. Missing formal/native joins do not reopen completed mathematics. Evidence-only commits record actual checked sources; they do not create fresh CI results.
