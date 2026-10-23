# Research Commons: portable Lean and Rust

A portable research package assembled from the canonical claim registry in reuse and dependency order. Existing mathematics and engines are reused; unresolved claims keep their exact statements and obligations.

The pinned registry has **118 claims:75 reuse-rated and43 unranked**, at `447e188def18d91133260f14baf9bdc8ffd5b4df`. The candidate source graph contains1,613 retained modules plus39 integration modules. Exact compiler, dependency and source identities are in [source-lock.json](source-lock.json).

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

The **full per-claim gate remains incomplete** and exits2 until every required binding has actual verification. The last accepted complete library is source[f7f8a356](https://github.com/Sodelin/Research-Commons/commit/f7f8a356c0c6d1a937e583e4b3ccedfa2960f880):1,649 source modules plus generated roots,104,893 declarations/94,588 theorems audited, zero owned axioms/nonstandard rows/missing modules. [Exact receipt](integration/coherent-library-verification-v3.json). This is library acceptance; its later whole-caller sequence rejected the final word proof.

The earlier source[67ef70da](https://github.com/Sodelin/Research-Commons/commit/67ef70da6fe13bce5e43faf028f864b33c2d56e7) passed all eleven then-selected Rust-generated proof documents and its1,638-source complete library/audit. [Receipt](integration/full-profile-verification.json). These source-specific results do not transfer automatically to changed code.

The current source[e7ed8159](https://github.com/Sodelin/Research-Commons/commit/e7ed8159f1ed59d0ab4c6d88593e56b72308084b) passed **85 Rust tests** and its919-source named-export context: **21 claim bindings/96 actual declaration names and owners**, with22008 declarations/14748 theorems audited.97 claims still lack named exports. [Exact export receipt](integration/claim-export-verification-v5.json). This includes the new positive atomic-law component; it does not establish complete applications for all21 claims.

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


The new checked-prefix word core passed in that919-source context; every compact prefix still needs its actual literal coefficient check before either complete mode can be accepted. [Generic staged receipt](integration/word-staged-core-verification.json). The current MSCI addition is a source component candidate, with strict actual-merger killed-rate/charge claims and a Rust port of the OLD exact observation-cutoff arithmetic. Rust87 tests passed; its complete Lean check rejected one local simplification term and awaits correction. It does not supply the full JC event/channel/recurrence/timed-genealogy equivalence. [Exact source comparison](integration/MSCI-REUSE-PREFLIGHT.md).

Run the old sufficient-cutoff calculator with `cargo run --locked -p research-commons-runtime --bin msci-cutoff -- n J P`. It retains arbitrary-precision integer output or structured refusal. The source-family/clock-JC hypotheses require actual admission; the number is not a parameter-identifiability or finite-data guarantee.

CI uses the existing explicit `[check word]`, `[check full]` and `[check completion]` commit markers or manual dispatch for expensive corresponding callers. Rust/current named-dependency/owned checks stay automatic. Skipped jobs do not count as acceptance; all required complete package/caller checks remain mandatory before closure.
