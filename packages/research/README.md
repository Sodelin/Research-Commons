# Research Commons: portable Lean and Rust

The package integrates the canonical claim registry in reuse and dependency order. Existing proofs and engines are reused; unresolved questions retain exact obligations. The pinned snapshot has **118 claims:75 reuse-rated and43 unranked**, at447e188d. The candidate graph has1,613 retained modules plus39 integration modules.

## Build on a development host

Use Rust1.90.0 and Lean4.33.1. Exact compiler/dependency/source identities are in [source-lock.json](source-lock.json).

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

The full per-claim gate remains incomplete and exits2 until every required binding has actual verification.

## Verified package evidence

- **88 Rust tests passed** at[sourceb169feb4/run40029043141](https://github.com/Sodelin/Research-Commons/actions/runs/40029043141).
- **22 scoped claim mappings/100 actual Lean declaration names and owners passed**, with the complete920-source export context and22030-declaration/14765-theorem owned audit. Zero owned axioms, nonstandard rows or missing modules.96 claims remain without named exports. [Exact receipt](integration/claim-export-verification-v6.json).
- The latest accepted **complete library** is sourcef7f8a356:1,649 sources plus generated roots,104893 declarations/94588 theorems audited. Its later literal word rejected. [Library receipt](integration/coherent-library-verification-v3.json). This does not accept the later1,652-source/15-caller sequence.
- The earlier source67ef70da passed its complete eleven-caller sequence and1,638-source library. [Receipt](integration/full-profile-verification.json). Historical acceptance does not transfer automatically to changed code.

Retained-object reuse validates the exact compiler, dependencies and every object companion. Added modules and literal callers are checked; complete owned audits are mandatory. [Reuse contract](integration/RETAINED-OBJECT-REUSE.md).

## Actual end-to-end callers

Each path below produced a complete proof document from Rust output and passed Lean checking at its recorded source.

| Caller | Checked input and conclusion | Evidence |
| --- | --- | --- |
| `cm-certificate` | Grouped rational positive laws; literal sparse-moment separation | [CM/affine](integration/certificate-verification.json) |
| `moment-signature-certificate` | Complete seven-coordinate signature of one three-atom law; total masses against EVERY finite positive rival, then every further moment | [Signature](integration/moment-signature-verification-v3.json), [exact input](examples/PositiveMomentSignature.lean) |
| `affine-certificate sat/unsat` | Ordered rational matrix; real witness or full external-multiplier exclusion | [CM/affine](integration/certificate-verification.json) |
| `source-certificate tree/parallel/infeasible` | Actual original Code/admission/ordered fields; SAME returned positive physical bank, or only supplied-cell exclusion | [Source/cell](integration/source-cell-verification.json) |
| `population-certificate edge/ancestral/path` | Actual native population row; total coefficients including zero on absence, original validity/colocation and SAME bank | [Population](integration/population-caller-verification.json) |
| `epoch-certificate` | Four copies/two original populations; all nine selected endpoint rows, raw witnesses, total coefficients and SAME bank | [Mixed epoch](integration/epoch-caller-verification.json) |
| `completion-certificate` | Conditional ancestral input; all12 ordered constant rows, true infinite ancestral limit, SAME rates and passive comb probability1/3 | [Completion](integration/completion-caller-verification.json) |
| `residual-certificate` | Complete rational ensemble; strict top-k set and residual conservation | [RNA](integration/rna-results-verification.json) |

Run a binary with `cargo run --locked -p research-commons-runtime --bin NAME -- ARG`. Emitters retain inputs in RAM and return a complete document or refuse. Resource failure and insufficient certificates remain UNKNOWN or INCONCLUSIVE.

The signature component reuses the existing sparse separator and positive-grid interpolation. Its all-finite-rival conclusion has no rival-size cap. Reaction coefficients, stopped-law/shifted-Euler observables, derivative acquisition and universal native refinement remain separate. The completed CB-RXN-001 hand proof is retained at its original scope.

The source caller also accepts `source-certificate --stdin MySource` within the original65,536-byte RC1 frame. Mixed-epoch and completion callers retain explicit valid conditional inputs; they do not construct a legal global calendar prefix or the external four-taxon tester.

## Reusable MSCI component

[ResearchCommons.MSCI.KilledClocks](lean/ResearchCommons/MSCI/KilledClocks.lean) passed its actual current-source/dependency/type/owned checks. For every finite original Copy/Site carrier it uses the existing same-rate surviving-clock embedding, actual legal merger and complete current-tree charges to derive strict total/killed-rate decrease. It does not assume a desired transition law.

The Rust library ports the OLD exact sufficient observation-cutoff calculation, using retained arbitrary-precision arithmetic and explicit profile/work/magnitude refusals:

```sh
cargo run --locked -p research-commons-runtime --bin msci-cutoff -- 3 2 3
```

Three immutable retained controls, beyond-machine-integer output, refusals and the zero-epoch profile boundary passed. [Exact accepted component](integration/msci-source-component-verification.json) · [prior/successor comparison](integration/MSCI-REUSE-PREFLIGHT.md).

This is a component of CB-MSCI-001. The actual JC event/channel/epoch/recurrence/timed-genealogy theorem and complete source admission are separate. The number is not an inference result or a finite-data recommendation.

## Independent verification targets

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

The isolated CM/affine context remains available through `prepare-certificates`/`build-certificates`. Qualified-menu/RNA exports preserve actual source/shape/joint-response, positivity, random-input and BE-origin premises. No wrapper converts those premises into implementation evidence.

## Remaining integration

[claims.json](integration/claims.json) preserves every ID/rating and actual Lean/Rust scope. [FRONTIER.md](integration/FRONTIER.md) names the current work; [VERIFICATION.md](VERIFICATION.md) retains failures and corrections.

The generic same-bank checked-prefix word theorem passed. Every compact literal prefix still requires its own complete coefficient check, followed by both full independent/COMMON modes and the whole owned caller audit. The original ungrouped three-copy word rejected its final composition/parent proof after all supplied primitives. [Generic staged receipt](integration/word-staged-core-verification.json) · [exact earlier rejection](integration/word-cache-literal-rejection-v3.json). The original source/copies/operations/full keys/register and SAME bank remain.

Still separate:96 unnamed claim exports and remaining scoped applications; complete physical source/target/action coverage; native/parser/AST/controlled-word/raw-root/readout refinement; actual history-relative QE/selector/result origin. G3 all-input and the original open scientific endpoints remain open. Missing formal/native joins do not reopen completed hand mathematics.

Expensive existing CI jobs use `[check word]`, `[check full]`, `[check completion]` commit markers or manual dispatch. Rust/current dependency/owned checks remain automatic. Skipped jobs provide no acceptance; all required complete checks remain mandatory before closure. Evidence-only commits name actual checked sources and create no fresh CI result.
