# Research Commons: portable Lean and Rust

The package integrates the canonical claim registry in reuse and dependency order. Existing proofs and engines are reused; unresolved questions retain exact obligations. The pinned snapshot has **118 claims:75 reuse-rated and43 unranked**, at447e188d. The candidate graph has1,613 retained modules plus44 integration modules; the all-finite tree-channel module and its complete64-entry native caller are accepted at their exact scopes; the original-copy readout is accepted; the real-date measurability join is accepted at its exact scope.

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

- **97 Rust tests passed** at[source631dbaa0/run40047327555](https://github.com/Sodelin/Research-Commons/actions/runs/40047327555), including three new complete JC-tree column/label/refusal groups. The generic tree component and complete native64-entry caller also passed at source631dbaa0/run40047327555.
- **23 scoped claim mappings/137 actual Lean declaration names and owners passed** atsource766c83b3, with the complete925-source export context and whole owned audit. Zero owned axioms, nonstandard rows or missing modules.95 claims remain without named exports. [Exact receipt](integration/claim-export-verification-v12.json). These are scoped components where stated, not137 complete scientific endpoints.
- The **complete1,657-source library +2roots passed** atsource766c83b3:105185 declarations/94755 theorems audited, zero owned axioms/nonstandard rows/missing modules. [Full receipt](integration/coherent-library-verification-v6.json). This library-only mode intentionally skips the expensive caller sequence; it is not whole-word or118-claim acceptance.
- The earlier source67ef70da passed its complete eleven-caller sequence and1,638-source library. [Receipt](integration/full-profile-verification.json). Historical acceptance does not transfer automatically to changed code.

Retained-object reuse validates the exact compiler, dependencies and every object companion. Added modules and literal callers are checked; complete owned audits are mandatory. [Reuse contract](integration/RETAINED-OBJECT-REUSE.md).

## Actual end-to-end callers

Each path below produced a complete proof document from Rust output and passed Lean checking at its recorded source.

| Caller | Checked input and conclusion | Evidence |
| --- | --- | --- |
| `cm-certificate` | Grouped rational positive laws; literal sparse-moment separation | [CM/affine](integration/certificate-verification.json) |
| `alignment-certificate coherent/incoherent` | ENTIRE supplied rational coherent-parameter filters, EVERY map and omission, SAME adjacent-layer ties | [Alignment](integration/msci-alignment-verification.json) |
| `jc69-certificate` | All16 actual four-base branch probabilities/row sums, SAME returned finite normalized-clock time | [JC branch](integration/jc69-branch-verification.json) |
| `jc69-tree-certificate` | All64 actual original3-copy pattern probabilities, complete normalization, ONE chronological clock/SAME decoded pair matrix and finite conditional loci | [JC tree](integration/jc69-tree-caller-verification.json) |
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

## Actual JC branch and coherent parameter filter

[JC69](lean/ResearchCommons/MSCI/JC69.lean) constructs the normalized PMF and proves its semigroup/Fourier/charge, generator and common-root pair/clock identities. The complete Rust16-entry table passed Lean checking and the selected caller owned audit at ONE returned time. [Exact record](integration/jc69-branch-verification.json).

The OLD CB-MSCI-002 coherent parameter filter is now implemented in [Rust](crates/runtime/src/alignment.rs), using exact supplied rational durations/rates/routing arrays. ONE hidden renaming is shared by both adjacent matrices; initial/root names stay fixed. It returns the whole filter or explicit invalid/resource refusal. Equal rates, support zeros and backward expansion are retained.

```sh
cargo run --locked -p research-commons-runtime --bin jc69-certificate
cargo run --locked -p research-commons-runtime --bin alignment-certificate -- coherent
cargo run --locked -p research-commons-runtime --bin alignment-certificate -- incoherent
```

The generic Lean filter equations/types AND BOTH complete actual filter results passed, including every omitted map and the full22133/14830 caller owned audit. Computational dependent arrays, explicit Fin indices and trusted kernel reduction repaired the earlier rejected renderers. [Exact accepted results](integration/msci-alignment-verification.json). [Exact rejection](integration/alignment-component-rejection.json) · [reuse comparison](integration/MSCI-ALIGNMENT-REUSE-PREFLIGHT.md). Structural array checks do not supply full canonical source admission, actual nested-forest observability or the whole classification theorem. JC branch checking also does not supply the full timed-tree/locus/source equivalence.

## Original-tree JC channel

[JC69Tree](lean/ResearchCommons/MSCI/JC69Tree.lean) constructs normalized patterns and conditional loci on EVERY finite ORIGINAL Genealogy, derives the Fourier factor, retains original copy IDs and reuses G2's SAME pair-matrix/age decoder. Its thirteen new named exports passed the complete923-source context/owned audit, and the original-copy successor brings the current scoped map to131 names. [Accepted generic component](integration/jc69-tree-verification.json).

[Rust pruning](crates/runtime/src/jc69_tree.rs) borrows the retained Tree and exact JC branch arithmetic, preserves one immutable branch/label bank and returns every pattern or explicit refusal. It passed its new tests. The actual three-tip caller emits all64 probabilities and proofs tying them to ONE coherent chronological clock and the decoded pair matrix:

```sh
cargo run --locked -p research-commons-runtime --bin jc69-tree-certificate
```

The COMPLETE generic tree module and SEPARATE64-entry caller now passed, including normalization, coherent chronology, SAME decoded pair-matrix clock and arbitrary finite conditional locus. The full caller audit has22293 declarations/14924 theorems and zero rejects. [Actual source/table/receipt](integration/jc69-tree-caller-verification.json). The actual original-copy PMF/Fourier adapter also passed its COMPLETE924-source/131-name context and owned audit at555695d9. [Readout receipt](integration/jc69-original-readout-verification.json). [Generic proof history](integration/jc69-tree-component-rejection.json) · [Actual caller failure](integration/jc69-tree-caller-rejection.json) · [predecessor/successor reuse](integration/JC69-TREE-REUSE-PREFLIGHT.md). The full unranked timed-output quotient, measurable source/channel mixture and bounded recurrence/reconstruction are still separate.

## Independent verification targets

```sh
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Integration.Exports
cargo run --locked -p research-commons-package -- check-exports --target ResearchCommons.Integration.Exports
cargo run --locked -p research-commons-package -- check-moment-callers --in-exports
cargo run --locked -p research-commons-package -- check-jc-callers --in-exports
cargo run --locked -p research-commons-package -- check-jc-tree-callers --in-exports
cargo run --locked -p research-commons-package -- check-alignment-callers --in-exports
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

The generic same-bank checked-prefix word theorem passed. Every compact literal prefix still requires its own complete coefficient check, followed by both full independent/COMMON modes and the whole owned caller audit. The original ungrouped word rejected its final composition/parent proof; the staged successors reached all primitives and then rejected a missing namespace followed by an unparenthesized composite Symbol argument. Those exact references/parentheses are corrected; that SAME-source word run40042311302/job120716173428 passed its first3 stages and then rejected Stage3 when its whole coefficient Boolean did not reduce. No false coefficient or host cause is established; the previous full job120711863617 is now terminal at the same old Symbol parse error, after its full library/export commands passed; the successor old full job120716173831 is now terminal at the SAME Stage3 Boolean after its full1654 library/export commands passed; fresh changed-source word job120743281427 remains running. [Generic staged receipt](integration/word-staged-core-verification.json) · [exact earlier rejection](integration/word-cache-literal-rejection-v3.json) · [staged successor rejection](integration/word-stage-literal-rejection.json). The original source/copies/operations/full keys/register and SAME bank remain.

Still separate:95 unnamed claim exports and remaining scoped applications; complete physical source/target/action coverage; native/parser/AST/controlled-word/raw-root/readout refinement; actual history-relative QE/selector/result origin. G3 all-input and the original open scientific endpoints remain open. Missing formal/native joins do not reopen completed hand mathematics.

Expensive existing CI jobs use `[check word]`, `[check full]`, `[check completion]` commit markers or manual dispatch. `[check library]` reuses the full library/owned/export job and skips its expensive caller step, in a separate non-cancelling group; this verifies library scope only. Rust/current dependency/owned checks remain automatic. Skipped jobs provide no acceptance; all required complete checks remain mandatory before closure. Evidence-only commits name actual checked sources and create no fresh CI result.

The first real-date measurability attempt rejected its graft product conversion in BOTH selected and full-library contexts. The successor preserves the same function/spaces and uses explicit kernel reflexivity; [exact rejection](integration/jc69-measurable-rejection.json). The word emitter now exposes every previous native-row/cache match as a separate kernel theorem before the unchanged total coefficient check. Those hints, complete BOTH modes and final audits are still pending. [Exact reuse/implementation scope](integration/WORD-STAGE-CACHE-MATCH-REUSE-PREFLIGHT.md).

The real-date likelihood/decoded-matrix/conditional-locus/original-copy measurability component now PASSED its complete925-source/137-name and full1657 library contexts at766c83b3. [Exact accepted scope](integration/jc69-measurable-verification.json). Actual original source-measure mixing and unranked observable descent remain separate; the changed SAME-word cache-match/literal/physical audit is still running.

A source-mixture adapter is now authored for checking: [JC69Source](lean/ResearchCommons/MSCI/JC69Source.lean) integrates the conditional locus on one actual original calendar/ancestral trace, with the entire register bank mixed once. It reuses the original probability/support theorems and real matrix; all8 new endpoints remain unverified until their fresh complete context/audit passes. [Exact reuse and remaining joins](integration/JC69-SOURCE-MIXTURE-REUSE-PREFLIGHT.md).

The first source-mixture check rejected the adapter's cardinality name and missing local decision instance. The repair preserves the original source/clock/locus data; all8 names still require a complete fresh check. [Observed rejection and repair](integration/jc69-source-mixture-rejection.json).
