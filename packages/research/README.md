# Research Commons: portable Lean and Rust

This package assembles the canonical 118 research claims in dependency and reuse-priority order: 75 rated and 43 explicitly unranked. Existing proofs and engines are reused. Unresolved scientific statements retain their exact obligations. The end-to-end goal remains ACTIVE; all-claim integration is incomplete.

The current graph selects 1,613 retained modules plus 219 integration modules. There are 47 scoped named claim mappings and 512 declaration requests. Selection, separately checked components, a combined package build and all-claim completion are distinct gates.

## Build on a development host

Use Rust1.90.0, Lean4.33.1 and the exact Mathlib/source identities in [source-lock.json](source-lock.json). Python3/standard library is a test/reference dependency for the retained exact-query decoder; production quartet recovery is Rust.

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

The final per-claim completion gate currently exits2 because required bindings remain missing. A successful selected build or source preparation must not suppress that result.

## Verified components and current build boundary

Latest exact [source168/run40140586536](https://github.com/Sodelin/Research-Commons/actions/runs/40140586536):

- Rust122 workspace tests PASS.
- Complete26-source/six-name RAW-noise core and BOTH actual Rust-generated tree/cycle proofs in one28-source/458-declaration/309-theorem owned context PASS. Every actual returned value, strict-half integer-source uniqueness and ENTIRE positive returned support is checked. No owned/nonstandard axioms/missing modules. [Current receipt](integration/nanuq-noise-component-verification-v2.json).
- Full1499-source build is REJECTED at old VertexDiscriminatingSections,1414 successful/84 blocked. Combined512-name/owned/caller gates did not run. Current proof-only port preserves all9 statements. [Current frontier](integration/FRONTIER.md), [rejections](integration/causal-compiler-rejections.json).
- Complete51-source actual causal reversal is CLOSED at source166:1251 declarations/757 theorems, all4 statements unchanged. [Receipt](integration/causal-active-reversal-component-verification.json).
- The complete BOTH natural word is CLOSED at ed4ed337:1280 generated proof documents/69238 declarations/57433 theorems, SAME original three-copy/seven-operation/21-variable bank with register sampled once. No identical replay/cache/key work is selected. [Receipt and limits](integration/whole-natural-word-verification.json).
- Earlier raw NANUQ836-source/34-name, exact-query245-source/21-name, deterministic memory36-source/54-name, stochastic, genome, ownership, SAME-array block, founder-window, formal-model, rare-event calibration and actual contiguous-copy/caller contexts remain verified at their literal source-specific scopes. Their exact receipts and limitations are indexed in [the closed-component table](integration/FRONTIER.md#closed-integration-components-reuse-them).
- Historical complete930-source/24-mapping/165-name context and1659-source full library remain tied to their original sources; they do not confer current whole-package acceptance. [930-source receipt](integration/claim-export-verification-v16.json).

The strict118 completion gate still fails. Completed HAND science is preserved; actual formal/native/source/action/observer/target/QE joins remain explicit. No standalone context or selected source count substitutes for end-to-end acceptance.

## Actual Rust-to-Lean callers

Each caller below produced a complete native-output proof document and passed its separately recorded Lean scope.

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

Use `cargo run --locked -p research-commons-runtime --bin NAME -- ARG`. Emitters keep inputs in memory and return a complete document or refuse. Resource failures and insufficient certificates are UNKNOWN/INCONCLUSIVE.

`source-certificate --stdin MySource` accepts the original65,536-byte RC1 frame. Mixed-epoch and completion paths retain valid conditional-input premises; they do not invent a legal full-calendar prefix or external observation provider.

## Original source, real clocks and JC loci

The accepted MSCI modules use the ORIGINAL finite Code/Copy/graph/rates/register and real-date/pair-matrix spaces. They construct normalized four-base branches, semigroup/Fourier/generator identities, complete labelled-tree and original-copy readouts, finite loci and measurable decoded clocks. Native callers check all16 branch and64 tree probabilities at ONE returned clock/SAME matrix; they do not independently refit coordinates.

[JC69Source](lean/ResearchCommons/MSCI/JC69Source.lean) constructs a normalized finite-locus PMF over the actual original complete calendar/ancestral trace measure. Old one-root/chronological support is derived; sites share ONE trace before multiplication. The supplied whole original entering bank is mixed ONCE outside that integral. Finite NONEMPTY Copy is explicit. [Accepted source mixture](integration/jc69-source-mixture-verification.json).

[JC69Unranked](lean/ResearchCommons/MSCI/JC69Unranked.lean) transports original child swaps, real decorations, labels, pair ages and likelihoods. Original decoder/full completed-forest support then derives identical conditional one-site/finite-locus PMFs across different source carriers sharing the SAME Copy IDs, leafAge and observed full forest/matrix. Desired probability equality is the conclusion. [Accepted five endpoints/types/owned scope](integration/jc69-unranked-verification.json).

Actual measurable whole-source quotient factorization, empty observer, same natural-bank specialization, canonical source/event coverage, killed Fourier/root expansion, recurrence/reconstruction and universal native/provider/parser refinement remain genuine joins. The full canonical MSCI mathematics is completed at its own HAND scope and is not reopened by these formal tasks.

The existing observation-cutoff port reuses arbitrary-precision rational/integer arithmetic:

```sh
cargo run --locked -p research-commons-runtime --bin msci-cutoff -- 3 2 3
```

[Cutoff/source component](integration/msci-source-component-verification.json) and [entire coherent filters](integration/msci-alignment-verification.json) keep their distinct contracts. A computed sufficient cutoff is not empirical inference or a finite-data recommendation.

## Exact quartet component — bounded port and geometric proofs accepted

Reuse-priority10 CB-EXACTQUERY-001 already has a completed supplied-circle search, unknown-order learner, shared cache and later accepted query theorem. The original supplied-circle decoder is retained byte-identically. The Rust component ports its exact rectangle search/cache and provides the bounded command below; it does not derive another algorithm or replace complete displayed-topology support with coalescent probabilities.

```sh
printf '%s\n' '{"circle":[40,10,30,20],"answers":[{"quartet":[10,20,30,40],"mask":2}]}' |
  cargo run --locked -p research-commons-runtime --bin exact-quartet-recovery
```

Expected conditional output: gap[0,2] in the supplied circle, one original-label query and two predicates. Original masks use SORTED labels, not circle positions. Local mask checks do not validate a hidden graph/source or common circle. Missing answers/resources refuse the entire run as UNKNOWN; no successful prefix or source NO is returned.

The accepted Lean module proves the old all-position rectangle/split-union/subdivision/singleton/wrap primitives. Whole search/query-charge induction, original graph/circle/source admission, retained unknown-order caller and exact finite minimax remain separate. The eight fixed differential and actual stdin controls PASSED, as NEW interface verification rather than replay of old graph/producer/main suites. [Exact accepted scope](integration/exact-query-verification.json). [Exact source/component/limits/test contract](integration/EXACT-QUERY-RUST-INTEGRATION.md) · [predecessor/successor comparison](integration/EXACT-QUERY-REUSE-PREFLIGHT.md).

The ALREADY-existing original split/quartet/all-compatible-circle providers and chronological first-query trace PASSED their fresh full-context/runtime checks atc79deb20. Numeric source/oracle/circle admission and whole algorithm refinement remain separate. [Provider/reuse/remaining-join contract](integration/EXACT-QUERY-ORIGINAL-SOURCE-REUSE.md).

## Existing causal proof integration

All 145 inventoried original root-closure sources plus the alignment companion are retained byte-for-byte. The original author-complete upper/lower/zero-parameter mathematics keeps arbitrary finite binary-valued DAGs, latent and selection carriers, ONE common positive faithful mechanism, the full marked class, exact query budgets, positive-parameter lower bounds, promise-only exact optimum and arbitrary-seed/nontermination/infinite-expectation scope. Mathematical completion is not reopened by compiler compatibility work.

Selected proof-only variants adapt the retained source to the package's pinned Lean/Mathlib APIs. The existing checked G7 game replaces a duplicate namespace through an explicit import shim. No new source axiom, desired-law premise, transition oracle or weaker graph class is introduced. Whole causal/name/type/owned acceptance and native causal provider/response/selector/result binding remain pending. [Prior/successor comparison](integration/CAUSAL-REUSE-PREFLIGHT.md) · [Source selection](integration/causal-source-intake.json).

## Reused algebraic-profile finite-equation component

Reuse-rank14 CB-G4-006's three finite-ORIGINAL-equation endpoints now PASS source `73c84c99`, run40096997969/job120881390655: the complete selected owned audit has 4 declarations/4 theorems (including one generated simp theorem), zero rejects. The artifact, selected source hash, complete three printed types, exact owners and axiom lists were independently read/checked. This closes only that formal use-site of the OLD HAND theorem. RCF witness transfer, actual source/menu admission and enumeration, the O⇔D algorithm receiver and uniform all-rival stopping remain separate. [Receipt](integration/g4-algebraic-profile-component-verification.json), [types](integration/g4-algebraic-profile-complete-printed-types.json), [predecessor/successor comparison](integration/G4-ALGEBRAIC-PROFILE-REUSE-PREFLIGHT.md).

## Checks and remaining scope

Check a complete original claim interface with its actual audit root:

```sh
cargo run --locked -p research-commons-package -- build --reuse-retained --target SocialScience.Audit
cargo run --locked -p research-commons-package -- check-exports --target SocialScience.Audit --claim CB-SOFTSCI-001 --claim CB-SOFTSCI-002 --claim CB-SOFTSCI-003 --claim CB-SOFTSCI-004
cargo run --locked -p research-commons-package -- build --reuse-retained --target ClinicalModels.Audit
cargo run --locked -p research-commons-package -- check-exports --target ClinicalModels.Audit --claim CB-SOFTSCI-005
```

The same checker validates canonical metadata, exact dependencies, owning modules, printed types and the whole selected owned audit. The full package and strict all-claim gate remain separate. Dependency collection uses `build --reuse-retained --keep-going --target ResearchCommons.Integration.Exports`; failed dependencies are recorded as blocked and exit2 prevents acceptance.

Ordinary CI runs Rust, the current causal boundary and the COMPLETE combined named/owned checks. Previously accepted unchanged small contexts are reused by exact source hashes; manual dispatch or `[check scoped contexts]` runs their separate checks again. [Reuse record](integration/SCOPED-CHECK-REUSE.md). Existing expensive lanes use `[check word]`, `[check full]`, `[check completion]` or manual dispatch. `[check library]` selects the separate library lane. Skips provide no fresh evidence. Retained object reuse checks compiler, dependency, source and object-companion identities.

Remaining original source/target/action coverage, native row/word/raw-root/completion/readout refinement, AST/game/history-relative QE/selector/result origin and all claim-specific bindings are explicit in [FRONTIER.md](integration/FRONTIER.md). Unbound claims cannot silently pass the completion gate.

G1/G2/G5 baseline, P5 HAND completion, G6/G7 completed science and exact G3/G4 owner-HAND successors keep their original scopes. Recovery, aliases, ports and fresh checking are integration or validation, not new scientific discoveries. The original private writer/controller/transitive hooks remain UNBOUND; public fixed-synthetic Linux CI supplies no private execution permit. Existing owners and private/model/held/USED/UNKNOWN stops remain. Phone deployment is not a deliverable.

Current compatibility checkpoint: accepted51-source causal1251/757 plus NEW noise COMPLETE26-source/six-name432/291,0 owned/nonstandard/missing. Entire426626B noise artifact/all6 complete types/every source/row checked. Rust122 engine passed, but first actual generated proof ENTIRE rejected for missing vector notation; cycle not attempted. Current emitter-only import/kernel-arithmetic fix keeps numerical engine/output semantics. BOTH native docs and mandatory full1499/512-name/owned/actual callers pending; whole118 incomplete.

## Exact known-rate calibration component

`research_commons_runtime::calibration::Calibration` computes the OLD sharp finite-sample bounds with the retained BigRational engine. It keeps one immutable strict rate, sample count and both optimal decisions. The zero-sample case is supported; it makes no dependent/unknown-rate or empirical guarantee.

```sh
cargo run --locked -p research-commons-package -- build --reuse-retained --target ResearchCommons.Calibration.RareEvent
cargo run --locked -p research-commons-package -- check-exports --target ResearchCommons.Calibration.RareEvent --claim CB-MEMORY-004
cargo run --locked -p research-commons-package -- check-calibration-callers
```

The last command executes the existing literal proof checker on both a three-trial and an empty-sample output, followed by the full owned audit. Successful rendering alone supplies no acceptance. Source146 passes all115 Rust tests, the general20-name probability module and BOTH literal caller proofs/joint audit. Input-specific namespaces distinguish complete canonical rates/counts. This is the stated mathematical model, not dependent/unknown-rate or empirical calibration.

The NEW partial RAW NANUQ noise receiver is checked with `cargo run --locked -p research-commons-package -- check-exports --target ResearchCommons.NANUQ.RawNoise --claim CB-NANUQ-005` after building that target, then `check-nanuq-noise-callers`. Its native API owns a complete signed Rational matrix and original supplied circle labels; ties refuse and limits are UNKNOWN. Six formal components/two complete literal proof callers await current checking; original admitted-source/correct-order/exact-support/optimality joins are separate. [Reuse and exact scope](integration/NANUQ-NOISE-REUSE-PREFLIGHT.md).
