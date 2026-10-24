# Research Commons: portable Lean and Rust

This is the user-requested portable end-to-end package for the canonical118 claims, in reuse/dependency order:75 rated and43 explicitly unranked. Existing mathematics/engines are reused; unresolved questions retain exact obligations. The goal is ACTIVE. Current source selects1,613 retained modules plus209 selected integration/proposal modules. Registry accounting is complete; actual integration of all118 is not.

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

## Current actual verification

- **Sourcec79deb20/run40062353912 passed102 Rust tests and the COMPLETE930-source selected Lean/owned context.**42 integration modules compiled/888 exact retained objects reused;22333 declarations/14950 theorems, zero owned axioms/nonstandard rows/missing modules.
- **24 SCOPED mappings/165 exact declaration names and owners passed**, including9 typed original-source query providers. These9 additions are definitions/exports of OLD results, not9 new mathematical theorems.94 claims remain unnamed at that accepted source. Every later positive-signature/JC16/native64/BOTH entire parameter-filter command and owned audit passed. [Exact receipt](integration/claim-export-verification-v16.json).
- The **full1,657-source library+2roots** remains separately accepted at766c83b3:105185 declarations/94755 theorems, zero rejects. [Receipt](integration/coherent-library-verification-v6.json). This library-only check skipped its expensive caller sequence; it is not fresh full1808-library/word/118 acceptance.
- Historical source67ef70da passed the complete eleven-caller sequence and1,638-source library. [Receipt](integration/full-profile-verification.json). Acceptance never transfers automatically to changed source.
- Latest source5b91ebb8/run40070946133 passed **107 Rust tests**, including the retained unknown-order/shared-cache production caller and actual CLI. [Exact port verification](integration/exact-query-order-verification.json). Its SAME full1,077-source causal target is correctly REJECTED at one original identity-map proof:940 successful objects (52 compiled/888 reused),1 failed module and136 blocked consumers. Full owned/name/type acceptance remains absent. The selected compatibility repair preserves original predicates and146 frozen vendor bodies. [Actual failures](integration/causal-compiler-rejections.json).
- The source282a95e1 full-word job is now rejected at a renderer syntax error before Stage0 coefficient checking. Literal braces are repaired with a runtime-wide format lint and emitted-stage regression; the changed SAME full BOTH-word check remains required. [Exact rejection](integration/word-stage-literal-rejection.json). Original private native/controller admission remains UNBOUND.

Raw receipts retain their phase boundaries: source build precedes owned audit, and initial owned=false stays literal even when the later actual owned audit passes. Actual artifacts/hashes/counts and every rejected predecessor remain in [VERIFICATION.md](VERIFICATION.md). [Retained-object validation](integration/RETAINED-OBJECT-REUSE.md) checks compiler/dependency/source/object-companion identities.

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

## Existing causal proof package — selected, not elaborated

The original author-complete upper/lower/k0 proposal is now included: ALL145 inventoried root-closure sources plus its source-alignment companion, byte-authenticated146 sources. It preserves arbitrary finite original binary-VALUED DAGs, latent/selection carriers, one common positive faithful bank, full marked class, exact population-query budgets, k>0 lower, promise-only exact optimum and arbitrary-seed/nontermination/infinite-expectation scope. Hand mathematics remains completed; the new kernel/owned and native integration is separate.

The proposed local G7 copy would duplicate an existing namespace. A documented import shim reuses the already checked G7 game; original vendor bytes remain unchanged. No duplicate engine, weakened theorem, smaller closure, new scientific discovery or native causal provider is claimed. Current actual full-context checks are PENDING. [Prior/successor/reuse/acceptance contract](integration/CAUSAL-REUSE-PREFLIGHT.md) · [all source hashes/selection](integration/causal-source-intake.json).

## Complete word: exact remaining blocker

The earlier generic174/175/176-source sparse/epoch/word-cache theorem contexts passed. The actual unchanged three-copy/seven-operation/BOTH-mode word still needs its full total coefficient and physical/final owned result.

Source89/run40050896773/job120743281427 is terminal REJECTED at Stage3: all416 primitive documents and Stage0/1/2 compiled, then its total Boolean did not reduce after38 cache-match hints. No false coefficient, host/timeout/memory diagnosis or partial final acceptance is established. [Complete rejection history](integration/word-stage-literal-rejection.json).

Changed executablef1cd000c explicitly exposes existing matched certificate/entry/row payloads and finite-list product algebra before the SAME total checker. The source/copies/operations/all keys/register/bank and both modes stay mandatory. Job120769448710/run40059355260 is TERMINAL REJECTED at Stage3 line533,45,722B/SHA75b99a23: even explicit payload/list expansion leaves the total checkRows Boolean non-reducing. No false coefficient or host/resource cause is established. This source import does not replay or replace it. [Proof-rendering reuse/implementation contract](integration/WORD-PAYLOAD-REUSE-PREFLIGHT.md).

## Scope and next integration

All118 cards remain accounted for by kind. Named components are not whole scientific claim closure. Remaining source/target/action coverage, native row/word/raw-root/completion/readout refinement, AST/game/history-relative QE/selector/result origin and claim-specific full bindings remain explicit in [FRONTIER.md](integration/FRONTIER.md).

CI automatically runs Rust/current named dependency/owned checks and the strict completion gate. Existing expensive jobs use `[check word]`, `[check full]`, `[check completion]` or manual dispatch. `[check library]` selects full-library/owned/export checks in a separate non-cancelling group and skips the caller sequence. Skipped jobs supply no fresh receipt.

Completed G1/G2/G5/P5/G6/G7 science and G3/G4 owner-HAND successors retain their original proof/status/quantifier scopes. Source recovery, ports and wrappers are not new scientific discoveries. No private-controller admission follows from public fixed-synthetic CI: original writer/controller/transitive hooks remain UNBOUND; private/model/held/USED/UNKNOWN stops and existing owners remain. Phone deployment is not this deliverable.

For integration diagnosis, `build --reuse-retained --keep-going --target ResearchCommons.Integration.Exports` collects failures in independent modules, records dependent modules as blocked, and exits2 if any selected source failed. It is the SAME complete target and cannot provide export/owned/caller acceptance after a failure. [Reuse and failure semantics](integration/BUILD-FAILURE-COLLECTION-REUSE-PREFLIGHT.md).


The same production `exact-quartet-recovery` command now also accepts `labels` instead of `circle` to run the retained unknown-order learner plus sparse decoder with one shared query cache. Supply exactly one carrier and the same complete-support `answers`; missing answers/resources refuse the whole request. The actual13-case differential/output/order/trace and CLI/refusal checks passed within107 Rust tests at5b91ebb8; source/oracle admission and universal algorithm/query-charge refinement remain open. [Source comparison and scope](integration/EXACT-QUERY-UNKNOWN-ORDER-REUSE.md).


Latest current checks:107 Rust tests passed at4ab958eb. ALL14 retained model modules/85 original theorem proofs compiled at the new Lean pin. All85 actual axiom reports use only permitted standard axioms. Full1092-source export checking remains rejected at one ambiguous ancestry endpoint, after963 successful objects; whole name/type/owned acceptance has not run. The next exact proof variant retains every source/theorem statement. The independent SAME full BOTH-word job continues. [Current frontier](integration/FRONTIER.md).


The direct original social-science/model intake adds85 OLD formal theorem declarations across five cards, with original owner modules and no alias proofs. Their historical4.19 receipts remain scoped; current4.33.1 package acceptance is pending. [Exact reuse and model limits](integration/SOFT-SCIENCE-REUSE-PREFLIGHT.md).
