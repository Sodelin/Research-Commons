# Research Commons: portable Lean and Rust

This package assembles the canonical 118 research claims in dependency and reuse-priority order: 75 rated and 43 explicitly unranked. Existing proofs and engines are reused. Unresolved scientific statements retain their exact obligations. The end-to-end goal remains ACTIVE; all-claim integration is incomplete.

The current graph selects 1,613 retained modules plus 212 integration modules. There are 39 named claim mappings and 334 declaration requests. Selection, separately checked components, a combined package build and all-claim completion are distinct gates.

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

- **The complete natural-word caller passes in BOTH modes.** Source `ed4ed337`, [run40084273155](https://github.com/Sodelin/Research-Commons/actions/runs/40084273155), job120844040087: all 1,280 generated Lean documents, 69,238 owned declarations /57,433 theorems, zero owned axioms, nonstandard axioms or missing modules. This is the actual original 9-vertex/9-edge/4-taxon/1-hybrid source, three copies, seven operations and 21-variable correlated bank. Both complete natural laws and the SAME returned physical bank are checked. The natural register is sampled once. [Exact receipt and limits](integration/whole-natural-word-verification.json), [complete printed endpoint types](integration/whole-natural-word-complete-printed-types.json), [all generated source hashes](integration/whole-natural-word-source-manifest.json). The full original calendar, final observer, universal native/parser/provider refinement and complete source/action/target/QE/origin binding remain separate. This fixed word is CLOSED and is not selected for an identical rerun.
- **Three raw-tensor/readout receiver proofs pass.** Source `0958975a`, [run40090840783](https://github.com/Sodelin/Research-Commons/actions/runs/40090840783), job120863151776: complete 836-source/34-name context, 80,346 declarations /77,444 theorems, zero rejects. The original raw tensor equals actual quartet data on every label tuple, including repeated labels, and reuses the existing weighted/source blob-composition laws. The all-level circularity, exact-support and complete-source-coverage theorem remains a separate formal binding. Completed HAND mathematics is unchanged. [Receipt](integration/nanuq-raw-actual-join-verification.json), [complete printed types](integration/nanuq-complete-printed-types-v2.json), [reuse comparison](integration/NANUQ-RAW-ACTUAL-REUSE-PREFLIGHT.md).
- **Exact-query source and recursive geometry pass.** Source `61027b35`, [run40088841986](https://github.com/Sodelin/Research-Commons/actions/runs/40088841986): 21 exact declarations in the complete 245-source context; 5,029 declarations /3,331 theorems, zero rejects. Six recursive cover/disjoint/legal-endpoint proofs and the original source interfaces are reusable. Whole search, query-charge/minimax, actual source/circle/oracle and native refinement remain separate. [Receipt](integration/exact-query-scoped-context-verification.json).
- **Five original formal-model claim interfaces pass.** Source `fe0dccd2`, run40085312861: all 85 original theorem names/owners and complete 9+5-module contexts; 318 owned declarations, zero rejects. These are deterministic/Boolean/integer model claims; no empirical or clinical inference is asserted. [Receipt](integration/soft-science-component-verification.json), [complete printed types](integration/soft-science-complete-printed-types.json).
- The earlier complete **930-source/24-mapping/165-name context** passed at `c79deb20`: 22,333 declarations /14,950 theorems, zero rejects. [Receipt](integration/claim-export-verification-v16.json). The full 1,657-source library plus two roots passed separately at `766c83b3`: 105,185 declarations /94,755 theorems. Historical `67ef70da` passed the eleven-caller sequence and 1,638-source library. Those receipts remain tied to their actual sources.
- **111 Rust workspace tests pass** at `fe0dccd2`, run40085312861. The bounded exact-query unknown-order/shared-cache command passed its 13 differential/CLI controls within the earlier 107-test suite.
- **The original causal graph projection component passes.** Source `6f17bed6`, [run40101349532](https://github.com/Sodelin/Research-Commons/actions/runs/40101349532), job120894134044: complete25-source owned context, 890 declarations /499 theorems, zero owned axioms, nonstandard axioms or missing modules. This checks the original bounded canonical source, baseline and each indicator graph transport, literal full marked MAG/TCM preservation and ancestral-graph laws. Artifact/source hashes and every owned row were independently verified. Full causal upper/lower/zero-parameter roots and native/parser/provider/selector joins remain separate. [Exact component receipt](integration/causal-original-graph-component-verification.json).
- **The original26-source marginal graph extension also passes.** Source `339b676b`, [run40103389432](https://github.com/Sodelin/Research-Commons/actions/runs/40103389432), job120900122604:902 declarations /508 theorems, zero owned axioms/nonstandard/missing; all26 source hashes and902 actual owned rows independently validated. The original29-source total profile decoder separately compiles. [Exact marginal graph receipt](integration/causal-marginal-graph-component-verification.json).
- The latest actual **1,462-source combined target remains rejected** at source49380f95:1,353 successful objects (97 compiled /1,256 reused), one failed module /108 blocked. The complete31-source transcript decoder compiles. The newer28-source query-family boundary compiled its finite subtype but still needs equality on that subtype to enumerate Boolean functions. The current precise instance repair and full1466-source context remain unchecked. [Failures](integration/causal-compiler-rejections.json).
- **Two original genome claim interfaces and their carrier join pass.** Source `b094ae85`, [run40105632721](https://github.com/Sodelin/Research-Commons/actions/runs/40105632721): complete32-source/20-name context,1,773 declarations /1,306 theorems, zero owned/nonstandard/missing. All20 COMPLETE printed types, owners/axioms and32 source hashes were read/validated. These are the original abstract finite-gARG obstruction and prescribed three-taxon exact/finite-evidence scopes. No biological/DNA/aggregate-error/Hoeffding Lean theorem is inferred. [Receipt](integration/genome-original-components-verification.json), [types](integration/genome-complete-printed-types.json).
- **Actual MSci root-pair moments pass.** Source `b094ae85`, complete3-source/3-name context,44 declarations /36 theorems, zero rejects. All3 COMPLETE printed types/owners/axioms and3 source hashes were checked. This OLD two-site theorem's root-pair step uses the actual exponential probability integral and SAME positive rate/onset. The full nine-parameter/source/JC/Jacobian/native contractor joins remain separate. [Receipt](integration/msci-root-pair-component-verification.json).
- **The original refined separator passes** in its complete27-source context:920 declarations /523 theorems, zero rejects. The complete31-source transcript decoder later compiles with the existing concrete equality dictionary. The next blocker is ONE equality instance for Boolean functions on the exact original finite query-family subtype; the pending target grows to1466 sources/334 names by directly importing four unchanged stochastic-history sources. [Separator receipt](integration/causal-refined-separator-component-verification.json), [failures](integration/causal-compiler-rejections.json).
- **Pending original stochastic-history interface:**20 unchanged theorem names reuse exact PMF quotient, full finite joint history/controller preservation and all-horizon counterexamples. No new proof or simulator. The complete4-source named/owned check is pending. [Source/reuse](integration/memory-stochastic-source-intake.json).

Every accepted scope has independently recovered artifact/hash/source/type/owner/axiom evidence. Rejected complete attempts stay rejected. Clean partials do not count as full acceptance. [Verification history](VERIFICATION.md) · [Current frontier](integration/FRONTIER.md).

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
