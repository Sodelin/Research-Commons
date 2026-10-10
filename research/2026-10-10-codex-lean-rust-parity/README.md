# Modular Lean baseline and corresponding Rust solver

Codex coordinator, 10 October 2026. **MASTER IN PROGRESS.** The requested four
Sol/max roles are Lean integration, theorem reuse, Rust implementation and solver
design. The coordinator checks their integration and scientific scope. The
[mission](MISSION.md) preserves the full original problem and
[traceability map](design/TRACEABILITY.md) records remaining obligations.
The [concise discovery map](design/DISCOVERY-MAP.md) explains the newest DOT
G3/G4 results, their older providers and the remaining gaps.
The [one-page research brief](design/RESEARCH-BRIEF.md) gives the four-lane overview.
The [goal completion sheet](design/GOAL-STATUS.md) distinguishes completed original
G1/G2/binary G5 proofs from G6/G7 formal assembly and remaining practical work.
The [G6/G7 reuse answer](design/G6-G7-REUSE-STATUS.md) states which gaps older
providers already solve and which new checked compositions consume them.

The starting baseline is commit `32f1538ebcd1a80b999bb14e08df905d13184ec7` on local
branch `codex/lean-rust-parity-20261010`. Main through `4d7a0467` was merged on
10 October after checking that incoming files did not overlap working changes.
Historical source and certificate bytes are preserved. No remote publication
or perpetual hosted job has been installed.

## Checked results

| Result | Evidence | Meaning |
|---|---|---|
| Public modular inventory | [Independent static review](quality/SOURCE-GRAPH-REVIEW.json), [source manifest](lean/SOURCE-MANIFEST.json), [dependency graph](lean/DEPENDENCY-GRAPH.json) | 1,342 exact public source versions, 52 explicit contexts, a new 1,340-module current union; byte/import/topological checks pass. This is distinct from the later delivered 1,411-module package and its historical 53-profile certificate. |
| Fresh complete current Lean union | [Preserved certificate](lean/CURRENT-CONNECTED-CERTIFICATE.json), [independent coordinator review](quality/CURRENT-CONNECTED-REVIEW.json) | All 1,340 components freshly compile without prior component reuse; aggregate and complete owned audit pass at trust zero: 97,493 declarations, 89,658 theorem declarations, no missing modules or owned/nonstandard axioms. The complete audit is distributed losslessly compressed. |
| Native Lean/Rust affine and conditional-count parity | [281/281 native replay](design/evidence/parity-attempt-2/PARITY-RECEIPT.json) | Canonical request/result bytes and exit codes match on tested cases, with independent original-row checks. The earlier UTF-8 refusal failure remains in attempt 1. |
| Independent affine decision checks | [249/249 exact graph oracle](quality/evidence/difference-review-1/RECEIPT.json), [250/250 exact Z3 oracle](rust/evidence/exact-z3-oracle-RESULT.json) | Separate decision methods agree on their finite cases. These counts are not unique theorem or source-coverage counts. |
| Kernel-checked standalone core | [Core certificate](lean/CORE-CERTIFICATE.json) | Eight owned modules, including CHART and LAW, checked at trust zero with complete declaration/axiom audit: 765 declarations, 93 theorem declarations. Native compilation is distinct from a universal Rust refinement proof. |
| Constructive witness, original bank and typed compiler proofs | [Historical reuse certificate](lean/REUSE-CERTIFICATE.json), [current typed certificate](lean/TYPED-REUSE-CERTIFICATE.json) | Eleven fresh modules and 41 exact original providers pass a complete 52-module audit: 2,272 declarations, 1,136 theorem declarations, no owned/nonstandard axioms. The current chain proves the original bank witness and ordered-list/finite-set compiler agreement, including the native 9/17-row two-tip fixtures. General raw-parser admission and universal solver refinement remain separate. |
| Native natural-cell parity | [78/78 chart and regression cases](design/evidence/chart-parity-attempt-1/PARITY-RECEIPT.json), [42/42 physical-bank cases](quality/evidence/chart-bank-review-1/RECEIPT.json) | BANK/MATRIX regeneration, direct physical-bank constraints, byte/exit agreement and forged-certificate refusals checked. Original-source admission remains separate. |
| Safe application component | [Launcher review](quality/LAUNCHER-REVIEW.json), [15/15 adapter challenges](design/evidence/adapter-challenge-2/ADAPTER-CHALLENGE-RECEIPT.json) | Witness, exclusion, budget UNKNOWN, binary-pin refusal, forged-certificate refusal and output preservation checked. |
| Natural-cell application | [Six launcher cases plus output preservation](quality/evidence/native-launcher-review-1/RECEIPT.json), [18/18 independent adapter challenges](design/evidence/chart-adapter-challenge-2/ADAPTER-CHALLENGE-RECEIPT.json) | Original-ID chart operation and separate certificate checks run through the practical launcher; admission/statistical gates remain false. |
| Full formal genealogy tables | [117/117 native cases](design/evidence/law-parity-attempt-1/PARITY-RECEIPT.json), [15 independent formula/budget cases](quality/evidence/law-native-review-1/RECEIPT.json), [two serial-hybrid cases](design/evidence/law-multi-hybrid-review-1/RECEIPT.json) | Exact rooted/unrooted coefficients agree with the pinned inherited compiler; COMMON/INDEPENDENT correlation, copied labels and conservative budgets checked. Finite checks do not establish universal original-model refinement. |
| Genealogy application integration | [Ten launcher cases plus output preservation](quality/evidence/genealogy-launcher-review-1/RECEIPT.json), [12 independent adapter challenges](design/evidence/law-adapter-challenge-1/ADAPTER-CHALLENGE-RECEIPT.json) | `genealogy-law` stages the native executable, discloses native replay, and independently compares every table coefficient. False but normalized tables are rejected. |
| Actual ordered population recurrence in Rust | [Population bridge contract](design/POPULATION-REFINEMENT.md), [8/8 original Lean/Rust/spectral comparisons](design/evidence/population-lean-rust-review-1/RECEIPT.json), [117/117 current-binary regressions](design/evidence/law-plus-population-regression-1/PARITY-RECEIPT.json) | The unchanged inherited Lean coefficient function executes through Lean's compiled evaluator; its full literal rows and unordered fibres agree with Rust and an independent exact generator oracle in all eight cases, including 193 literal rows and 37 fibres with four copies. Lean is not a standalone extracted ELF here. The general Rust refinement proof remains open. |
| Original population support and encoded-state closure | [Population fixture certificate](lean/POPULATION-FIXTURE-CERTIFICATE.json), [execution receipt](lean/evidence/source-population-execution/20261010T113514.964547Z/RECEIPT.json) | Complete 108-module audit passes with 3,741 declarations and 2,052 theorem declarations, no owned/nonstandard axioms; 14 fresh modules and 94 exact-context reuses. Generic arbitrary-fuel support and actual encoded-merger closure are proved. The valid-decoded carrier is broader than the actual encoded image. |
| Constructive panel joining and selected population support | [Support/join certificate](lean/SUPPORT-JOIN-CERTIFICATE.json), [coordinator saved-evidence review](quality/SUPPORT-JOIN-REVIEW.json) | Three fresh proof roots pass complete overlapping 117/120/120-module audits with no owned/nonstandard axioms or missing modules. They supply actual source-valid panel gluing, support-only equality to the unchanged original selected population polynomial and an executable copied-field join. The later full epoch product equality is separately checked; universal native refinement remains open. |
| Recovered original G7 full-epoch coefficients | [Compiler certificate](lean/COEFFICIENT-RECOVERY-CERTIFICATE.json), [independent coordinator review](quality/COEFFICIENT-RECOVERY-REVIEW.json) | Separately attributed proof repairs preserve all 15 executable definitions and 19 original theorem statements. The accepted 118-module context has 3,288 declarations and 2,074 theorem declarations, no owned/nonstandard axioms; the unchanged original failed attempt remains preserved. This does not yet establish general end-to-end Rust epoch refinement. |
| Internal Rust whole-epoch candidate | [Separate candidate inventory](rust/EPOCH-INVENTORY-20261010T1149Z.json), [9/9 independent coefficient/range checks](design/evidence/epoch-rust-review-1/RECEIPT.json), [117/117 existing protocol cases](design/evidence/epoch-candidate-regression-1/PARITY-RECEIPT.json) | Whole ancestor-closed panels, shared registers, full per-copy selected views and constructive literal joining are implemented. The candidate passes 40 Rust tests and has a separate binary/source identity; the accepted public runtime stays pinned independently. Actual original Lean whole-epoch comparison and universal refinement remain open. |
| Original G6 exposure and sharp exponent support | [Compiler certificate](lean/ORIGINAL-POPULATION-CERTIFICATE.json), [saved-evidence review](quality/PROOF-EXTENSION-REVIEW.json) | Two separate 88-module audits pass. Equal physical exposure preserves full population rows under correlated entering priors; every original recursion exponent is choose(j,2) with j bounded by entering live count. Global positive reconstruction remains open. |
| Sparse full-epoch equality | [Full epoch certificate](lean/FULL-EPOCH-SUPPORT-CERTIFICATE.json), [saved-evidence review](quality/PROOF-EXTENSION-REVIEW.json) | The 124-module audit passes: support-only literal products equal the unchanged original whole-epoch polynomial. Universal native/serialization refinement remains open. |
| Internal conditional boundary candidate | [Build receipt](rust/evidence/boundary-build-1/BUILD-RECEIPT.json), [independent 12-case coefficient review](design/evidence/boundary-rust-review-1/RECEIPT.json), [117-case regression](design/evidence/boundary-candidate-regression-1/PARITY-RECEIPT.json) | Separate candidate passes 49 Rust tests, all 12 ordered coefficient/range fixtures and existing protocol cases. The public runtime remains pinned. Typed sparse extraction and the fixed-word consumer remain in progress. |
| Additional newest DOT publication coverage | [Six-packet byte review](quality/evidence/publication-delta-4d7a0467/RECEIPT.json), [fresh arithmetic](quality/evidence/newest-arithmetic-replay-1/RECEIPT.json) | Six more commits and 40 paths through 4d7a0467 are checked separately from the frozen earlier discovery. New G3 output-size/three-log and G4 all-fair finite-forcing results retain their exact hand-proof scopes; no general G6/G7 closure follows. |
| Latest and historical source reconciliation | [Source identity review](quality/LEADING-INTEGRATION-REVIEW.json), [delivered canonical package](../2026-10-10-dot-connected-modular-lake-0855z/README.md) | Newly public 1,440-version/78-profile package and 219-version G7 recovery pool verified; 1,320 versions overlap our earlier inventory, with older/later versions retained separately. This review assigns no new compiler or theorem pass. |
| Recent DOT publication coverage | [Publication audit](quality/RECENT-PUBLICATION-COVERAGE.json), [discovery map](design/DISCOVERY-MAP.md) | All 29 commits and 2,659 changed paths from the initial snapshot through `d47787d8` are inventoried with matching published bytes; all 13 recent G3/G4 packets are linked. Publication coverage does not mean every historical argument has been rechecked. |
| New G3 two-head exact arithmetic | [Fresh three-script replay](quality/evidence/g3-two-head-replay-1/RECEIPT.json) | Rational rank/Hessian and full Sturm checks pass; independent long division verifies every Sturm step and reproduces the published polynomial bytes. This checks the finite algebraic certificate, not the analytic source-interior theorem, an extracted source witness or general G3. |
| New G3 killing/extraction and G4 inverse arithmetic | [Fresh six-script replay](quality/evidence/research-replay-1/RECEIPT.json) | Killing normal and positive quotient, valuation determinant, sparse exposure/interpolation, and five inverse fixtures reproduce their published exact arithmetic. The independently reproduced actual G4 inverse has a negative entry that refutes the proposed checkerboard-sign premise. These checks do not establish the all-length analytic proofs, a numerical killing cutoff, the full opaque-forest inverse bound or general G3/G4 closure. |
| New computable G3 cutoff chart | [Fresh exact chart replay](quality/evidence/cutoff-chart-replay-1/RECEIPT.json) | Published physical chart derivatives, rational inverse/rank and norm reproduce exactly. The hand result supplies a terminating restricted-family cutoff algorithm; its final numerical cutoff and NO fixture have not been evaluated. The new infinite-retained-tail corollary uses older closure/submersion results to force a finite retained list for boundary presentations, without an effective size bound. |
| Application source identity | [Derivative pins](APPLICATION-DERIVATIVE-PINS.json), [verifier](verify_derivative.py) | Current launcher/runtime bytes are recorded separately from the historical manifest; one intervening navigation update is explicit. Byte identity does not establish scientific admission. |

## Current implementation

The [RC1 contract](design/CONTRACT.md) gives exact rational AFFINE feasibility,
deterministic witnesses and original-row contradiction certificates. COUNT
computes conditional arithmetic and always preserves the missing-provider gate.
The [additive CHART contract](design/CHART-CONTRACT.md) connects original graph,
calendar, exposure and hybrid records to one shared bank of affine rows. Its
source-admission gate remains explicit. See [Rust build instructions](rust/README.md)
and the [application command](../../applications/practical-solver/README.md).
The [LAW contract](design/LAW-CONTRACT.md) adds the supplied-graph joint terminal
genealogy compiler with exact survival-variable polynomials and up to four
sampled copies. Its physical-image, observation and statistical bridges remain
separate unresolved obligations.

Constructive witness, typed source-bank decoding and certificate refinements
live in [reuse/sources](reuse/sources). Their individual compiler receipts, rather
than a file's presence, establish formal acceptance. The Lean integration role
owns compiler scheduling and proof receipts.

The full 1,340-module public union completed its fresh build, aggregate and
complete ownership audit on 10 October: 97,493 declarations and 89,658 theorem
declarations, no owned/nonstandard axioms and no missing modules. All 1,340
components compiled in this run without prior component reuse. External
prerequisites completed in 3,664 Lake jobs because the official HTTPS cache is
unavailable in this environment. The later 1,433-module union and 53-profile
public-layout replay have separate acceptance requirements and run statuses. Check current logs
before restarting any build.

The later [09:45 delivery handoff](../../handoffs/2026-10-09-goal-oriented-finish-lines/20261010T094500Z-CODEX-BUILD-HANDOFF.md)
explicitly supersedes the earlier publication hold. The canonical 1,411-module
and compatible 1,124-module historical audits are now delivered with the
53-required/25-provisional profile inventory. The public-layout replay checks all 53 required contexts: 52 under the original
policy, plus a separately preserved 6 GiB retry of the 337-module context.
[Independent saved-evidence review](quality/PUBLISHED53-REVIEW.json) verifies
the exact contexts and lossless portable evidence. These are not the same graph
as our 1,340-module union. Newly delivered G6 hand proofs and unfinished G7 candidate chains retain
their exact hand-review, failed and uncompiled boundaries.

## Review and continuation

Run these static checks from the repository root:

```bash
python3 research/2026-10-10-codex-lean-rust-parity/quality/check_source_graph.py
python3 research/2026-10-10-codex-lean-rust-parity/verify_derivative.py
```

Read [CHECKPOINT.md](CHECKPOINT.md) before continuing. Preserve old attempts and
record new binary/source identities after any change. Native parity, direct
physical-bank checks, formal refinement, graph/source admission, observation-law
coverage and statistical calibration have separate acceptance criteria.

Original unknown-size G3/G4 mathematics remains open. Broader G5 HG, G6 bounded
representatives/clouds and G7 effective policy consumers remain explicit in the
traceability map. This executable component is groundwork for the full solver;
it does not issue unrestricted all-source exclusion or empirical accuracy claims.
