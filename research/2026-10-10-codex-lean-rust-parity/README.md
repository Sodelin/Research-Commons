# Modular Lean baseline and corresponding Rust solver

Codex coordinator, 10 October 2026. **MASTER IN PROGRESS.** The requested four
Sol/max roles are Lean integration, theorem reuse, Rust implementation and solver
design. The coordinator checks their integration and scientific scope. The
[mission](MISSION.md) preserves the full original problem and
[traceability map](design/TRACEABILITY.md) records remaining obligations.

The starting baseline is commit `32f1538ebcd1a80b999bb14e08df905d13184ec7` on local
branch `codex/lean-rust-parity-20261010`. Main through `4e9f1ef2` was merged on
10 October after checking that incoming files did not overlap working changes.
Historical source and certificate bytes are preserved. No remote publication
or perpetual hosted job has been installed.

## Checked results

| Result | Evidence | Meaning |
|---|---|---|
| Public modular inventory | [Independent static review](quality/SOURCE-GRAPH-REVIEW.json), [source manifest](lean/SOURCE-MANIFEST.json), [dependency graph](lean/DEPENDENCY-GRAPH.json) | 1,342 exact public source versions, 52 explicit contexts, a new 1,340-module current union; byte/import/topological checks pass. This is distinct from the later delivered 1,411-module package and its historical 53-profile certificate. |
| Native Lean/Rust affine and conditional-count parity | [281/281 native replay](design/evidence/parity-attempt-2/PARITY-RECEIPT.json) | Canonical request/result bytes and exit codes match on tested cases, with independent original-row checks. The earlier UTF-8 refusal failure remains in attempt 1. |
| Independent affine decision checks | [249/249 exact graph oracle](quality/evidence/difference-review-1/RECEIPT.json), [250/250 exact Z3 oracle](rust/evidence/exact-z3-oracle-RESULT.json) | Separate decision methods agree on their finite cases. These counts are not unique theorem or source-coverage counts. |
| Kernel-checked standalone core | [Core certificate](lean/CORE-CERTIFICATE.json) | Eight owned modules, including CHART and LAW, checked at trust zero with complete declaration/axiom audit: 765 declarations, 93 theorem declarations. Native compilation is distinct from a universal Rust refinement proof. |
| Constructive witness and native checker proofs | [Reuse certificate](lean/REUSE-CERTIFICATE.json) | The recorded rational witness and original-row native checker source snapshot passed its complete owned audit. Two later typed-context source variants and the original-bank wrappers await separate current-source acceptance. |
| Native natural-cell parity | [78/78 chart and regression cases](design/evidence/chart-parity-attempt-1/PARITY-RECEIPT.json), [42/42 physical-bank cases](quality/evidence/chart-bank-review-1/RECEIPT.json) | BANK/MATRIX regeneration, direct physical-bank constraints, byte/exit agreement and forged-certificate refusals checked. Original-source admission remains separate. |
| Safe application component | [Launcher review](quality/LAUNCHER-REVIEW.json), [15/15 adapter challenges](design/evidence/adapter-challenge-2/ADAPTER-CHALLENGE-RECEIPT.json) | Witness, exclusion, budget UNKNOWN, binary-pin refusal, forged-certificate refusal and output preservation checked. |
| Natural-cell application | [Six launcher cases plus output preservation](quality/evidence/native-launcher-review-1/RECEIPT.json), [18/18 independent adapter challenges](design/evidence/chart-adapter-challenge-2/ADAPTER-CHALLENGE-RECEIPT.json) | Original-ID chart operation and separate certificate checks run through the practical launcher; admission/statistical gates remain false. |
| Full formal genealogy tables | [117/117 native cases](design/evidence/law-parity-attempt-1/PARITY-RECEIPT.json), [15 independent formula/budget cases](quality/evidence/law-native-review-1/RECEIPT.json), [two serial-hybrid cases](design/evidence/law-multi-hybrid-review-1/RECEIPT.json) | Exact rooted/unrooted coefficients agree with the pinned inherited compiler; COMMON/INDEPENDENT correlation, copied labels and conservative budgets checked. Finite checks do not establish universal original-model refinement. |
| Genealogy application integration | [Ten launcher cases plus output preservation](quality/evidence/genealogy-launcher-review-1/RECEIPT.json), [12 independent adapter challenges](design/evidence/law-adapter-challenge-1/ADAPTER-CHALLENGE-RECEIPT.json) | `genealogy-law` stages the native executable, discloses native replay, and independently compares every table coefficient. False but normalized tables are rejected. |
| Latest and historical source reconciliation | [Source identity review](quality/LEADING-INTEGRATION-REVIEW.json), [delivered canonical package](../2026-10-10-dot-connected-modular-lake-0855z/README.md) | Newly public 1,440-version/78-profile package and 219-version G7 recovery pool verified; 1,320 versions overlap our earlier inventory, with older/later versions retained separately. This review assigns no new compiler or theorem pass. |
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

The full public union is being compiled from pinned Mathlib sources because the
official HTTPS cache is unavailable in this environment. External prerequisites
completed in 3,664 Lake jobs. The full 1,340-module aggregate and audit remain
pending. Check current logs and receipts before restarting any build.

The later [09:45 delivery handoff](../../handoffs/2026-10-09-goal-oriented-finish-lines/20261010T094500Z-CODEX-BUILD-HANDOFF.md)
explicitly supersedes the earlier publication hold. The canonical 1,411-module
and compatible 1,124-module historical audits are now delivered with the
53-required/25-provisional profile inventory. Their public-layout fresh replay
is being prepared separately; they are not the same graph as our 1,340-module
union. Newly delivered G6 hand proofs and unfinished G7 candidate chains retain
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
