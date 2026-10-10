# Modular Lean baseline and corresponding Rust solver

Codex coordinator, 10 October 2026. **MASTER IN PROGRESS.** The requested four
Sol/max roles are Lean integration, theorem reuse, Rust implementation and solver
design. The coordinator checks their integration and scientific scope. The
[mission](MISSION.md) preserves the full original problem and
[traceability map](design/TRACEABILITY.md) records remaining obligations.

The working baseline is commit `32f1538ebcd1a80b999bb14e08df905d13184ec7` on local
branch `codex/lean-rust-parity-20261010`. Historical source and certificate bytes
are preserved. No remote publication or perpetual hosted job has been installed.

## Checked results

| Result | Evidence | Meaning |
|---|---|---|
| Public modular inventory | [Independent static review](quality/SOURCE-GRAPH-REVIEW.json), [source manifest](lean/SOURCE-MANIFEST.json), [dependency graph](lean/DEPENDENCY-GRAPH.json) | 1,342 exact public source versions, 52 explicit contexts, a new 1,340-module current union; byte/import/topological checks pass. This is not the held 1,411-module package or its historical 53-profile certificate. |
| Native Lean/Rust affine and conditional-count parity | [281/281 native replay](design/evidence/parity-attempt-2/PARITY-RECEIPT.json) | Canonical request/result bytes and exit codes match on tested cases, with independent original-row checks. The earlier UTF-8 refusal failure remains in attempt 1. |
| Independent affine decision checks | [249/249 exact graph oracle](quality/evidence/difference-review-1/RECEIPT.json), [250/250 exact Z3 oracle](rust/evidence/exact-z3-oracle-RESULT.json) | Separate decision methods agree on their finite cases. These counts are not unique theorem or source-coverage counts. |
| Kernel-checked standalone core | [Core certificate](lean/CORE-CERTIFICATE.json) | Six owned modules, including CHART, checked at trust zero with complete declaration/axiom audit. Native compilation is distinct from a universal Rust refinement proof. |
| Constructive witness and native checker proofs | [Reuse certificate](lean/REUSE-CERTIFICATE.json) | Rational witness and original-row positive/negative native checker refinements pass their complete owned audit. |
| Native natural-cell parity | [78/78 chart and regression cases](design/evidence/chart-parity-attempt-1/PARITY-RECEIPT.json), [42/42 physical-bank cases](quality/evidence/chart-bank-review-1/RECEIPT.json) | BANK/MATRIX regeneration, direct physical-bank constraints, byte/exit agreement and forged-certificate refusals checked. Original-source admission remains separate. |
| Safe application component | [Launcher review](quality/LAUNCHER-REVIEW.json), [15/15 adapter challenges](design/evidence/adapter-challenge-2/ADAPTER-CHALLENGE-RECEIPT.json) | Witness, exclusion, budget UNKNOWN, binary-pin refusal, forged-certificate refusal and output preservation checked. |
| Natural-cell application | [Six launcher cases plus output preservation](quality/evidence/native-launcher-review-1/RECEIPT.json), [18/18 independent adapter challenges](design/evidence/chart-adapter-challenge-2/ADAPTER-CHALLENGE-RECEIPT.json) | Original-ID chart operation and separate certificate checks run through the practical launcher; admission/statistical gates remain false. |
| Application source identity | [Derivative pins](APPLICATION-DERIVATIVE-PINS.json), [verifier](verify_derivative.py) | Current launcher/runtime bytes are recorded separately from the historical manifest; one intervening navigation update is explicit. Byte identity does not establish scientific admission. |

## Current implementation

The [RC1 contract](design/CONTRACT.md) gives exact rational AFFINE feasibility,
deterministic witnesses and original-row contradiction certificates. COUNT
computes conditional arithmetic and always preserves the missing-provider gate.
The [additive CHART contract](design/CHART-CONTRACT.md) connects original graph,
calendar, exposure and hybrid records to one shared bank of affine rows. Its
source-admission gate remains explicit. See [Rust build instructions](rust/README.md)
and the [application command](../../applications/practical-solver/README.md).

Constructive witness, typed source-bank decoding and certificate refinements
live in [reuse/sources](reuse/sources). Their individual compiler receipts, rather
than a file's presence, establish formal acceptance. The Lean integration role
owns compiler scheduling and proof receipts.

The full public union is being compiled from pinned Mathlib sources because the
official HTTPS cache is unavailable in this environment. Ready project modules
are now being checked while external prerequisites continue building. The full
1,340-module aggregate and audit remain pending. Check current logs and receipts
before restarting any build.

The next broader executable operation is the inherited full-joint genealogy
polynomial compiler. Its [five independent symbolic baseline checks](quality/evidence/law-analytic-baseline-1/RECEIPT.json)
pass for ordinary, COMMON, INDEPENDENT and forced-parent cases. The native LAW
port and Lean mirror are in progress; these Python checks are not native parity.

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
