# ProofBridge declarative proof-job ingress pilot

This Python/Linux gate answers **“Does this registered source/statement have an acceptable existing evidence chain?”** It does not answer **“Did the check just run?”** or execute any program. An index hit is never promoted to proof evidence automatically.

## Contract

- The operator, not the incoming request, chooses local registry/ledger paths and supplies both SHA-256 anchors from independently trusted configuration. Obtain registry source commits/hash mappings and ledger attestations through the trusted backend. **Do not generate trusted anchors by hashing user uploads.**
- The request carries only a registered job ID, full lowercase 40-hex Git commit, file-content SHA-256, exact-goal identity SHA-256, and receipt references. No commands, code, paths, source URLs, remote fetch, or plugin dispatch are accepted.
- Each registry row pins the stage plan, expected result, checker digest, and checker-input digest. `exact`, `smt`, `lean` are fixed stage labels, not command names. The lane can be Lean-only but Lean is mandatory; the registry can require stages before it. A received `sat` does not satisfy `unsat`; `unknown` and failed checks cannot advance the chain.
- The trusted ledger is registry-bound. Reuse is exact across job, source commit and digest, statement digest, stage, checker digest, and checker-input digest. Receipt references are SHA-256 over canonical JSON (UTF-8, sorted keys, compact separators); a receipt only counts if present in the independently anchored ledger. Output digest is reported from the ledger, not recomputed from an output file.
- Status is `trusted_kernel_receipt_matched`, not `verified_now`, and always has `fresh_checker_execution: false`. `not_certified` means a valid job lacks a completing chain; `rejected` (exit 2) means malformed or unauthorized evidence. No theorem publication follows from this output.

The checker-input digest must include the effective dependency/toolchain manifest; the ledger producer must verify the commit→source binding, statement and axiom policy, checker execution/output, and freshness/revocation policy before anchoring. This gate does not implement these producer steps, Git/Lean/SMT adapters, private/public scope clearance, concurrency, or deployment. A proof certificate for a restricted or conditional statement warrants only that exact statement. The pilot's tests use synthetic receipts, not real theorem checks.

## Replay

```sh
PYTHONDONTWRITEBYTECODE=1 python -m unittest -v
python proof_job_ingress.py --registry REG.json --registry-sha256 TRUSTED_REG_HASH \
  --ledger LEDGER.json --ledger-sha256 TRUSTED_LEDGER_HASH --job JOB.json --source SOURCE.lean
```
