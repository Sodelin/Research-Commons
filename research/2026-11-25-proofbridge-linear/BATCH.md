# Desktop batch: manifest-bound replay

This is a supplement to [ProofBridge](README.md); it does not change the proof predicates or discover new proofs. It pins the linear checker source, explicit flat input names, exact certificate hashes, and a caller-supplied SHA-256 of the whole manifest. Keep that hash outside the mutable input folder, e.g. in a pinned Git commit. A hash is not a signature or a verdict on the assumptions.

```sh
python manifest_runner.py make . goldbach-budget.json bad-budget.json combine.json > plan.json
# Read then independently record the SHA-256 of plan.json.
python manifest_runner.py run . plan.json MANIFEST_SHA256 run-1 --jobs 2 --wall 120
python manifest_runner.py run . plan.json MANIFEST_SHA256 run-2 --start 2
```

Use separate, fresh output directories next to the immutable input directory. Keep the project/interpreter/toolchain and output directories in a trusted workspace, not a sandbox for hostile local peers. Each attempted entry writes its own JSON receipt via flush, fsync, and same-directory replacement. Verification always runs again for a selected entry; the runner does not trust old receipts to skip work. Keep the earlier directory and set `--start` to the first unattempted index, or intentionally rerun a failed index. The summary's `complete` means the traversal reached the end, not that earlier runs passed. Inspect per-entry statuses. Exit codes: 0 no attempted failures in this run; 1 failed/timed out entry; 2 invalid setup or I/O error. No external solver invoked.

## Windows validation

Python 3.14.7 and Lean 4.33.1. Manifest SHA-256 `745e0230acdb63f6cbc1ceb2008a68f9e818a7aea25b67a22aa300200cb4dda0`.
- First run stopped after two entries: changed-bound witness rejected, independent linear example freshly kernel-checked.
- Second run resumed at index 2: Goldbach integer budget implication freshly kernel-checked under supplied premises.
- Third run used the same manifest after changing one input byte sequence: input hash mismatch, no proof check recorded.
- Wrong manifest hash refused before creating an output directory. Four durable receipts across the three completed traversals.
- Accepted proofs retained exactly `propext` and `Quot.sound`. No aggregate proof claim or external SMT evidence.

Next capacity test: select 20 representative supported and unsupported records from the proof register, keep their original statement pins and separate authoring time, check time, and unsupported reasons. This is not a claim that 20 records or a four-hour corpus pass have already been verified.

## Direct cloud Lean and Discovery handoff

Add `--lean /path/to/pinned/lean --discovery-jsonl` to the same `run` command. The runner checks the direct compiler pin before creating the output directory. The existing per-entry receipts remain the durable master; `out/discovery-results.jsonl` is a separate projection for `theorem-intake.py --checker-results` with the matching export index. Resume in a fresh run directory. A checker rejection or timeout does not become a theorem failure or a verification. If a crash interrupts the projection, retain authoritative per-entry receipts and rerun with the same immutable manifest instead of trusting a partial tail. [Cloud smoke receipt](cloud-batch.receipt.json) records a successful conditional proof and a rejected input rejoining their exact rows. This is not an automatic build-on-push service.

Each projected row uses `commons.proofbridge.discovery_result.v1` and carries the certificate and checker SHA-256 even for a rejection or timeout. Discovery refuses stale failures at a reused filename and checks reported Lean commit, allowed axioms, variables, premises and conclusion on conditional passes. Regenerate projections created before this format; the per-entry evidence does not change. A matching projection is still a provided receipt, not an independent rerun or cryptographic attestation of the runner.
