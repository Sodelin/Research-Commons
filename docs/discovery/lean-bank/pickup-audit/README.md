# Recurrence pickup audit

Local prototype only. Reuse the existing 15-minute wake; do not add a second timer. Each wake picks zero or one eligible proof. Use trusted scheduler UTC event slot ID (not request input or retry wall clock) and a durable state store shared by all workers. SQLite is appropriate for one host with durable storage, not multiple independent scratch stores or a synced Drive folder. Production must check current approved generation and revocation; a once-authenticated digest may be stale.

The policy operator pins queue, catalog, registry and ledger independently. Resolve repository and full commit via trusted Git; verify the allowlisted regular-source path and raw hash. This harness checks bytes, not Git provenance. Bind fully-qualified Lean declaration, exact elaborated type and checker/toolchain/import/axiom policy in the trusted producer. A title, search hit or path does not identify a theorem. Never compute trust anchors from untrusted uploads. The queue binds catalog, ledger and registry snapshots; the catalog must identify both the specific Lean receipt and output hash. Stop on an invalid unconsumed row; fix/quarantine by trusted queue policy.

Pickup reuses existing evidence; fresh execution would need a separate trusted worker with immutable checker configuration and job budget 1. Fresh execution is not exactly once merely because pickup is atomic: heal crash windows with durable claims, expiry and fencing where needed, and idempotent result publication. Keep any publication separate.

First deployment pilot: one real registered theorem and one controlled existing wake, rerun the same scheduled slot and verify no second dispatch; verify catalog resolution and durable receipt; check a later wake is a no-op for that binding. Do not treat synthetic fixtures as meeting this bar.

Replay: PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=../pb-next-jobs python -m unittest -v. Tests use synthetic receipts: no Lean/SMT run, automation, Git access, credentials or publications. Catalog schema here is a narrow receipt adapter, not the whole Discovery index. Deployment must bound byte loads and coordinate stable DB state and the live approved generation.
