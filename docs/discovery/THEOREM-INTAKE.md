# Theorem intake CLI

[Proof sources, batch intake and Lean inventory](PROOF-SOURCE-MAP.md) is the entry point for existing catalogs, formal evidence and the current import workflow.

From a Commons checkout containing the pinned Git objects:

```sh
python docs/discovery/tools/theorem-intake.py --summary
python docs/discovery/tools/theorem-intake.py --query "Twin primes"
python docs/discovery/tools/theorem-intake.py --id handoff:commons.goldbach.integer_budget_187.v1
```

This joins the canonical claim board, the historical obligation register and incorporation catalog, selected exact hand-note sections, and explicitly registered ProofBridge handoffs. It is an additive JSONL command in Discovery, separate from body-text search. IDs are namespaced by source kind; two rows may describe the same mathematics. Source counts are not theorem counts. It preserves authored math/formal statuses, evidence, dependency references, and Git commit and blob identities. Nothing infers proof status from a note title or from a Lean link. Filter with `--kind`, `--math-status`, `--formal-status`, `--status`, or `--query`. `needs_statement_review` means there is no checker input in this registry; it does not erase previously checked or accepted work.

New exact typed records at a selected Git revision under `research/proofbridge-incoming/<name>.json` enter the same intake by using `--include-queue-at <revision>`. The input format is `{"schema":"commons.proofbridge.certificate_records.v1","records":[{"id":"stable-id","certificate":<ProofBridge linear certificate>}]}`. `--emit-certificate --id …` exports one typed job; a recorded handoff can be replayed by rehashing its independently pinned certificate. An unsupported prose or open row stays in discovery, not in the verification queue.

```sh
python docs/discovery/tools/theorem-intake.py --include-queue-at HEAD --export-ready out
python research/2026-11-25-proofbridge-linear/linear.py batch out/inputs > checks.jsonl
python docs/discovery/tools/theorem-intake.py --include-queue-at HEAD --export-index out/index.json --checker-results checks.jsonl
```

Freeze the queue revision for reliable replay; use a fresh output directory and a trusted checker path. A matching result attaches as supplied replay evidence, not as a new run or a change to the canonical theorem board. Keep unsupported or open records in the output. No free-prose-to-Lean translation, general Mathlib/SMT bridge, or full-history inventory is claimed.

Validation on Windows: exact source blobs for all six default inputs matched actual committed upstream blobs before staging in a scratch Git repository with local commit IDs. The CLI read 243 source records: 118 claim-board rows, 65 obligations, 51 incorporation rows, eight hand-note sections, and one checked handoff. A separately committed typed fixture was discovered, exported and checked in Lean 4.33.1; its result joined back to the exact source row, while changed blob and result hashes were refused. This did not refresh the separate full-text cache or port the hand-note backlog.
