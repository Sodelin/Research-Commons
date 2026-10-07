# Main preservation check

Codex coordinator for Nolan. Observed 2026-10-07T14:10:47Z. User asked whether everything was on main; interpreted in the existing save/main context.

Snapshot inspected: f562813098db842c9dc47896d96b2e92d57180e2. Only main was listed; no open pull requests. GitHub comparison verifies earlier Codex saved-work commit 00668a531655f9be2d7ae91000b4dd11a3652387 is an ancestor of this main (nine newer commits, zero behind). Thus prior checked overnight/prompts/coordination/build history remains reachable.

All five local engineering files were compared to main by exact Git blob hashes: workflow, runtime script, runtime smoke, G5 verification script, corrected G5 source. All five match. Successful G5 proof receipt and complete retrieved job log are present. This is a preservation check; it does not rerun proofs or change their scope.

G5's current status actually acknowledges the revised hand-proof division. Its 13:24:56Z checkpoint reports no scientific source left solely local and points to the preserved packet at 4cdaa5e and hand-proof ACK at f13bb32. That is a dated report, not a claim of current live activity.

G6's mutable status is older than its actual publications. Current main contains COUNT-SOURCE and FOREST-PAIR hand proofs, finite_source_prefix.py, test_finite_source_prefix.py, forest_pair_controls.py, evidence/reference-tests.json and evidence/reference-tests.stdout.log. The 1143-check report's source/test SHA256s were compared to saved code by the read-only audit and match. The 13:30 immutable count handoff was read; it explicitly delivers the packet rather than merely planning it. Publication and finite checks do not establish whole G6 or new Lean acceptance.

One narrower unresolved preservation item: FOREST-PAIR cites 770 executed exact-rational checks, but this packet's evidence directory lists only the 1143 reference report/log at the inspected snapshot. Forest control source and the written run summary are saved; the original 770-run raw receipt/output was not located. A directed request asks G6 to preserve or link that original output and refresh the stale status. No unsaved work in another chat can be ruled out by repository inspection alone.

Next action: confirm G6's original forest-run receipt and status link, then use the saved count/source packet for the next Lean implementation. G7 remains queued; no slot changes or build were made by this audit.

11. Process integrity: current ref/history, actual file identities and source-linked receipts checked; stale-status inference corrected using newer commits.
12. Robustness: high confidence for inspected saved bytes/history; no blanket guarantee about invisible local drafts or the unlocated original forest-run output.
