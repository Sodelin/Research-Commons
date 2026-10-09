# Replay and scope

Use official Lean 4.33.1 with mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. Add the unchanged 181-module baseline object directory, the pinned natural inverse-rate provider, and the proved natural-cell decision modules to LEAN_PATH, with this packet first. Exact public predecessor links are in README.md.

Run sequentially:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o RationalNaturalCellWitness.olean RationalNaturalCellWitness.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6RationalWitnessAudit.olean G6RationalWitnessAudit.lean
```

The second command writes AUDIT-OWNED.json. Object hashes in BUILD-RECEIPTS.json are evidence of the recorded build, not a portability promise across arbitrary paths/environments. Historical failures are retained with source snapshots and portable logs. The inherited baseline's historical unchecked file headers are superseded only by its separately recorded successful replay. This packet audits the one new mathematical module, not all inherited modules.
