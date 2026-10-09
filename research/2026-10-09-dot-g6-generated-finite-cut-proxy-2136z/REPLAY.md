# Replay

Use official Lean 4.33.1 and the pinned mathlib revision in SOURCE-PINS.json. Add the authenticated 181-module baseline and the listed unchanged public predecessor modules to LEAN_PATH, with this packet first. No G5 or G7 continuation module is a build dependency.

Run sequentially under a 180-second per-module cap:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o FiniteCutSourceWord.olean FiniteCutSourceWord.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o GeneratedCompleteBinProxy.olean GeneratedCompleteBinProxy.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6FiniteCutWordAudit.olean G6FiniteCutWordAudit.lean
```

The final command emits the full two-module AUDIT-OWNED.json. ATTEMPT-HISTORY.json retains all five attempts, original receipt/log hashes, source snapshots and portable logs. Attempts 1 and 2 failed; 3 and 4 are successful final source checks, 5 is the final audit. Recorded object hashes identify the original runtime/path build and do not promise binary portability. No independent clean public-checkout replay or new unified Lake membership is claimed.
