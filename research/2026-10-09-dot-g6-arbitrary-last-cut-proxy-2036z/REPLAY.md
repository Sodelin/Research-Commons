# Replay

Use official Lean4.33.1 commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and mathlib0df444a360eaa60ab8c11dca51a86af692955474. Add the authenticated181-module baseline and the two frozen prior proxy packets linked in README to LEAN_PATH, with this packet first. Compile sequentially:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o NaturalAncestralCutExtension.olean NaturalAncestralCutExtension.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o ArbitraryCutSharedBankProxy.olean ArbitraryCutSharedBankProxy.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6NaturalCutAudit.olean G6NaturalCutAudit.lean
```

The last command writes AUDIT-OWNED.json. The recorded audit covers both mathematical modules, including all owned declarations. Historical successful partial checks, failed elaborations and deterministic heartbeat timeouts are retained in ATTEMPT-HISTORY.json; failure recovery rows never confer acceptance. Compiler limits were not raised. Historical unchecked headers in inherited providers do not override their later exact build receipts, and imported objects are not claimed as fresh rebuilds here.
