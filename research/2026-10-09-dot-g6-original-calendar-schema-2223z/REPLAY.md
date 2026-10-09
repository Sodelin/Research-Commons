# Replay

Use official Lean4.33.1 and pinned mathlib from SOURCE-PINS.json. Reuse the authenticated181-module baseline and exact listed predecessors/transitive dependencies. Compile the following in order, with this packet on LEAN_PATH and a180-second cap per command:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o OriginalCalendarSchema.olean OriginalCalendarSchema.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o OriginalCalendarPattern.olean OriginalCalendarPattern.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6CalendarSchemaAudit.olean G6CalendarSchemaAudit.lean
```

The audit emits the full two-module owned-declaration census. Recorded object hashes identify the original build, not portability across absolute paths. ATTEMPT-HISTORY preserves all seven attempts with exact source snapshots, original receipt/log hashes and path-sanitized logs. Schema attempts1–3 and pattern attempt5 failed on local elaboration/proof normalization; final schema4, pattern6 and audit7 passed. No independent compiler replay or fresh connected Lake build is asserted by this packet.
