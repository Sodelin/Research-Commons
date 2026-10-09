# Replay

Use official Lean 4.33.1 and mathlib at the exact SOURCE-PINS.json revision. Reuse the authenticated 181-module baseline and the listed public predecessor modules. Put this packet first on LEAN_PATH. Avoid a partial UnifiedLean namespace directory shadowing the complete baseline. All custom dependencies are those of the listed predecessor modules; the G1 joint-provider overlay is not required.

Run in order with a 180-second per-module cap:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o GeneratedNaturalChronology.olean GeneratedNaturalChronology.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o RationalNaturalGrid.olean RationalNaturalGrid.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o GeneratedRationalSourceWitness.olean GeneratedRationalSourceWitness.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6GeneratedChartAudit.olean G6GeneratedChartAudit.lean
```

The last command emits the full three-module AUDIT-OWNED.json. Recorded object hashes identify the original build, not portability across paths/runtime variants. ATTEMPT-HISTORY.json retains all seven attempts, source snapshots, original receipt/log hashes and path-sanitized logs. Attempts 1 and 5 failed; 2/3/6 are final source checks, 7 is the final audit, and 4 is an earlier two-module audit. No independent clean replay of this public packet is claimed.
