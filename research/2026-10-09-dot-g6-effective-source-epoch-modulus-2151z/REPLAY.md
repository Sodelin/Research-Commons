# Replay

Use official Lean 4.33.1 and the exact mathlib revision in SOURCE-PINS.json. Reuse the authenticated baseline181 and the unchanged published G7SinglePopulationPolynomialKernel provider. Put this packet first on LEAN_PATH; no other new G6 or G7 continuation module is required.

Run sequentially with a 180-second per-module cap:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o ActualKernelCoefficientBound.olean ActualKernelCoefficientBound.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o ActualPolynomialEpochModulus.olean ActualPolynomialEpochModulus.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6EffectiveModulusAudit.olean G6EffectiveModulusAudit.lean
```

The final command emits the complete two-module AUDIT-OWNED.json. ATTEMPT-HISTORY.json retains all seven attempts with source snapshots, portable logs and original receipt/log hashes. Source checks3/6 and audit7 are the final successes;1/2/4/5 failed. Object hashes identify the recorded build context, not binary portability across arbitrary paths. No independent clean public-checkout replay or new unified Lake target membership is claimed.
