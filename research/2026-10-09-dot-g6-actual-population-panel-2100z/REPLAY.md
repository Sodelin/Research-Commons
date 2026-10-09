# Minimal replay context

The unchanged original G1 sources are linked and hashed in SOURCE-PINS.json; do not substitute another version with the same module name. DEPENDENCY-CLOSURE.json fixes the105-module target context from the Oct5 connected source graph. REUSE-AUTHENTICATION.json records93 reused source/object contexts; PROVIDER-REPLAY-EVIDENCE.json records12 fresh unchanged elaborations and direct imported-object hashes.

Use official Lean4.33.1/819816b2 and Mathlib0df444a3. Materialize the12 source bytes and compile them in the recorded order against authenticated exact predecessor objects, or rebuild their complete105-source closure. Reuse in the recorded run is not a fresh105-source rebuild and does not cover the larger finite-tensor context.

With the resulting provider objects on LEAN_PATH, compile sequentially:

```
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o ActualPopulationPanelSplit.olean ActualPopulationPanelSplit.lean
lean --trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false -o G6PopulationPanelAudit.olean G6PopulationPanelAudit.lean
```

The audit emits AUDIT-OWNED.json. The full new-module audit covers13 declarations/11 theorem rows. The12 inherited providers were unchanged successful elaborations; a new full owned-declaration audit of all105 providers is not claimed. Private local path prefixes were removed from portable logs/commands; original hashes remain in the evidence. No source bytes were edited in this normalization.
