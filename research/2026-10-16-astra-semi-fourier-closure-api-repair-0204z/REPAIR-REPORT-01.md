# Fourier intensity subgroup-closure API repair r1

Evidence label: **STATIC_API_FINDING_NOT_AN_ACTUAL_FOURIER_COMPILER_DIAGNOSTIC**.

16 October 2026, 02:04 UTC. Lean source owner; isolated source candidate, uncompiled and awaiting focused independent review. No compiler, checker or acquisition was run for this packet.

## Exact change

Against frozen source commit `55eecf2a337a43c0a9b958592dde1e50a6bf405d`, file `source/Semi/Diffraction/FourierIntensity.lean` (5,932 bytes; SHA256 `6bc1f4c653a37336c03c38b4db0fd02b86276c25131a273817496255fb12503c`), replace only original line 134:

```diff
-    apply Subgroup.closure_le.mpr
+    apply (Subgroup.closure_le (K := intensityStabilizer N)).mpr
```

Successor `FourierIntensity.lean`: 5963 bytes; SHA256 `ca54ff7c457432db4bf5512908a90feb21b2c4a479553814fb7a9cb2e7b93c4e`. Patch `FourierIntensity.patch`: 496 bytes; SHA256 `7133b17aaca72b5c2b5b2afe67a73181f5f8c5394864ccfc135cbf8038c86eec`.

The existing local goal is `symmetries N ≤ intensityStabilizer N`. The named `K` selects that same subgroup; the existing generator-membership argument and all subsequent proof text remain unchanged. At pinned Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Algebra/Group/Subgroup/Lattice.lean:355` states `closure_le : closure k ≤ K ↔ k ⊆ K`; line 384 itself applies `closure_le (K := K) |>.mpr`. The exact API file is 28,505 bytes, SHA256 `feb594cb9ff4164130e0e05f21495cea51fcc74776e833f75116429549a4beab`, Git blob `39795007baa68c35eac387377724294f9d37ec05`, matched to the pinned Git tree. This supports the API spelling; it is not elaboration evidence for the successor.

## Preservation and verification

The successor has exactly one changed line and one unified-diff hunk. Reversing the replacement recovers the complete frozen source byte for byte; independently replaying the unified patch also produces the complete successor. Every other byte, including declarations, theorem statements, assumptions, definitions, imports, options and inherited attribution, is unchanged. Original source and all active/used execution leaves were not modified.

The selected composition retains the finite-orbit repair at `8f8eaa60faae0a7398e6d561d0fc23dad08529a5` (6,286 bytes; SHA256 `538a0c3fdbb82e93c51f70f7d26e590ca309797da72ffc05938b7e0b84676cf9`) and the cyclic-grid repair at `2d8f5b6444e57f60eae6317d47cbfc30a7fd6057` (3,447 bytes; SHA256 `55daccdefae9bee719462c83fb56b4d53f072da56bd9257a6f70cadf4e0ab4b1`). Both actual held files were rehashed unchanged. This packet is separate from, and preserves, those immutable contributions.

## Evidence boundary and next action

The supplied actual compilation stopped in CyclicGrid before FourierIntensity was attempted. This occurrence was found by source inspection, not a Fourier compiler diagnostic. The earlier CyclicGrid source PASS does not automatically review or compile this new candidate. No endpoint, axiom audit, whole-package success, physical-model adequacy, or G3/G4 closure is claimed.

Next action: focused independent review of this exact one-line candidate. Any subsequent check belongs to the existing sole desktop workflow under a fresh selected finite record, preserving consumed records and failed evidence. This publication itself grants no execution admission and makes no canonical package overwrite. Existing theorem authorship and Mathlib attribution are retained; the contribution is an API application repair, not new mathematics.
