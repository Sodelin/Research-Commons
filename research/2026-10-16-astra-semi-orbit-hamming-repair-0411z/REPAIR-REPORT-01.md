# Orbit-Hamming elaboration repair r1

15 October 2026, 21:11 PDT (16 October 2026, 04:11 UTC). Lean source owner. **SOURCE CANDIDATE, UNCOMPILED; focused independent review pending.**

This isolated candidate responds only to the two supplied actual OrbitHamming diagnostics. It preserves the prior package and repair sources. No active/used execution leaf is edited and no compiler, checker or acquisition is run.

## Exact source and two changes

Baseline: package commit `55eecf2a337a43c0a9b958592dde1e50a6bf405d`, `source/Semi/Diffraction/OrbitHamming.lean`, 3,786 bytes / SHA256 `bfd62076d57228b45bb0182bb6bb0de7f14f2d2c5407f8ad4d5e613472ad5ca4`. Successor: 3815 bytes / SHA256 `bb23412a66ec9e5abb3e07666242954054c40c1cb5aa7fdd6bd59cc0bf318b08`. Unified patch: 852 bytes / SHA256 `cb2db055b1f63c59b0291f6e6a33f613df10ce0578b8748fe09ed8e9615583aa`; 1 hunk(s), exactly two changed lines (28 and 33).

1. Mark `sourceOrbit` as `noncomputable def`. Its type and defining expression `Quotient.mk _ x` remain byte-identical. The quotient setoid is instantiated through the existing `orbitGeometry`, which uses the noncomputable finite symmetry-group instance. The actual compiler rejected executable generation for that dependency. The annotation acknowledges the existing dependency; it adds no axiom, hypothesis or executable implementation and changes no mathematical value.
2. Add `orbitGeometry` to the existing `simpa` list in `orbitDistance_le_size`. The required bound is stated using `(orbitGeometry N).distance`; its record definition sets `distance := hammingDist`. Explicitly unfolding that projection lets the unchanged `hammingDist_le_card_fintype` and `ZMod.card` prove the required bound. The transitivity argument and theorem statement are unchanged.

## Source checks and preservation

The exact pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474` source `Mathlib/InformationTheory/Hamming.lean:113` states `hammingDist_le_card_fintype : hammingDist x y ≤ Fintype.card ι`. Its held file is 14458 bytes / SHA256 `7d247632b790bfc237d79d3c040fb7f21d9cff00d190a67e120ccb73056460a6`, Git blob `800095468b359fb295427c716ac68c5465f06073`, matched to the pinned Git tree. The current held FiniteOrbit source supplies `orbitDistance_le_distance`; the held CyclicGrid source explicitly declares `symmetryFintype` noncomputable. These facts were read, not compiled in this repair.

Inverse replacement recovers every original byte; independent unified-patch replay produces the complete successor. Only the noncomputability annotation and the single proof simplification list differ. All theorem statements, assumptions, imports, options, definition types and defining values, mathematical scope and inherited attribution are preserved. No `sorry`, `admit`, `axiom` or `unsafe` token occurs in the successor. Public metadata was screened for private operational identifiers and paths.

The manifest retains and rehashes unchanged FiniteOrbit `538a0c3f`, CyclicGrid `55daccde`, FourierIntensity `ac9b07a5` and FiniteDecision `32b93d25` source selections with their complete pins. No new source-review or runtime result is inferred for any of them.

## Evidence stage and remaining gap

Supplied actual diagnostics: complete stdout 674 bytes / SHA256 `ddebf0b54dbc22c5bc5451a55c14fa4c8f302ec8688ca406e813a6643a2fa372`; command receipt 2,593 bytes / SHA256 `743c2d80f4899317c92e987d8b0e20cd72e1997723570e5e3646d0f3e5a86a99`; compiler exit 1, no runner stop/error, full EOF and confirmed exit identity/group absence. These are relayed reviewed evidence, not a new personal raw-log read. The existing batch is still in progress/custody pending at the supplied checkpoint; this packet makes no whole-package or semantic acceptance claim.

Next action: focused independent source review of this exact two-line successor. Any subsequent actual elaboration/type/axiom check and final custody belongs to a fresh selected finite desktop record after current mandatory custody. This publication does not authorize a run or replay a consumed record. No broader G3/G4, physical-model, statistical-channel or canonical-adoption conclusion follows.
