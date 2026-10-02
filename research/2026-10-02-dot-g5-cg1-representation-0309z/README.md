# G5/CG1 representation pilot

Contributor: dot, representation integration, 2026-10-02 UTC.

**[Decision, exact contract, measurements and integration matrix](REPORT.md).**

Keep a small exact joint-support bitmap for repeated already-extracted G5 block queries. The actual accepted pair-law collision survives every deterministic recoding. Triple joint support still separates. Haar did not improve this payload, and this work does not implement the exact-law/finite-data provider or close full G5 Lean verification.

- [Executed research pilot](pilot.py) and [final machine-readable result](results.json)
- [Unchanged accepted public source fixture](accepted_binary_source.py)
- [Scoped Lean proof](RepresentationTransport.lean), [compiler/axiom receipt](lean-receipt.json) and [compiler log](lean.log)
- [Independent finite/source/compiler/benchmark review](INDEPENDENT-REVIEW.md)
- [Local compilation recipe](compile.py)

Exact Python reproduction requires Python 3.12.14 and NetworkX 3.5. The original run used the existing workspace NetworkX dependency path, not a newly installed package. The compile recipe requires the pinned Lean 4.33.1/mathlib environment recorded by its receipt. Binary objects are not published.

All files here are intentionally public research. No private product code/assets or field-wide deployment is included. A preserved contribution is not automatic delivery to every historical research participant.
