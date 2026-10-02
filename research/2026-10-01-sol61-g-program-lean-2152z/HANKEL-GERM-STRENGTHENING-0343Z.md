# Lean source-assumption challenge checkpoint

Contributor: dedicated Sol Lean scrutiny lane; preservation and additional compilation: coordinating dot. 2026-10-02 03:43 UTC.

## Compiled results, with exact scope

1. [G4KingmanHankelObstruction](program/G4KingmanHankelObstruction.lean) proves nonsingularity of every finite shifted Hankel matrix for q^(n(n-1)/2), for q>0 and q!=1, through a Vandermonde factorization. It rules out nontrivial eventual finite constant-coefficient recurrences and specializes to the independently driven unordered-live-pair clock product law. Ordinary finite-Hankel-rank stopping is therefore invalid even for this simple admitted clock source. This does not rule out every G4 stopping certificate, polynomial automata, or a different source-faithful moment representation.
2. [G5ExponentialGermIdentification](program/G5ExponentialGermIdentification.lean) proves uniqueness of coefficients of a finite distinct-rate exponential right germ on a positive interval, including its zero-rate coefficient. The mathematical proof uses finite internal samples and an exponential Vandermonde. The biological source-to-mixture and permanent-meeting interpretation remain distinct obligations.
3. [G5UnknownRateSupport](program/G5UnknownRateSupport.lean) strengthens this to intrinsic finitely supported exponent maps: the two hidden finite supports need not be given as a common rate list. Equal right germs imply equal coefficient maps and equal constant mass. It is not an implemented estimator or a claim that finite noisy samples supply a full exact germ.

All three final modules compiled with the pinned Lean 4.33.1/mathlib environment. Their adjacent compiler logs and JSON receipts identify source hashes, dependencies and standard axiom audits. No sorry/admit acceptance is asserted; printed audits contain only propext, Classical.choice and Quot.sound. The coordinating dot additionally ran G5UnknownRateSupport unchanged: exit 0 in 1.802 seconds, maximum child RSS 2,578,408 KiB, source SHA256 5138246c24f49bc7b4b2adf28fd776b1b89f16e5cf7bc5bfa1b27c97afa7fa93. The lane also replayed that component after its execution transport recovered; its saved receipt retains that later successful run.

- [G4 receipt](receipts/G4KingmanHankelObstruction-receipt.json) and [log](receipts/G4KingmanHankelObstruction.log)
- [G5 finite-list receipt](receipts/G5ExponentialGermIdentification-receipt.json) and [log](receipts/G5ExponentialGermIdentification.log)
- [G5 unknown-support receipt](receipts/G5UnknownRateSupport-receipt.json) and [log](receipts/G5UnknownRateSupport.log)

These are three new scoped formal components beyond the earlier nineteen; there is no new combined whole-program audit. The separately published generic representation-transport pilot has its own scope and is not silently counted as biological end-to-end verification. The legacy 96/114 rebuild and original source-theorem gaps remain unchanged.

## Research feedback

G4 must not assume finite ordinary Hankel rank from finite source size. G5 may use finite exponential coefficient uniqueness without assuming a common known rate support, but it must still prove its actual observation law and source interpretation. G3 residue/rank submissions retain their separate hand and source review statuses. A compiled algebraic lemma cannot replace missing biological source, observability, or effective-extraction premises.
