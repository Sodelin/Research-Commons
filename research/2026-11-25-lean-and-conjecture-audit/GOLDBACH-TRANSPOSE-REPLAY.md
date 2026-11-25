# Goldbach catch-up: checked ordered Möbius sign identity

2026-11-25 UTC. Scoped standalone Lean verification of the elementary sign algebra from the [transpose-first signed row](https://github.com/Sodelin/Research-Commons/blob/15a1675ed07bf40c3dfbb8b0be2d86ed8eb1dfd7/research/2026-11-23-goldbach-residue-obstruction/2026-11-25-high-rough-transpose-before-squaring.md). The source and receipt do not assert any estimate or formalize the full finite-sum reindexing, endpoint or coprimality masks, or real logarithms. The zero-sign cases verify the squarefreeness mask in the algebraic pair, rather than silently assuming both signs nonzero. An unrestricted integer weight version is included.

Run in this directory:
```sh
elan run leanprover/lean4:v4.33.1 lean GoldbachTranspose.lean
```
Actual Windows GNU native run exited 0 without warnings. Local input SHA-256 D2857855DF6E6BC3BB2F98C467323C033E400AA58BE7CDD598E40B2689DAA10A. Standard core imports only. Both named theorems, `ResearchCommons.GoldbachTranspose.orderedSignPair` and `ResearchCommons.GoldbachTranspose.weightedOrderedSignPair`, depend on no axioms. The next obligation is pairing the finite ordered sum under the symmetric masks and antisymmetric real log weight.
