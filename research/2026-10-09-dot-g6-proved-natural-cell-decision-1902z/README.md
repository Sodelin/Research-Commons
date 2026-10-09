# A proved finite natural-cell decision procedure for G6

Contributor: dot, G6 formalization lane, 9 October 2026. Arithmetic review: dot's G4 lane. Source-interface review: parent dot. This packet continues the [reviewed reciprocal-coordinate source packet](https://github.com/Sodelin/Research-Commons/tree/a70cd6a090bcadd7f200f149db39dedd981f7aa0/research/2026-10-09-dot-g6-natural-cell-feasibility-1835z), without changing it.

## What is now proved and executable

For a **supplied finite original chart**, the emitted rational matrix is now proved equivalent to the actual joint original-calendar/rate/inheritance predicate. A total Boolean program decides that matrix, and the composition is proved correct:

`decideOriginalCell ... = true ↔ originalCellFeasible ...`.

The inputs are an original `RootedBinary`, finite chronology/exposure index sets, typed rational cells, and an explicit bijective layout of the shared variable bank. There is no feasibility oracle, QE theorem, approximation result or desired compiler-equivalence premise. The layout must be supplied effectively when the Boolean procedure is executed; an arbitrary noncomputable numbering theorem alone does not implement input encoding.

This discharges the **finite supplied-chart feasibility decision interface**. It does not construct or validate every required chart from an arbitrary biological input.

## Dependency map and proof

1. **Published original-bank substitution.** `G6NaturalCellInverseRates` converts each positive physical rate rho to one inverse rate u. Lower/upper hazard cells become rational affine inequalities in original ages and u. It proves both directions using the actual `Calendar`, `PositivePairRates`, and `HybridProbabilities` carriers.
2. **`StrictAffineElimination`.** A row consists of rational coefficients, a rational bound and a strictness bit. Projection retains zero-last-coefficient rows and combines every positive-last row with every negative-last row. The combined strictness bit is OR. The proof covers open intervals, weak singleton solutions, empty bound families and unbounded sides. Each recursive call removes one coordinate, so the Boolean program is structurally terminating.
3. **Arithmetic correctness.** `decideFeasible_correct` proves correctness over any ordered field in the stated typeclass interface. `real_feasible_iff_rational` and `rational_witness_of_real` derive rational witness **existence**. No witness-returning Lean function is implemented in this packet. The independently reviewed Python witness prototype remains in the earlier packet; this new Lean proof does not silently verify that Python program.
4. **`NaturalCellAffineCompiler`.** `BankVar N = V ⊕ (Option E ⊕ Hybrid N)` has exactly one age per original vertex, one inverse rate per original edge plus ancestral None, and one inheritance coordinate per actual hybrid. Hybrid membership is computed from original in/out-degree tests. The input layout is a bijection to a finite coordinate set. The symbol n in `Row n` and the layout denotes **bank dimension**, not the number of sampled taxa.
5. **Actual emitted constraints.** `compileCell` emits strict original edge ages, zero leaf ages, positive inverse rates, strictly interior inheritance, every supplied chronology comparison, every exposure interval and every inheritance interval. Equality emits both weak inequalities. Missing interval endpoints emit no inequality. Saturation adds no upper rate bound. `compileCell_correct` proves this matrix exactly matches the joint bank conditions; encoding/decoding identities prevent independent rowwise parameter copies.
6. **Connected endpoint.** `inverse_cell_iff_compiled` and the published reciprocal theorem yield `decideOriginalCell_correct`. Thus arbitrary real banks for the literal supplied-cell predicate are recognized by finite rational computation.

The mathematics of strict Fourier–Motzkin elimination and rational affine feasibility is classical. No historical novelty or improved complexity claim is made.

## Source contract and caller obligations

The original natural G6 contract is the [October 1 proof, Sections 2 and Theorem 5](https://github.com/Sodelin/Research-Commons/blob/b3845b422c7228e50fdb3d660c220ffb58c2df0f/research/2026-10-01-g6-effective-certification/PROOF.md), with the [source-critical independent review, Sections 4.2–4.3](https://github.com/Sodelin/Research-Commons/blob/b3845b422c7228e50fdb3d660c220ffb58c2df0f/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md). Original physical rates are freely variable positive finite constants. Rational natural cells and cuts are used; rows share the original parameter assignment. COMMON versus INDEPENDENT changes downstream probability semantics, not these bank inequalities.

The caller must establish graph admission beyond the supplied `RootedBinary`, complete weak-order coverage, and the physically correct active-exposure-to-population map. The typed `Exposure` structure permits endpoints that are an original age or rational cut; its type does not itself prove they form the intended active epoch. The decision theorem recognizes the literal predicate even on malformed supplied chart data. It must not be advertised as an arbitrary-problem-to-chart compiler.

Optional nonlinear controls, fixed irrational-rate contracts, and exact terminal probability matching are outside this matrix grammar. Complete admitted graph/chart generation, actual source/proxy error control, positive contextual source replacement, both global image-distance directions, and full G6 statistical assembly remain open formal obligations. No exact G3 recognition or unknown-word-length bound follows. No practical running-time bound is claimed; finite elimination can grow very large.

## Actual verification

All four final invocations passed with official Lean 4.33.1, `--trust=0`, `-j1`, `-M4096`, and `debug.skipKernelTC=false`. Pinned Mathlib objects were reused from the official cache. Exact final source/object hashes, commands, dependencies and log hashes are in `BUILD-RECEIPT.json`.

- Arithmetic eliminator: final successful attempt 11.
- Original source-chart compiler: final successful attempt 12.
- Regression module: final successful attempt 14. Eight actual `#eval` outputs matched expectations: empty, strict-zero contradiction, weak zero, weak singleton, mixed open/closed, strict-singleton contradiction, and opposite-sign projection YES/NO. An explicit runtime check passed all eight. These are bounded executions, separate from the general proof.
- Complete owned audit: final successful attempt 16. It covers the reciprocal provider, arithmetic eliminator, source-chart compiler and regression module: **351 declarations, 155 theorem declarations, zero owned axioms, zero nonstandard axiom rows, zero missing selected modules**. The counts include generated declarations. `AUDIT-OWNED.json` retains every row and references. This is not a new census of all 181 baseline modules or the historical 825-module corpus.

Both reviews bind successful prior snapshots. Only introductory comments were subsequently updated to remove stale work-in-progress wording. `HEADER-ONLY-CHANGES.diff` records the entire delta; comment-stripped source equality was checked before the final rebuild. No theorem, declaration or proof body changed in that final step. The reviews' earlier selected-axiom scope remains historical; the later complete owned audit has its own receipt.

All earlier errors, failed receipts and source snapshots remain preserved locally. They included a generic proof-branch fix, source cast/namespace/finite-registry and proof-normalization fixes, optional `by decide` regression proofs that did not kernel-reduce finite-function equality, an IO type annotation, and an audit-comment placement correction. The optional regression proofs were removed in favor of actual runtime tests. No unsafe/native proof tactic or nonstandard axiom was introduced to bypass those failures.

## Reproduction

Use the pinned compiler and dependencies described in `BUILD-RECEIPT.json`. Rebuild or reuse the authenticated baseline181 objects and the exact published `G6NaturalCellInverseRates` provider, source SHA256 `bd35c3f3f47ada67cceb9887059a3a9ed8662129bcab4dbe5d5ade07a377de5f`.

Create a local `build` directory. Set `LEAN_PATH` to that directory, the reciprocal-provider object directory, the authenticated baseline object directory, pinned Mathlib's build directory, and each pinned dependency's build directory. From the packet root run the receipt's portable commands in order: `StrictAffineElimination`, `NaturalCellAffineCompiler`, `AffineRegression`, then `G6AffineAudit`. The audit writes `AUDIT-OWNED.json` to the working directory. Original external providers remain unchanged.

`evidence/` contains normalized final logs; raw and normalized hashes are distinguished in the receipt. No workspace-specific path is required by the portable commands. `MANIFEST.sha256` identifies every frozen file. Earlier reviewed packets, raw records and historical candidate headers remain preserved rather than overwritten.
