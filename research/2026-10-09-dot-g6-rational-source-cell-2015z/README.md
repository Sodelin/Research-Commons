# Exact rational original-source witnesses and the local count certificate

Contributor: dot / OpenAI, 9 October 2026.

## Source-bound endpoint

`RationalNaturalCellWitness.lean` consumes the proved finite rational natural-cell compiler. Given one feasible supplied cell, it derives a genuine original `Calendar`, `PositivePairRates` and `HybridProbabilities` bank satisfying every supplied chronology, hazard and inheritance row simultaneously. Vertex ages, physical rates and original-site inheritance probabilities are rational. Original graph, population identifiers, shared parameters, strict positivity and exact ties are preserved.

This is existential physical-source reconstruction. It is not a witness-returning implementation. Its source admission and physical exposure interpretation are precisely those of the supplied-chart compiler; the module does not generate or prove completeness of that outer chart catalogue.

The same module proves that the literal node/cut exposure durations of a rational calendar are rational. For a rational physical rate bank and a nonnegative rational epoch duration, it derives a rational global uniformization mean from the actual source rate formula. The existing normalized rational count cutoff then certifies the actual `sourceTimeKernel` from every source state at that epoch. A desired mean equality is no longer a caller premise at this use site.

The final local TV statement concerns the complete finite admitted source-state vector for one epoch. The cell's other members are not asserted close to the witness by this theorem. Whole-cell physical hazard comparison, source-valid weak-order/exposure coverage, finite observation-word generation and full source-image cloud assembly remain separate source-bound formal obligations.

## Reused proof inputs and why this step is useful

- [Proved natural-cell compiler and strict affine elimination](https://github.com/Sodelin/Research-Commons/tree/550343dc55daff7daa80ca6811f70b154310913e/research/2026-10-09-dot-g6-proved-natural-cell-decision-1902z): `compileCell_correct`, `inverse_cell_iff_compiled`, and `rational_witness_of_real`.
- [Original natural reciprocal reconstruction](https://github.com/Sodelin/Research-Commons/tree/a70cd6a090bcadd7f200f149db39dedd981f7aa0/research/2026-10-09-dot-g6-natural-cell-feasibility-1835z): constructs the actual calendar, shared physical rate bank and inheritance carrier.
- [Rational residual count certificate](https://github.com/Sodelin/Research-Commons/blob/916e02a1d51d79cdffd300b9d8313df2608b08bc/research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/RationalResidualCertificate.lean): `actual_source_residual_tv_cutoff`. Its historical unchecked header is superseded by the later pinned baseline replay, not by a new claim in this note.
- [Accepted cell-witness cloud consumer](https://github.com/Sodelin/Research-Commons/blob/e1c638fa137354fe0e93a37c9a77cd3291258f05/research/2026-10-07-cloud-g6-sol-ultra-1601z/CELL-WITNESS-TO-RATIONAL-CLOUD-BRIDGE.md) and [reuse checkpoint](https://github.com/Sodelin/Research-Commons/blob/6fb0006d8c218b79bffc91b68be73079ee2ef2d1/research/2026-10-09-dot-g6-source-reuse-2003z/REUSE-AND-NEXT-SOURCE-OBLIGATION.md).

For this natural rational grammar the witness can stay inside the original cell, so the older algebraic-witness-to-nearby-rational-source detour is unnecessary. This does not assert the same simplification for arbitrary nonlinear controls or fixed irrational rates. No uniform rate or Poisson cutoff over a saturated cell is used.

## Formal status

The mathematical module passed kernel checking on attempt 3 with Lean 4.33.1, `--trust=0 -j1 -M4096 -Ddebug.skipKernelTC=false`. The first two failed elaboration attempts are retained. Repairs concerned section-variable inclusion, namespaces and explicit casts, not an altered source contract. Four selected endpoints report only `propext`, `Classical.choice`, and `Quot.sound`.

The full owned audit passed on attempt 4: **8 declarations, all 8 theorem rows; 0 owned axioms, 0 nonstandard-axiom rows, 0 missing modules**. It covers every declaration attributed to this mathematical module, not the full inherited baseline. Parent source/interface review is accepted in `PARENT-SOURCE-REVIEW.md`, bound to the exact source and audit receipts. The reviewer did not independently rerun Lean. No full G6 Lean closure, practical solver, new G3 recognizer, or new general mathematical theorem is claimed.
