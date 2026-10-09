# Independent scope review: source-typed reciprocal-rate theorem

Reviewer: dot, G3 recognition lane. 9 October 2026, 18:33 UTC.

**Verdict: SCOPED STATEMENT/SOURCE ACCEPT.** This is a review of the substitution gate, not formal elimination completeness or full G6 assembly.

## Frozen subject and relation to the hand review

- `drafts/G6NaturalCellInverseRates.lean`, SHA256 `bd35c3f3f47ada67cceb9887059a3a9ed8662129bcab4dbe5d5ade07a377de5f`.
- Hand manuscript: `INVERSE-RATE-NATURAL-CELL-FEASIBILITY.md`, SHA256 `66c79c327c1792b7e7680d621739e7cfadd950aaf904e1e951aeb52049dedf88`.
- Earlier independent hand/source and Python review: `INDEPENDENT-RECOGNITION-INVERSE-RATE-REVIEW.md`, SHA256 `7bc39c260c5e22e1978039c44d17423099eef23b3a813d3bbd1145595752e80c`.

I read the complete final Lean module and inspected the inherited definitions of `Calendar`, `PositivePairRates`, `pairRate`, and `HybridProbabilities` in the existing baseline sources.

## What the statement establishes

`originalCellFeasible` existentially quantifies one actual inherited calendar, one positive edge/ancestral rate bank, and one interior inheritance bank on the unchanged supplied `RootedBinary` graph. Leaf ages are zero. All supplied chronology, coin-cell and hazard-cell constraints hold simultaneously on that bank.

`inverseCellFeasible` retains the same age and inheritance variables and introduces one positive inverse-rate coordinate per original edge plus one shared `none` ancestral coordinate. Original edge durations remain strict. Each hazard row uses the same population coordinate wherever that physical population recurs.

`original_cell_iff_inverse` proves the exact equivalence by reciprocal substitution in both directions, reconstructing the genuine inherited carriers. There is no hypothesis supplying an observation law, feasibility decision, desired witness, source-image equality, or approximation. The proof does not independently fit rows. Strict and weak interval endpoints are distinguished; absent bounds remain absent; equal lower/upper weak endpoints express singleton cells. Chronology allows exact ties. Age endpoints are syntactically original node ages or rational constants, so no nonlinear age expression enters this gate.

The inherited carriers agree with the hand theorem: `Calendar` has strict original edge-age inequalities; positive rates are freely variable real constants for original populations; inheritance values lie strictly between zero and one. The module does not impose or prove extra graph-admission properties beyond its supplied graph carrier.

## Required limits

1. A supplied exposure is not certified to lie within its named population, nor is its duration separately proved nonnegative. Actual legal exposures, complete weak-order charts and their exhaustive enumeration must be supplied by the source compiler. The reciprocal equivalence remains mathematically valid even for malformed exposure rows, so compilation cannot be inferred from the equivalence alone.
2. The index types `I` and `C` have no finiteness assumptions. This harmlessly strengthens the algebraic equivalence to arbitrary families. Calling the system a **finite** rational-affine feasibility problem requires finite supplied row and chronology index types, as in the natural G6 application.
3. The module proves neither rational witness existence nor an effective decision procedure, Fourier–Motzkin correctness, graph/chronology enumeration, probability compilation, error bounds, finite nets, or full G6. Those remain distinct implementation/formalization obligations. It does not address G3 exact terminal observation equalities or unrestricted source size.
4. Optional rate ties, rate bounds, and broader nonlinear controls are not represented here. The claim uses the original freely variable natural rate bank. Shared use of one physical rate is represented exactly.

## Evidence inspected, without independent Lean execution

I verified the final source hash and inspected `build-evidence/natural-cell-2.json`, its stdout/stderr, and the generated object hash. The receipt records exit code zero with `--trust=0` and `-Ddebug.skipKernelTC=false`; the source hash matches the reviewed module. The object SHA256 is `7c6555966cb1c1fdc2cb379732838deca8220107c0e41fa96b8035d996338f3a`, matching the receipt. The stdout lists all eight named theorem reports with only `propext`, `Classical.choice`, and `Quot.sound`; the visible warnings concern unused section variables. Stderr is empty.

This is inspection of the author's matching execution evidence, not a reviewer rerun of Lean. No new execution or full-baseline certification is claimed by this addendum.
