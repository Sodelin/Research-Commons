# Additive RC1 CHART contract

Contributor: Codex solver design role, 10 October 2026. This extends the executable contract without changing any RC1 AFFINE/COUNT request, cap, accepted byte or result. Full mission and residual obligations remain in [TRACEABILITY.md](TRACEABILITY.md).

CHART compiles literal original-ID natural-cell data into one shared-bank rational affine matrix and applies the existing exact kernel. Its row forms match `NaturalCellAffineCompiler.compileCell`: original edge calendar inequalities, zero leaf ages, positive inverse rates, interior hybrid coordinates, chronology comparisons, scaled exposure intervals and hybrid intervals. The operation is not an arbitrary observation-law compiler. `SOURCE_ADMISSION_NOT_ESTABLISHED` remains in every valid result until the dynamic graph/active-exposure/type correspondence is actually checked. The copied mathematical theorem's hypotheses are not replaced by a caller flag.

## Canonical request

All framing, integer/rational normalization and 65,536-byte input rules from [CONTRACT.md](CONTRACT.md) apply. Input rationals remain bounded below `2^256` in numerator absolute value and denominator. Every mentioned record ID is a distinct original occurrence in its own registry; IDs are contiguous natural tokens in the declared input order. Parallel edges may have equal endpoints and still retain different edge IDs.

```text
RC1 CHART v e l h c x cap
ROOT rootVertex
EDGE 0 sourceVertex targetVertex
... exactly e EDGE records ...
LEAF 0 vertex
... exactly l LEAF records ...
HYBRID 0 vertex incomingEdge0 incomingEdge1
... exactly h HYBRID records ...
AGE LT leftAtom rightAtom
... exactly c AGE records ...
EXPOSURE 0 population youngerAtom olderAtom lowerBound upperBound
... exactly x EXPOSURE records ...
COIN 0 lowerBound upperBound
... exactly h COIN records ...
```

- Atom tokens are `V:id` for an original vertex age, or `Q:p/q` for a literal fixed rational age/cut. Signed fixed ages are permitted by the literal compiler grammar.
- Population tokens are `E:id` for an original edge occurrence or `A` for the one shared ancestral `None`. A new inverse rate for each ancestral exposure is forbidden.
- Bound tokens are `NONE`, `LE:p/q` or `LT:p/q`. Lower bounds compare their value to the coordinate; upper bounds compare the coordinate to their value. Absent endpoints generate no row. No hidden saturation upper bound is added.
- AGE comparisons are LT, LE or EQ. EQ emits two weak rows in forward/reverse order.
- EDGE, LEAF, HYBRID, EXPOSURE and COIN record IDs must be exactly `0,1,...,count−1` in the declared record order. All vertex/edge/hybrid references are range checked. Hybrid incoming occurrences are distinct edges with the stated target, with their supplied 0/1 occurrence order preserved.

Counts are finite natural tokens at most 32; `3≤v≤32`, `2≤e≤32`, `2≤l≤v`, `h≤v`, `c,x≤32` and `cap≤4096`. The stronger derived limits are `n=v+e+1+h≤32` and **actual emitted row count** `m≤128`. A maximum-row estimate does not refuse an otherwise valid chart with absent endpoints. The separate CHART limits do not enlarge the frozen AFFINE caps `n≤8,m≤64`.

## Structural checks and what they establish

The finite structural predicate mirrors `Nanuq.Source.RootedBinary`: one root of indegree zero/outdegree two; injective labelled leaves of indegree one/outdegree zero; every other vertex either indegree one/outdegree two or indegree two/outdegree one; no directed nonempty cycle; all vertices reachable from the root; and no nonroot vertex dominating all labelled leaves. For the last condition, each nonroot vertex must have at least one labelled leaf reachable from the root on a directed path avoiding that vertex **including both endpoints**. Zero-length reachability is permitted away from the blocked vertex. Degree counts include each original edge occurrence.

The HYBRID registry must enumerate exactly the indegree-two/outdegree-one vertices, with each incoming edge occurrence named once in that vertex's pair. No ordinary vertex can be relabelled as a hybrid. Leaves, hybrid vertices and the root have distinct roles under the degree conditions.

These are executable finite graph checks. Their refinement to the inherited proof carrier needs its own theorem; finite test success is not that theorem. Cut-child bridges, planarity/cofacial taxa, galledness, level, active-epoch interpretation, complete weak-order coverage, nonlinear probability rows and biological admission are not established by this predicate. The G6 supplied `RootedBinary` compiler has its own scope, broader than the original planar cut-child G3/G4 master class.

## Shared bank and exact row order

The effective bijective layout is fixed: age vertices `0..v−1`, inverse rates for original edges `0..e−1`, the single ancestral inverse rate, and inheritance coordinates for original hybrid IDs `0..h−1`. Its dimension is `v+e+1+h`. No rowwise copies or independent interval coordinates are created.

Every comparison is compiled from an affine form `f = constant + Σ coeffᵢxᵢ`. The row for `f <(≤) g` has coefficient vector `f.coeff−g.coeff`, bound `g.constant−f.constant` and the comparison strictness. Constant and variable atoms have their literal meanings. An exposure duration is `older−younger`. Rational input may combine into derived coefficients/bounds exceeding the input bit cap; emitted/solved values remain exact arbitrary-precision rationals.

Rows are emitted in these blocks, without deduplication or rescaling:

1. For each EDGE ID, `age(target)<age(source)`.
2. For each LEAF taxon ID, `age(leaf)≤0`, then `0≤age(leaf)`.
3. Positive inverse rates: each original EDGE ID, then ancestral A.
4. For each HYBRID ID, `0<g`.
5. For each HYBRID ID, `g<1`.
6. AGE records in input order; EQ emits forward then reverse weak comparison.
7. EXPOSURE records in input order; lower endpoint then upper endpoint when present. Lower q emits `q*u <(≤) duration`; upper q emits `duration <(≤) q*u`.
8. COIN intervals by hybrid ID; lower endpoint then upper endpoint when present. Lower q emits `q <(≤) g`; upper q emits `g <(≤) q`.

This is a new executable list convention. Its refinement target, after decoding at a checked effective layout, is `emittedList.toFinset = compileCell`; the inherited compiler supplies a finite set and does not define this order. Duplicate semantic rows stay in the ordered wire matrix. The concrete typed fixture and general compiler correspondence have separate proof receipts.

## Result and certificate

```text
RC1 RESULT CHART
BEGIN_REQUEST
<exact complete canonical CHART request bytes>
END_REQUEST
BANK n AGE:0 ... AGE:v-1 RATE:0 ... RATE:e-1 RATE:A COIN:0 ... COIN:h-1
MATRIX n m cap
<m canonical LE/LT bound coefficient rows>
END_MATRIX
GATE SOURCE_ADMISSION_NOT_ESTABLISHED
STATUS SAT
WITNESS n q0 ... q(n-1)
EVAL m lhs0 ... lhs(m-1)
END
```

The alternative payloads are the same as AFFINE: UNSAT uses `MULTIPLIERS m ...`, `BOUND ...`, `STRICT 0|1`; UNKNOWN uses `LIMIT currentDimension requiredRows cap`. Multipliers refer to the emitted matrix rows in the exact block order above. The resource cap, deterministic projection/back-substitution and exit codes stay unchanged: SAT/UNSAT 0, UNKNOWN 2, malformed/unsupported chart 1 with exactly `RC1 ERROR INVALID_REQUEST` plus LF.

Independent acceptance must first regenerate the matrix from the complete original chart and compare its exact rows/bank keys; then check the witness or nonnegative exclusion directly against those original compiled rows. Checking a solver-supplied arbitrary replacement matrix is insufficient. Request echo plus compiled rows bind the result to original IDs, shared ancestral rates, literal cuts, chronology and hybrid intervals. The independent checker must never promote the source-admission gate.

The native consumer's total certificate transport limit is separately documented at 4 MiB; excess or failed checking yields execution failure without a matrix or scientific certificate. A killed process is execution failure, not a mathematical NO. A feasible matrix does not establish that supplied exposures are the intended active epochs, nor that an actual source fits any observation law.

## Acceptance obligations

1. Compile both native implementations and compare actual CHART request/result bytes on admitted ordinary/hybrid/parallel-edge charts and refusal controls.
2. Compare emitted chronology, scaled exposure, coin and positivity rows to the existing `NaturalCellAffineCompiler`. Prefer a concrete type-safe Lean fixture with a checked emitted-row equality and actual coefficient evaluation. A hand-transcribed matrix alone is not that bridge.
3. Run original-row Fraction certificate checking independently of both elimination implementations, including negative coefficients, fixed cuts, absent bounds, equality, repeated populations and one ancestral rate.
4. Preserve previous AFFINE/COUNT accepted behavior and identities/receipts. If source or binary changes, record the new identity and run focused regressions appropriate to the additive operation.
5. Keep the graph/active-exposure/source-law/compiler refinement gaps explicit. The full modular G1–G7 and Rust scientific solver remain MASTER IN PROGRESS until their original obligations are discharged.
