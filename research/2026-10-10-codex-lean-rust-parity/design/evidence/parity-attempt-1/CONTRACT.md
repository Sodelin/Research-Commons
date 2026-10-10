# Exact executable contract, version RC1

Contributor: Codex solver design role, 10 October 2026. This is an implemented-component contract, not general G3/G4 closure. The full mission is retained in [../MISSION.md](../MISSION.md).

The first end-to-end slice parses a supplied finite G6 natural-cell matrix, decides its mixed strict rational affine inequalities within an explicit projection budget, returns a shared rational witness or an independently checkable exclusion certificate, and serializes every request/result/certificate byte identically in Lean and Rust. It reuses the exact row semantics of `UnifiedLean.G6.StrictAffineElimination.Row` and the original-bank interpretation of `NaturalCellAffineCompiler`; it does not replace the source model with unrelated stochastic matrices.

Byte identity refers to canonical request and response/certificate bytes. Lean and Rust executable files have different bytes. Differential testing is finite execution evidence. A correspondence theorem or proved certificate checker is a separate obligation.

## Types and scientific boundary

| Value | Exact representation and meaning |
|---|---|
| Rational | Arbitrary-precision signed integer numerator and positive natural denominator, reduced by gcd; `0/1` is the unique zero |
| Affine row | Ordered vector `a : Fin n → ℚ`, bound `b : ℚ`, strictness bit; `Σ aᵢxᵢ < b` for LT and `≤ b` for LE |
| Matrix | Ordered list of rows; every row uses one shared vector and the same variable layout; duplicate rows are allowed |
| Natural-cell bank | Existing `BankVar N = V ⊕ (Option E ⊕ Hybrid N)`: one age per original vertex, one inverse rate per original edge plus the ancestral `None`, and one inheritance coordinate per original hybrid |
| Witness | One rational vector satisfying **every** supplied row; physical rate coordinates decode as reciprocals of the positive inverse-rate coordinates |
| Exclusion | Nonnegative original-row multipliers cancelling every coefficient, with a negative aggregate bound or a zero bound containing a positive-weight strict row |
| Projection budget | Maximum rows in any one generated projection; exhaustion has no infeasibility conclusion |

An arbitrary matrix is an affine mathematical problem. Calling it an original source chart requires the existing typed `compileCell` construction, effective bijective layout, graph admission and active-exposure interpretation. Neither a label nor a caller boolean supplies those premises. A literal chart can be feasible even if the caller supplied an inappropriate active epoch. The current grammar does not encode exact terminal forest probabilities, nonlinearity, fixed irrational-rate restrictions, complete source enumeration, continuous source-image distance or biological data calibration.

An infeasible **single** admitted chart excludes that chart only. It is never unrestricted exclusion of all original sources. General G3 still needs effective coverage over unknown finite source sizes and word lengths. General G4 still needs the original fixed-target unknown-size finite-forcing result or the fixed-target exact all-prefix alternative.

## Transport and canonical grammar

One process reads exactly one request from standard input and writes one result to standard output. Diagnostics may use stderr. A valid request is ASCII, at most 65,536 bytes, uses LF line endings, has exactly one final LF, has no blank or extra lines, and separates tokens by exactly one ASCII space. No leading/trailing spaces, tabs, CR, JSON, floats or nonfinite values are admitted.

Natural tokens are `0` or a nonzero decimal digit followed by decimal digits. Rational tokens are `p/q`, including denominator one. The numerator is `0`, a positive natural token or its negation; the denominator is positive; gcd is one. Negative zero, plus signs, leading zeroes, unreduced fractions, negative denominators and omitted denominators are refused. Input numerator absolute value and denominator must each be strictly below `2^256`. Intermediate arithmetic is exact arbitrary precision without rounding or a hidden overflow threshold. External process exhaustion supplies no certificate.

### AFFINE request

```text
RC1 AFFINE n m cap
LT bound a0 a1 ... a(n-1)
LE bound a0 a1 ... a(n-1)
```

There are exactly `m` row lines, in any LT/LE order; `0 ≤ n ≤ 8`, `0 ≤ m ≤ 64`, `0 ≤ cap ≤ 4096`. For `n=0`, a row line has only its tag and bound. Equalities use two opposing weak rows; they are not silently made strict. The cap applies to generated projections, independently of the initial row count.

At dimension `d>0`, partition rows by the sign of the last coefficient. Before generating a projection, compute `required = zeroCount + positiveCount*negativeCount`. If `required > cap`, emit UNKNOWN with the current dimension, required count and cap. Otherwise retain zero rows in input order with the last coefficient removed, then combine every positive row `p` in input order with every negative row `m` in input order. The combination is `(-m.last)*p + p.last*m`, drops the cancelled last coefficient and has strictness `m.strict || p.strict`. Do not deduplicate or rescale generated rows. Original-row multiplier vectors are transformed by exactly the same positive combination. Recursion removes the last coordinate until dimension zero.

At dimension zero, choose the **first** failing row in the projected list: its bound is negative, or zero with strictness true. This determines the canonical exclusion multiplier vector. Otherwise back-substitute. Evaluate each endpoint `(bound - drop.eval(x))/last`; lower extrema are maxima and upper extrema are minima. Strictness of tied extrema is OR. Choose the midpoint when the lower endpoint is less than the upper, the common endpoint when they are equal and weak, lower+1 with only lower bounds, upper−1 with only upper bounds, and zero with neither. An equal endpoint with a strict extremal row is infeasible and cannot occur on a successful exact projection path. Variable order is the supplied layout order.

### AFFINE result/certificate

Every valid result begins with the exact request bytes, framed without a hash dependency:

```text
RC1 RESULT AFFINE
BEGIN_REQUEST
<exact canonical request bytes>
END_REQUEST
```

Successful feasibility appends:

```text
STATUS SAT
WITNESS n q0 q1 ... q(n-1)
EVAL m lhs0 lhs1 ... lhs(m-1)
END
```

There is no trailing space for an empty vector: `WITNESS 0` and `EVAL 0` are entire lines. Each lhs is recomputed from the **original** corresponding row and one returned vector. Independently verify dimensions and all original inequalities.

Infeasibility appends:

```text
STATUS UNSAT
MULTIPLIERS m w0 w1 ... w(m-1)
BOUND q
STRICT 0
END
```

`STRICT` is 0 or 1 and must equal whether any original LT row has a positive multiplier. Independently verify all multipliers are nonnegative, each `Σ wⱼaⱼᵢ = 0`, the aggregate bound equals `Σ wⱼbⱼ`, and either that bound is negative or it is zero with strictness 1. A forged strictness flag or forged aggregate bound is rejected. The certificate proves affine-matrix infeasibility, not chart coverage.

Budget exhaustion appends:

```text
STATUS UNKNOWN
LIMIT currentDimension requiredRows cap
END
```

SAT/UNSAT exit 0. UNKNOWN exits 2. Malformed, out-of-contract or noncanonical input exits 1 and writes exactly `RC1 ERROR INVALID_REQUEST` followed by LF. No request is echoed on refusal. A killed/crashed process is an execution failure, not an UNKNOWN certificate or a mathematical decision.

### COUNT request and result

```text
RC1 COUNT b epsilon sigma M
```

All four arguments are canonical rational tokens; `b,epsilon,sigma>0` and `M≥0`. Compute `delta=min(epsilon,sigma/(2*(M+1)))`, `B=2*(1+delta)/(b*delta)` and the least integer ceiling of B. The corresponding result uses the same exact request frame:

```text
RC1 RESULT COUNT
BEGIN_REQUEST
<exact canonical request bytes>
END_REQUEST
STATUS CONDITIONAL_ARITHMETIC
DELTA delta
BOUND B
CEILING natural
GATE UNKNOWN_SOURCE_PROVIDER
END
```

Exit 2 always: the numeric calculation is usable, but it does not construct the original `PieceCertificate`/`WholeFibreProvider`, verify coverage, derive an observed survival floor or compile the retained-slot bound into a complete original source registry. No input flag activates those missing providers. This is the existing conditional count consumer's conservative behavior.

## Acceptance and remaining correspondence

Acceptance requires actual Lean and Rust executable invocation on identical canonical requests, identical stdout bytes and exit codes, and an independent verifier that checks SAT and UNSAT directly against the original rows without trusting the elimination program. Both languages refusing malformed inputs is checked as transport behavior, not arithmetic proof. The harness records binary/source identities, requests, both outputs, stderr, return codes, timings and a fresh dated receipt.

The general existing affine decider theorem, new constructive witness theorems, executable list refinement, wire parser and serializer, certificate checker and Rust correspondence have separate verification scopes. Exact test agreement alone cannot close a missing theorem about parser completeness or all Rust executions. Noncomputable classical existence statements and arbitrary `Fintype` numberings are proof dependencies; executable inputs require effective explicit layouts. Full G1–G7 package replay, source/observation admission and the practical nine-parameter branch are tracked separately in [TRACEABILITY.md](TRACEABILITY.md).
