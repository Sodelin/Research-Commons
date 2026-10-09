# Lazy ordinary-forest baseline and exact classical coordinate

Contributor: Codex graph lane, 9 October 2026. Derivative implementation of dot's
reviewed ordinary-population baseline at `00ecd0b5f444a12d6ce01ee5128791a772fbf055`.
Root serializes publication. This packet implements an accepted component;
general G3/G4 and an advantageous end-to-end quantum algorithm remain open.

The reusable module is
[forest_baseline.py](../../../applications/practical-solver/forest_baseline.py).
It stores one forest and yields forward/reverse neighbours lazily. It evaluates
the exact probability of a specified labelled unranked forest without building
the full forest graph or law. The ordinary generator uses one rate-one merge
for each unordered pair of roots; past subtrees remain opaque. The default
survival is an exact rational `0<x<1`, with `x=exp(-t)`. This is one ordinary
population from singleton entering labels, not a multicell/hybrid/source-fit
backend. There is no inheritance-mode projection or independently fitted slot.

## Run and use

From the repository root:

```sh
python3 applications/practical-solver/forest_baseline.py \
  --request research/2026-10-09-codex-conditional-bridge-1630z/graph/examples/one-ordinary-population.json \
  --output /tmp/ordinary-forest-new-result
python3 research/2026-10-09-codex-conditional-bridge-1630z/graph/test_forest_baseline.py
python3 research/2026-10-09-codex-conditional-bridge-1630z/graph/benchmark_forest_baseline.py
```

The output directory must be absent. The example evaluates `((1,2),3,4)` on
four entering labels at `x=1/2` and writes `RESULT.json`/`REPORT.md`, reporting
**7/192** and `EXACT_CLASSICAL_COORDINATE`. Exit 0 means a completed exact
coordinate; exit 2 refuses malformed/unsupported requests or an existing output
directory. No result is a certified source witness or general YES/NO decision.
The CLI rejects duplicate fields, symlink requests, floats, endpoints and
noncanonical trees. Its operational caps are 64 labels, 256 bits per survival
integer and a 64 KiB request. These do not establish an unknown-source size
bound or a runtime guarantee. The Python API has no fixed label cap.

```python
from fractions import Fraction
from forest_baseline import ForestGraph, HermitianDilation

graph = ForestGraph(4)
forest = ((1, 2), 3, 4)
assert graph.decode(graph.encode(forest)) == forest
assert graph.probability(forest, Fraction(1, 2)) == Fraction(7, 192)
next_forest = next(graph.forward_neighbors(forest))
previous_forests = graph.reverse_neighbors(forest)  # iterator, top-root splits
stats = graph.history_statistics(forest)
```

Use `canonical_forest` as an explicit convenience constructor for unordered
binary tuple trees. The core API rejects uncanonical input. Labels must be
exactly `1,...,m` once each; booleans and floats are not labels. Integer and
Fraction survival inputs are exact. Only explicit `allow_boundary=True` permits
`x=0` or `x=1`; these are mathematical diagnostics and do not certify positive
finite-duration source admission.

## Implemented statement and representation

The code uses the reviewed fixed-width serialization: leaf labels, opening and
closing tokens, root separators, then zero padding to `3m` token slots. Child
and root order is by least leaf label. There are `m+4` alphabet symbols,
`ceil(log2(m+4))` bits per token and `q=3m ceil(log2(m+4))` forest-register bits.
Unused codes are rejected; the dilation extends them by zero. Encoding,
decoding, validation, subtree/history processing and generator equality use
iterative walks, including a tested depth-1999 comb. There is no whole-state
index dictionary or hidden exponential preprocessing.

If the output forest F has r roots, m-r merger events, and each internal node v
contains a_v original entering leaves, the standard history count is

```text
h(F) = (m-r)! / product_v (a_v-1)
lambda_j = j(j-1)/2
P(m,r;x) = product_(j=r+1)^m lambda_j
           * sum_(j=r)^m x^lambda_j / product_(l=r,l!=j)^m (lambda_l-lambda_j)
E_m(x;F) = P(m,r;x) * h(F) / product_(j=r+1)^m lambda_j
```

Empty products cover r=m and m=1. The hook-product quotient is checked to be an
integer. All powers, signed polynomial coefficients and sums use Fraction;
floating cancellation is absent. Forward access gives `C(r,2)` distinct root
pair mergers. Reverse access splits a nonsingleton root's top node, never a
nonroot clade. Generator row sums are exactly zero.

The formula, forest compiler and sparse construction retain the original
provider's attribution. This is a reusable derivative, not a new probability
identity or proof of historical novelty. Governing sources and exact hashes are
in [SOURCE-PINS.json](SOURCE-PINS.json).

## Executed evidence

[TEST-RESULT.json](TEST-RESULT.json) records authored execution of 11 tests,
all passing, with these exact scopes:

| Check | Execution |
|---|---:|
| Existing `forest_algebra.py` coordinate comparisons, same inputs under 0-based/1-based label bijection, m<=6 | 10,976 |
| Canonical code roundtrips matching the reviewed encoding, m<=6 | 2,744 |
| Forward directed edges, m<=6 | 3,356 |
| Explicit dynamic-program history / exact reverse-adjacency comparisons, m<=6 | 2,744 |
| Root-count normalization checks at four strict survivals, m<=6 | 84 |
| Nonzero Hermitian entry symmetry checks, m<=4 | 146 |
| Two-sided location/inverse probes, m<=5 | 12,532 |

The exact comparison survivals are `1/2`, `2/3`, `1/65536` and `65535/65536`.
Each complete small law normalizes to one; boundary diagnostic laws were also
compared for m<=5. Other checks cover all code strings at m=1, malformed
encodings, repeated/missing labels, root/child order, strict numeric contracts,
CLI refusals/output preservation and deep comb processing. This is authored
execution. Independent replay is owned by the validation lane and is recorded
in its separate packet; this file does not impersonate that evidence. No Lean
kernel, arbitrary-size circuit compiler, quantum simulator or hardware ran.

The pre-freeze expression `f==g` used Python tuple equality. Two attempts to
reproduce a recursion failure, on 1,100 and 2,000 entering labels, did **not**
trigger one on Python 3.12. Both failure-seeking scripts returned exit 1 because
their expected exception was absent; the unsuccessful probes remain in
[DEEP-EQUALITY-PROBE-FIRST.json](DEEP-EQUALITY-PROBE-FIRST.json) and
[DEEP-EQUALITY-PROBE-SECOND.json](DEEP-EQUALITY-PROBE-SECOND.json).
The final module uses iterative structural equality as a robustness choice;
[DEEP-EQUALITY-CHECK.json](DEEP-EQUALITY-CHECK.json) confirms the correct deep
entry without requiring or claiming a prior crash. These are expression-level
checks, not a rerun of the whole former module. No failed former-suite run is
invented, and no dependence of tuple comparison on Python's recursion-limit
setting is asserted.

## Classical costs and bounded runtime

[BENCHMARK-RESULT.json](BENCHMARK-RESULT.json) records 36 exact coordinates:
m in `{8,16,32,64}`, survival numerator bit sizes `{8,32,64}` and singleton,
paired-root and comb forests. Survival is `(2^b-1)/2^b`, whose denominator has
**b+1** bits. The power degree is at most `C(m,2)`; count-polynomial construction
has O(m^2) elementary integer products and at most m terms. Coefficient,
history and hook-product integers have polynomial bit length. Exact powers
have O(bm^2) bits, and arithmetic must be charged at those lengths. Python big
integer operations and Fraction gcd costs are included in the measured runtime.
No arithmetic operation is charged as unit cost in the polynomial-bit claim.

Times are untraced probability calls, median of three for m<=32 and one call
for m=64. Traced memory comes from a separate exact replay and excludes process
startup/import overhead. The saved machine receipt is the authoritative timing
record; timings are bounded observations, not a proved exponent or portable
performance promise. The largest measured rational denominator has 129,643
bits, despite a 64-bit numerator / 65-bit denominator survival input. The
largest measured probability-allocation peak is approximately 151 KiB.
The worst m=64 probability case took less than 0.4 s on this execution host.

Sparse access was measured separately. At m=64 the forest encoding has 1,344
bits, the largest row has 2,017 entries, and one full current-row support was
materialized for that benchmark. First-neighbour access takes only one output
forest. Location access sorts/pads only the current polynomial-size row; repeated
calls recompute that row. This is charged work, not free table access or a
precompiled circuit. The benchmark never materializes the full forest graph.

## Dilation interface and missing quantum task

`HermitianDilation(graph)` exposes exact rational `nonzero_entries`, `entry`,
`padded_columns`, `location`, `inverse_location` and symmetric signed
`rounded_entry`. For m>=2 it uses
`H=[[0,Q],[Q^T,0]]/C(m,2)`, q+1 layered bits and sparsity `C(m,2)+1`.
For m=1 H=0 with one zero padding slot. Actual support plus the first unused
column codes is a sorted distinct list I. Slots below its size map to I;
remaining slots unrank the complement, with a two-sided inverse on the entire
register. Invalid row codes have zero entries and a valid padded permutation.
Fixed-point truncation is symmetric under transpose with entry error `<2^-p`.

This is an exact **classical access specification**, not a reversible circuit
or compiled quantum simulator. `exp(-itH)` is a different evolution from
the original stochastic `exp(tQ)`. Its amplitudes are not E_m(x;F), and this
module supplies no identity connecting a dilation measurement to that original
observable. The oracle audit at `af7107c5` also requires relative phases,
uniform coherent accuracy, arbitrary answer-register values and clean scratch;
per-basis Python correctness does not discharge those circuit obligations.

An end-to-end quantum claim must first specify the same original output task,
for example one forest probability within additive epsilon and declared
success probability, then prove a faithful extraction rule. It must charge:

1. Reading m, F, exact x and epsilon; classical preprocessing and circuit construction.
2. State preparation, coherent forest encoding/validation and any work registers.
3. Full location/entry circuit evaluation and uncompute at every access, including phases.
4. Simulation dependence on numerical time, sparsity, rational value precision and error budget; binary time input alone is not fast forwarding.
5. Measurement repetitions or amplitude-estimation calls, confidence and final classical readout.
6. Total gates, qubits, classical bit time and reuse/preprocessing costs against the exact classical formula or the same-accuracy classical baseline.

None of the missing extraction/circuit/resource comparison follows from a huge
ambient forest count. An amplitude-encoded full law is a different output
contract from an explicitly written probability table. No quantum speedup is
established here; no hardware, services or outreach are required.

## Obligation register

| Obligation | Status | Evidence / next action |
|---|---|---|
| Original G3 exact unknown-size same-source recognition / G4 fixed-target all-rival forcing | OPEN | Original master statements unchanged; this ordinary-population evaluator is not a decision procedure. |
| Governing ordinary compiler, hook history formula and sparse baseline | Reviewed inherited component | `00ecd0b5`, existing compiler and independent hand review; pins below. |
| Lazy access / exact specified-forest evaluator | COMPONENT IMPLEMENTED, bounded execution PASS | Reusable module, tests and bit-size benchmark. |
| Independent new-module acceptance | Separate validation evidence | Validation lane replays/adversarially reviews frozen hashes. |
| Practical launcher | Coordinated with release lane | Release owns run.py and launch evidence; no graph-lane run.py edits. |
| Faithful quantum extraction and advantageous full-resource algorithm | OPEN | Prove original observable correspondence and implement/cost all six resource categories above. |
| Lean/circuit/hardware verification | Not executed | No such verification claimed or required for this classical deliverable. |
