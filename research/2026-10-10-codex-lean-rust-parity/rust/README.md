# Exact native matrix and natural-cell components

Contributor: Codex Rust implementation role, 10 October 2026. This derivative
extends the inherited Rust exact-arithmetic packages with a complete finite
strict-affine decision, a deterministic rational witness, exclusion
multipliers and independently checked native execution. An additive literal
natural-cell compiler now builds these rows on one shared original-ID bank.
The inherited typed G6 theorem and compiler are attributed in
[INHERITED-SOURCES.json](INHERITED-SOURCES.json).

For one finite rational matrix, all rows use one shared parameter vector.
`SAT` supplies an assignment satisfying every original row. `UNSAT` supplies
nonnegative original-row multipliers which annihilate every coefficient and
give a strictly contradictory bound. An independent checker uses original
row arithmetic, without running Fourier–Motzkin. Projection beyond the
declared budget yields `UNKNOWN`; it has no negative implication. RC1 count
arithmetic retains `UNKNOWN_SOURCE_PROVIDER` and exits 2.

The literal compiler checks rooted binary structural predicates, preserves
parallel edge occurrences and assigns one age per vertex, inverse rate per
edge plus one ancestral rate, and coin per hybrid. Exposure constraints using
the same original edge share its rate. All compiled rows are solved jointly.
Software validation has not been refined into the inherited typed source
premises. Active-exposure admission, source census coverage and the observation
law are also unfinished. Both components retain
`SOURCE_ADMISSION_NOT_ESTABLISHED`; general G3/G4 and empirical nine-parameter
accuracy remain open.

## Build

Provision the inherited checksum-pinned Rust1.90.0 and five dependency archives
in fresh scratch. Initial provisioning uses public network; the new build is
locked and offline. Toolchains, vendored dependencies and binaries stay outside
the repository:

```sh
python3 -B research/2026-10-09-codex-practical-release-0207z/coordinator/native_replay.py --scratch /tmp/parity-native-1
python3 -B research/2026-10-10-codex-lean-rust-parity/rust/build.py --runtime /tmp/parity-native-1/runtime --output /tmp/parity-build-1
```

The inherited interval, signed-nine and Poisson packages are reused by local
Cargo path dependencies, preserving their original bytes. The new library also
ports the inherited exact ordinary-forest formula; its API computes `7/192` for
the reviewed four-label example. That forest API currently has no RC1 wire or
Lean executable parity claim. Source pinning identifies reference bytes; it is
neither a signature nor a proof that an arbitrary binary uses those bytes.

## Solve and independently check

Save a canonical ASCII request to `/tmp/cell.rc1`:

```text
RC1 AFFINE 1 2 1
LT 0/1 -1/1
LT 1/1 1/1
```

```sh
/tmp/parity-native-1/runtime/parity-target/release/parity-solver solve /tmp/cell.rc1 --output /tmp/cell-certificate-1.rc1
/tmp/parity-native-1/runtime/parity-target/release/parity-solver check /tmp/cell.rc1 /tmp/cell-certificate-1.rc1
```

No arguments means one stdin request. `solve -` explicitly selects stdin.
Native `--output` files must be absent. SAT/UNSAT exit 0, projection UNKNOWN and
conditional count exit 2, invalid requests exit 1. Internal certificate errors
and file execution failures have distinct error strings. The result echoes the
entire request, preventing another matrix's certificate from being substituted.
The [design contract](../design/CONTRACT.md) owns canonical byte semantics.

AFFINE requests are capped at eight dimensions and 64 original rows. CHART has
separate limits: 32 bank coordinates, 128 actually emitted rows, and at most
32 records of each kind. Both cap requests at 65,536 bytes and each projected
stage at 4,096 rows. Input rational magnitudes are below `2^256`; intermediate
arithmetic is exact and has no hidden digit cap. The native independent-check
command accepts at most 4MiB of certificate bytes. These operational limits do
not prove practical termination of larger tasks. AFFINE/COUNT syntax, caps and
canonical output bytes remain unchanged by the CHART extension.

The staged component preserves full evidence and separately launches the native
checker and the pinned Python Fraction checker. Each child has a 30-second CPU
cap, 45-second wall timeout, 512MiB address-space cap and 16MiB per-file cap:

```sh
python3 -B research/2026-10-10-codex-lean-rust-parity/rust/native_component.py --request /tmp/cell.rc1 --binary /tmp/parity-native-1/runtime/parity-target/release/parity-solver --output /tmp/native-cell-1
```

Optional `--expected-binary-sha256` verifies a caller-supplied pin before
launch. Without it, the digest is explicitly an observation. The adapter stages
one captured binary/request/helper buffer, tracks each actual process start and
refuses reused output directories. Outcomes are `MATRIX_WITNESS`,
`MATRIX_EXCLUSION`, `UNKNOWN`, `REFUSED_REQUEST` or
`RESOURCE_OR_EXECUTION_FAILURE`, preserving source-admission limits.

## Literal natural-cell chart

The [CHART contract](../design/CHART-CONTRACT.md) specifies original vertex,
edge, leaf and hybrid IDs, literal age comparisons and exposure/coin intervals.
The exact compiler follows the inherited `NaturalCellAffineCompiler` forms;
its eight ordered row blocks are a new executable convention because the
inherited compiler returns a `Finset` without a canonical iteration order.
Responses bind the full chart request, bank keys, every emitted matrix row and
the source-admission gate before the checked witness or exclusion. The
independent Fraction helper regenerates this complete matrix from the chart.

For a two-tip cell with fixed root age and three literal exposure intervals:

```sh
python3 -B research/2026-10-10-codex-lean-rust-parity/rust/native_chart_component.py --request research/2026-10-10-codex-lean-rust-parity/design/chart-fixtures/chart_two_tip_typed_cells.req --binary /tmp/parity-native-1/runtime/parity-target/release/parity-solver --output /tmp/native-chart-1
```

The separate adapter uses the same bounded stages and exit meanings as the
AFFINE adapter, with schema `rust_natural_cell_component_result_v1`. Both
reviewed Fraction modules are captured and hash-pinned; an isolated child runs
their captured bytes without importing a mutable companion path. The staged
bootstrap has its own recorded digest. Source/helper identities and the
observed release identity are in [COMPONENT-PINS.json](COMPONENT-PINS.json).

The original AFFINE release and source snapshot are preserved separately under
`/workspace/scratch/lean-rust-parity-native/runtime/affine-v1-frozen/` and
[evidence/history/affine-v1](evidence/history/affine-v1). The additive CHART
build receipt is [chart-build-1](evidence/chart-build-1/BUILD-RECEIPT.json).

## Executed verification

- Nineteen Rust tests passed: thirteen affine/count/certificate controls plus
  six natural-cell controls for original IDs, parallel occurrences, graph
  refusal, shared exposure contradictions and compiler/certificate binding.
  The optimized build passed with locked offline dependencies.
- The design owner's Lean/Rust canonical byte differential passed 281 cases
  with independent Fraction certificate checking and forged controls. Its
  separate receipt is in `../design/evidence/parity-attempt-2/`.
- The focused additive replay passed 78 cases: 46 frozen AFFINE/COUNT cases and
  32 CHART cases. Fifteen altered CHART certificates were independently rejected.
  See `../design/evidence/chart-parity-attempt-1/PARITY-RECEIPT.json`.
- [Exact Z3 adjunct](evidence/exact-z3-oracle-RESULT.json): 250 seeded matrices
  matched exact QF_LRA statuses; all 250 returned certificates passed direct
  Fraction original-row checks. Eight native CLI/certificate controls passed.
- Fifteen staged-component controls passed, including false producer exit
  pairing, process-creation failure, failure after start, forged witness despite
  fake native-check acceptance, cross-request substitution and output retention.
  The same fifteen AFFINE controls passed after the CHART adapter extension;
  [the new receipt](evidence/affine-after-chart-component-TEST-RESULT.json)
  identifies the current shared adapter and binary.
- [Sixteen CHART adapter controls](evidence/chart-component-TEST-RESULT.json)
  passed, including altered matrix/witness rejection despite fake native-check
  acceptance, false gate promotion, original-chart substitution, producer
  status/exit mismatch, process-start provenance and fresh-output preservation.
- Fresh inherited 39-case signed-nine replay passed. Its unchanged diagnostic
  scope is preserved in [the fresh receipt](evidence/inherited-native-REPLAY-RESULT.json).
- The first test source compilation failed on two non-Copy array repetitions;
  the corrected tests passed. The independent SymPy attempt stalled and was
  terminated; [its incomplete receipt](evidence/oracle-attempt-1.json) is excluded
  from acceptance, with the former harness source preserved under `evidence/history/`.

Finite tests are evidence of execution, not a universal proof of Rust or of the
complete scientific pipeline. Next: prove that the executable graph validator
and ordered compiler refine the inherited typed graph and cell predicates,
establish active-epoch chart admission, then connect actual coefficient/law
fitting, complete source census and G7 confidence/count policy. A literal chart
matrix decision alone does not discharge those obligations.
