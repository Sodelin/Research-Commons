# Exact native matrix, natural-cell and genealogy-law components

Contributor: Codex Rust implementation role, 10 October 2026. This derivative
extends the inherited Rust exact-arithmetic packages with a complete finite
strict-affine decision, a deterministic rational witness, exclusion
multipliers and independently checked native execution. An additive literal
natural-cell compiler now builds these rows on one shared original-ID bank.
The inherited typed G6 theorem and compiler are attributed in
[INHERITED-SOURCES.json](INHERITED-SOURCES.json).
The actual G7 joint-frontier compiler is now ported as an additive formal
genealogy-law operation, retaining that same provenance discipline.

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

## Formal joint genealogy law

The [LAW contract](../design/LAW-CONTRACT.md) ports the actual inherited
[full joint-frontier compiler](../../2026-10-01-g7-continuous-design/law_compiler.py).
It follows all correlated edge forests together, routes whole current lineages
at original hybrids, applies the shared exact ordinary-population kernel and
completes the ancestral root. COMMON draws one route for the current locus;
INDEPENDENT enumerates the current lineage choices. A merged tree remains one
lineage. Distinct parallel edges keep distinct formal survival variables.

Outputs include every nonzero rooted genealogy polynomial and its complete
unrooted split pushforward. Coefficients are reduced rationals; sparse exponent
vectors use original edge variables followed by original hybrid variables.
Three copied tips reproduce the species-tree coefficients `1−2X/3, X/3, X/3`.
Up to four distinct copied labels may attach to repeated or unsampled taxa.
Declared history/state/term budgets are checked before generating the new
stage; exhaustion returns UNKNOWN with no partial table. Full table response
bytes are capped at 4MiB.

```sh
python3 -B research/2026-10-10-codex-lean-rust-parity/rust/native_law_component.py --request research/2026-10-10-codex-lean-rust-parity/design/law-fixtures/law_three_tip.req --binary /tmp/parity-native-1/runtime/parity-target/release/parity-solver --output /tmp/native-law-1
```

This separate bounded adapter reports `FORMAL_GENEALOGY_TABLE`, schema
`rust_genealogy_law_component_result_v1`. Native `check` replays the forward
compiler; it is not an independent law algorithm. A separate isolated child
compares every coefficient with the captured, hash-pinned original Python
compiler, and independently checks normalization and the unrooted pushforward.
It captures all four provider/checker source buffers before launch. SymPy
1.14.0 and mpmath 1.3.0 are required by
[law_component_requirements.txt](law_component_requirements.txt); the bounded
child records their observed versions, origins and initializer identities.
This does not verify every byte of the supplied third-party runtime.

`formal_table_checked` and `inherited_baseline_all_coefficients_checked` become
true only after both native replay and independent checking succeed.
`certificate_checked` stays false: a compiled formal table is not a
mathematical source certificate. Source admission, physical survival image,
full joint calendar law, observation admission and statistical confidence
remain false. Independent rational X probes need not lie on the shared
calendar/rate image `X_e=exp(−rho_e·duration_e)`.

The original source/menu discipline is recorded in
[MASTER-STATEMENTS.md](../../2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md).
The October 1 compiler and accepted mathematics are earlier providers, rather
than new polynomiality claims. The latest
[completed-calendar theorem](../../2026-10-09-dot-g7-completed-calendar-polynomial-2330z/README.md)
retains one shared original physical rate/probability bank, natural register
initialization and ancestral completion. Its noncomputable polynomial choices
are not an extracted frontier compiler. The next required correspondence is
from this effective frontier to that actual selected-state/source-program
law, with the correct admitted reader and physical image.

The accepted CHART release/source snapshot remain at
`/workspace/scratch/lean-rust-parity-native/runtime/chart-v1-frozen/` and
[evidence/history/chart-v1](evidence/history/chart-v1). The new LAW build has
its separate [receipt](evidence/law-build-1/BUILD-RECEIPT.json).

## Literal source-population refinement

The internal [source_population.rs](src/source_population.rs) ports the actual
ordered original-source recurrence recovered in the latest
[G7 coefficient packet](../../2026-10-10-dot-g7-pending-codex-recovery-0952z/README.md).
It preserves the live representative, ancestry, ordered genealogy graft,
original edge or ancestral location, and the entire original vertex register.
Each of the two ordered merger orientations retains its own destination and
half rate. Two singleton copies therefore produce two distinct literal merged
states, each with polynomial `(1-X)/2`. Their full unordered fibre has `1-X`.

The restricted copy carrier has at most four local labels and an injective
embedding into global copied-label IDs. All local copies must belong to the
specified original population, and each original sample must descend from it.
The module checks the literal forest/ancestor invariants and uses the inherited
`encodeActual` image: live genealogy/population fields are `some`, dead fields
are `none`. An arbitrary admitted original Code may retain dead garbage or
active `none` defaults; those variants are outside this library's input scope.
Carried subtrees remain intact, and representatives
need not be the smallest label. Explicit library work limits return UNKNOWN
without a partial row. The module adds no RC1 operation and is not substituted
for the accepted LAW compiler merely by being linked into the crate.

The fixed-fixture diagnostic probe emits every normalized literal destination
and every complete unordered fibre sum:

```sh
/tmp/parity-native-1/runtime/parity-target/release/examples/source_population_probe fourAncestral
```

Its JSON is test interchange, not a public command contract or a mathematical
certificate. The independent spectral oracle applies the literal ordered-pair
generator; it uses neither the new recursive lift algorithm nor LAW's merger
history formula. All eight fixture comparisons passed, including 193 literal
four-copy destinations, nonminimum representatives, earlier subtrees,
restricted label permutations and changed frozen registers. The original typed
Lean coefficient code-generation comparison is still pending. Historical
component checks in the recovery packet do not establish successful extraction.
Reachable-row support, label transport and general quotient refinement also
remain separate proof obligations under the
[internal refinement contract](../design/POPULATION-REFINEMENT.md).

The complete accepted LAW v1 sources, helpers and adapter identities were
preserved before this addition in
[evidence/history/law-v1/SNAPSHOT.json](evidence/history/law-v1/SNAPSHOT.json),
with its original executable in the scratch `law-v1-frozen` directory. The
original byte-parity receipts are not relabelled as source-refinement evidence.

## Executed verification

- Thirty-two Rust tests passed in the additive
  [population build](evidence/population-build-2/BUILD-RECEIPT.json). The seven
  added checks cover literal ordered half rates, full destination rows,
  original snapshot/descendant invariants, carried subtrees, original parallel
  identities, explicit resource refusal and every unordered coefficient against
  the accepted LAW edge kernel. The earlier twenty-five tests comprise thirteen affine/count/certificate controls,
  six natural-cell controls and six LAW controls. LAW tests cover the species
  tree closed form, ordinary kernel initial/differential identities, current
  lineage routing, original parallel variables and conservative budget priority.
  The optimized build passed with locked offline dependencies.
- The design owner's Lean/Rust canonical byte differential passed 281 cases
  with independent Fraction certificate checking and forged controls. Its
  separate receipt is in `../design/evidence/parity-attempt-2/`.
- The focused additive replay passed 78 cases: 46 frozen AFFINE/COUNT cases and
  32 CHART cases. Fifteen altered CHART certificates were independently rejected.
  See `../design/evidence/chart-parity-attempt-1/PARITY-RECEIPT.json`.
- The additive LAW native replay passed 117 cases, comprising the 78 frozen
  prior cases plus 39 LAW cases. Every TABLE coefficient matched the pinned
  original full-joint compiler; thirteen forgeries were rejected. Its receipt
  is `../design/evidence/law-parity-attempt-1/PARITY-RECEIPT.json`; repeated cases
  are not additional scientific coverage.
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
- [Fourteen LAW adapter controls](evidence/law-component-controls-1/TEST-RESULT.json)
  passed. A balanced false law preserved exact normalization and the unrooted
  pushforward, and was rejected by the independent full-coefficient comparator
  despite fake native acceptance. The evidence export retains requests, exact
  responses, execution/checker logs and the original authored harness; staged
  executable images remain in scratch.
- The independent source-population spectral review passed eight fixtures;
  [its receipt](../design/evidence/population-rust-review-2/RECEIPT.json) checks
  every literal coefficient and complete unordered fibre. The first probe
  attempt had schema/fixture metadata drift and failed before coefficient
  comparison. Its receipt and original diagnostic source/binary remain
  preserved; the corrected contexts match the frozen design fixtures exactly.
- The rebuilt executable passed all 117 frozen RC1 regression cases against
  the Lean baseline after the library addition, with exact canonical outputs
  and independent certificate/reference checks. Its separate
  [receipt](../design/evidence/law-plus-population-regression-1/PARITY-RECEIPT.json)
  establishes continued wire behavior, not original source-law refinement.
- Fresh inherited 39-case signed-nine replay passed. Its unchanged diagnostic
  scope is preserved in [the fresh receipt](evidence/inherited-native-REPLAY-RESULT.json).
- The first test source compilation failed on two non-Copy array repetitions;
  the corrected tests passed. The independent SymPy attempt stalled and was
  terminated; [its incomplete receipt](evidence/oracle-attempt-1.json) is excluded
  from acceptance, with the former harness source preserved under `evidence/history/`.

Finite tests are evidence of execution, not a universal proof of Rust or of the
complete scientific pipeline. Next: prove that the executable graph validator
and ordered compiler refine the inherited typed graph and cell predicates,
establish active-epoch chart admission, connect the effective frontier to the
actual completed source-program law and physical image, then implement joint
fitting, complete source census and G7 confidence/count policy. Neither a
literal chart matrix decision nor a formal terminal genealogy table alone
discharges those obligations.
