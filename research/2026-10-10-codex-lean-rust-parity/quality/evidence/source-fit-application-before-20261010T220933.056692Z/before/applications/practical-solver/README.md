# Practical genealogy solver

Run the inherited nine-parameter solver, independently check its complete
journal, and export a readable report plus exact machine-readable evidence.
Included examples demonstrate informative arithmetic, finite-data UNKNOWN and
unsupported-model refusal. The application uses the existing solver and keeps
its scientific limits visible.

## Launch

Clone Research Commons and use Python 3.10+ on Linux or another POSIX system
with Python's `resource` module. The core requires no package installation,
credentials or network after cloning:

```sh
git clone https://github.com/Sodelin/Research-Commons.git
cd Research-Commons
python3 -B applications/practical-solver/run.py run --example informative
```

The command prints a new dated output directory and its `REPORT.html` path.
Open that file in a browser. `REPORT.md` is portable Markdown and `RESULT.json`
contains exact bounds and the complete retained outer cover. Defaults save
under `runs/`; choose explicit fresh directories for reproducible demonstrations:

```sh
python3 -B applications/practical-solver/run.py run --example informative --output /tmp/solver-informative-1
python3 -B applications/practical-solver/run.py run --example finite-data --output /tmp/solver-finite-1
python3 -B applications/practical-solver/run.py run --example unsupported --output /tmp/solver-refusal-1
```

Output directories must be absent. Reusing a path is refused to preserve
previous results. Paths shown here are examples; use new names for later runs.

## Conditional count and exact source backend

Use the same launcher to consume the reviewed count arithmetic or invoke the
existing exact source census/backend:

```sh
python3 -B applications/practical-solver/run.py certified-bounds --request applications/practical-solver/examples/certified-bounds/conditional-count-unknown.json --output /tmp/solver-count-new
python3 -B applications/practical-solver/run.py certified-bounds --request applications/practical-solver/examples/certified-bounds/finite-witness.json --output /tmp/solver-source-new
```

The first example computes delta=1/2 and ceiling=24, then returns **UNKNOWN**:
its placeholder provider is unverified, and no all-core source catalogue bridge
exists. An artifact hash or supplied hypothesis does not discharge that
obligation. The bound is not applied as a hybrid-count budget.

The second command reuses the original exact shared-row feasibility backend.
It also returns UNKNOWN when pinned backend dependencies are absent. A prepared
scratch environment can be selected with `--python-executable /absolute/path/to/venv/bin/python`;
see the [bounded integration packet](../../research/2026-10-09-codex-conditional-bridge-1630z/bounded/README.md)
for exact pinned setup, complete request contract, examples and replay evidence.
The default launcher never installs dependencies or uses the network.

| Scoped outcome | Meaning |
|---|---|
| `CERTIFIED_SOURCE_WITNESS` | One strict source and physical assignment pass exact software recomputation for every supplied row |
| `CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS` | Exclusion inside the declared verified complete finite registry only |
| `UNKNOWN` | Missing provider/backend, exhausted bounded scan, or incomplete evidence; no unrestricted NO |
| `REFUSED_REQUEST` | Input violates the scoped contract |

These commands preserve shared parameters, original IDs and all supplied rows;
independently fitted rows are invalid. Certified results exit 0, UNKNOWN exits
2 and refused bounded requests exit 1. `RESULT.json` retains the full delegated
result as `component_result`, including actual backend/checker invocation,
coverage scope and execution receipts. This original-source path is distinct
from the nine-parameter clock-JC outer-cover command above and its optional
Rust diagnostic.

## Exact classical ordinary-forest coordinate

```sh
python3 -B applications/practical-solver/run.py forest-baseline --request research/2026-10-09-codex-conditional-bridge-1630z/graph/examples/one-ordinary-population.json --output /tmp/solver-forest-new
```

The example gives exact probability 7/192 for the specified four-label forest
at survival 1/2. The module counts compatible histories and exposes lazy
neighbours without constructing the full forest law. Its request uses
`ordinary_forest_request_v1`, a canonical forest, 1..64 labels and a strictly
interior exact rational survival with integer numerator/denominator of at most
256 bits. Success exits 0; refused input exits 2. It computes one ordinary
stochastic coordinate, and establishes no source fit or quantum advantage.
The optional Hermitian-dilation API specifies a different evolution and is not
used by this command. See the [graph packet](../../research/2026-10-09-codex-conditional-bridge-1630z/graph/README.md)
for API checks, classical cost measurements and remaining quantum costs.

Both delegated commands show `FRESH_COMPONENT_EXECUTION`, export readable
reports and preserve their exact scoped result and child logs under
`component/`. They use the same process limits and fresh-output safeguards.
Read the [limitations and failure recovery page](../../research/2026-10-09-codex-conditional-bridge-1630z/release/LIMITATIONS.md)
before interpreting any result as a scientific certificate.

## Native exact finite cells

The additive Rust component uses the same canonical RC1 requests and result
bytes as the executable Lean baseline. Build it with Rust 1.90 or later:

```sh
cargo build --locked --release --manifest-path research/2026-10-10-codex-lean-rust-parity/rust/Cargo.toml
python3 -B applications/practical-solver/run.py affine-cell --request research/2026-10-10-codex-lean-rust-parity/design/fixtures/two_tip_natural_cell.req --native-binary research/2026-10-10-codex-lean-rust-parity/rust/target/release/parity-solver --output /tmp/solver-affine-new
python3 -B applications/practical-solver/run.py natural-cell --request applications/practical-solver/examples/natural-cell.rc1 --native-binary research/2026-10-10-codex-lean-rust-parity/rust/target/release/parity-solver --output /tmp/solver-natural-cell-new
```

The result contains one exact vector satisfying every supplied affine row,
or nonnegative original-row multipliers proving that matrix infeasible.
The runner preserves the request and certificate, stages the executable,
and invokes both its native checker and a separately bounded exact rational
checker. An optional `--expected-binary-sha256` verifies a trusted executable
pin; without it, the digest is an observed identity.

`MATRIX_WITNESS` and `MATRIX_EXCLUSION` exit 0. Projection-budget exhaustion
returns `UNKNOWN` and exits 2. Refused requests and execution failures exit 1.
Reports retain `SOURCE_ADMISSION_NOT_ESTABLISHED`: supplying a matrix does not
validate an original graph/chart or exclude every source. See the
[exact contract and correspondence scope](../../research/2026-10-10-codex-lean-rust-parity/design/CONTRACT.md)
and [full solver obligation map](../../research/2026-10-10-codex-lean-rust-parity/design/TRACEABILITY.md).
The launcher uses a fresh output directory and preserves actual producer and
checker start records.

`natural-cell` accepts original vertex/edge/hybrid records, literal age
comparisons and exposure/coin intervals. It checks the finite rooted binary
graph predicate and compiles one shared bank: vertex ages, one inverse rate
per original edge, one ancestral inverse rate, and one coordinate per hybrid.
Returned physical rates are reciprocals of the positive inverse coordinates.
The independent checker regenerates the bank and matrix from the request
before checking the certificate. The example constrains a two-tip graph with
two exposures sharing its ancestral rate. Its result establishes feasibility
of those literal constraints; active-epoch interpretation and observation-law
admission remain unverified. The source gate stays in every result, including
exclusions. See the [chart contract](../../research/2026-10-10-codex-lean-rust-parity/design/CHART-CONTRACT.md).

## Full formal genealogy tables

`genealogy-law` computes the complete joint terminal genealogy table for a
supplied finite graph with one to four sampled copies. It preserves distinct
original edges, shared hybrid probabilities and the COMMON or INDEPENDENT
routing mechanism. The output includes rooted-tree polynomials and their
root-suppressed unrooted split probabilities. The native solver uses exact
rational polynomial coefficients.

The separate coefficient checker requires SymPy 1.14.0 and mpmath 1.3.0 in
the launcher's Python environment. These dependencies are used only by this
optional command. Prepare that environment explicitly if needed:

```sh
python3 -m pip install -r research/2026-10-10-codex-lean-rust-parity/rust/law_component_requirements.txt
python3 -B applications/practical-solver/run.py genealogy-law --request applications/practical-solver/examples/genealogy-law.rc1 --native-binary research/2026-10-10-codex-lean-rust-parity/rust/target/release/parity-solver --output /tmp/solver-genealogy-law-new
```

The example has a parallel-edge hybrid with two copies sharing a sampled
taxon. Success returns `FORMAL_GENEALOGY_TABLE` and exits 0 after native replay
and an independent comparison of every coefficient against the pinned
inherited joint-law compiler. History, state or polynomial-work budgets can
return `UNKNOWN` with exit 2; refusals and execution failures exit 1. Saved
evidence includes `component/TABLE.rc1`, separate checker logs, source
identities and observed scientific-runtime versions and origins.

These are formal survival-variable polynomials for the supplied graph. The
command does not yet certify their correspondence to a physical calendar,
observation data or a complete source catalogue. Source admission and
statistical confidence remain unestablished. See the
[LAW contract](../../research/2026-10-10-codex-lean-rust-parity/design/LAW-CONTRACT.md)
for exact input bounds, variable order and budget semantics.

## Supplied calendar and genealogy table

`calendar-law` connects the existing calendar compiler, finite-word evaluator
and ancestral completion. Its JSON request supplies the original graph,
sampled copies, vertex ages, one shared inverse-rate bank, hybrid probabilities,
COMMON/INDEPENDENT mechanisms and explicit work limits.

```sh
cargo build --locked --release --manifest-path research/2026-10-10-codex-lean-rust-parity/rust/calendar-cli/Cargo.toml
python3 -B applications/practical-solver/run.py calendar-law --request applications/practical-solver/examples/calendar-law.json --native-binary research/2026-10-10-codex-lean-rust-parity/rust/calendar-cli/target/release/calendar-solver --output /tmp/solver-calendar-new
```

The example has two tips and their complete calendar. The command preserves
the full ordered genealogy-state polynomial table, original registers,
literal range witnesses and exact calendar substitutions. Each `EXP_NEG`
coordinate records `exp(-duration / shared_inverse_rate)` symbolically.
The reference checker uses Python's standard library and a different
coefficient algorithm from the Rust producer.

`SUPPLIED_CALENDAR_TABLE` exits 0 after native replay and independent checks
of every coefficient, the agenda and physical substitutions. Bounded
`UNKNOWN` exits 2; refusals and execution failures exit 1. An inner provider's
UNKNOWN authenticates its request and limit frame; it does not establish
an independently proved exhaustion result or source exclusion. Saved artifacts
record exactly which checks ran. Existing fresh-output and optional executable
SHA-256 checks apply.

This is a forward calculation for supplied inputs. Source-census completeness,
observation-law admission, statistical confidence and full solver/policy
completion remain unestablished. See the
[calendar application contract](../../research/2026-10-10-codex-lean-rust-parity/design/CALENDAR-APPLICATION-CONTRACT-20261010T1458Z.md)
for the exact nine-field request, graph/copy limits and result scope.

## What the three examples mean

| Example | Expected checked result | Interpretation |
|---|---|---|
| `informative` | `CONDITIONAL_UNION_WIDTH_CERTIFIED`, maximum normalized width ≈0.00377180445 | Supplied near-exact arithmetic mean bands localize all nine widths below 1/20; observed-data accuracy is unverified |
| `finite-data` | `UNKNOWN_OUTER_COVER`, all nine union widths one | Archived 1,024-locus synthetic bands admit two sources separated by normalized rA=3/55>1/20; unchanged bands cannot meet the target |
| `unsupported` | `MODEL_NOT_ADMITTED`, solver not invoked | Marker-alignment model has no admitted mapping to this solver's source/observation contract |

The model uses labelled phased A1,A2,B1,B2,C1,C2 copies, two sites sharing one
genealogy per complete locus, a fixed backward B-to-C pulse, original shared
rates/pulse ties and stationary homogeneous clock-Jukes–Cantor observations.
Its physical parameters are h,u,v,rA,rB,rC,rAB,rR,g. All nine original domain
and width targets are preserved. Shifted Bernoulli-character means are
converted to raw parity exactly once by the inherited initializer.

The returned cover is an outer cover: a retained box can contain non-solutions.
Narrow width does not prove existence of a physical source witness. The app
does not issue statistical confidence or biological parameter accuracy. The
finite-data example preserves its historical bands; better inversion alone
cannot remove two truly compatible points. New data or changed statistics
need an explicit source, sampling and coverage justification.

## Fresh runs, saved evidence and separate checking

Fresh commands show a **Fresh run** banner and `execution_mode: FRESH_RUN`.
To display the inherited 8 October result without executing a solver:

```sh
python3 -B applications/practical-solver/run.py show --example informative --output /tmp/solver-saved-1
```

That report says **Saved results — no solver executed** and records its
historical source/hash. Generating a new report around a saved receipt is
not a new numerical run.

Recheck a fresh run using the separate whole-journal checker:

```sh
python3 -B applications/practical-solver/run.py check --run /tmp/solver-informative-1 --output /tmp/solver-recheck-1
```

The recheck authenticates the staged runtime against the package's inherited
pins and recomputes the journal. It has a separate execution/report. Invalid
numerical journals fall back conservatively; source/request identity errors
are explicit refusals. Hashes detect changes relative to trusted records;
they are not signatures or protection against an attacker who replaces the
entire package and its expected hashes.

## Invocation provenance and failure recovery

`solver_called` becomes true only after the producer process starts. Staging,
source authentication and process-creation failures leave it false. A launched
producer that exits unsuccessfully keeps it true. `checker_called` and
`diagnostic_called` track their separate process starts; a recheck launches
only the checker. Execution receipts record `process_started`, and failed
process creation preserves its error receipt.

`RESOURCE_OR_EXECUTION_FAILURE` is an execution failure and issues no new
numerical certificate. Inspect `RESULT.json` and the preserved stage logs;
restore trusted package bytes after an identity mismatch, or use a fresh
output directory after an interrupted run. Do not patch expected hashes to
make modified runtime files pass. A failed optional diagnostic leaves the
independently checked numerical result visible. More resource budget does not
resolve missing source coverage or finite-data ambiguity.

The [current correction and replay packet](../../research/2026-10-09-codex-conditional-bridge-1630z/release/README.md)
preserves the pre-dispatch defect, repaired positive and negative controls,
and current derivative identities. The earlier release packet and its byte
manifests describe historical source versions; they remain preserved.

Check the current application derivative's byte manifest from the repository root:

```sh
python3 -B research/2026-10-10-codex-lean-rust-parity/verify_derivative.py
```

This verifies the new derivative and the unchanged inherited bridge files;
it supplies no scientific or mathematical certification. The October 9
`verify_bridge.py` and earlier `verify_release.py` retain their historical
manifests and report the subsequently changed launcher/documentation bytes.

## Inputs and exported evidence

Copy an example JSON to prepare a request, then run:

```sh
python3 -B applications/practical-solver/run.py run --request /tmp/my-request.json --output /tmp/solver-request-1
```

Use the exact request schema and original model/domain/targets. Nine named
feature intervals use bounded rational strings, such as `"3/4"`. Floats,
duplicate JSON keys, malformed or excessive rationals, invalid intervals and
unsupported budgets fail with clear errors. Input is capped at 64 KiB; the
documented numerical budget is bounded. Each solver/checker/diagnostic child
uses a 30-second CPU cap, 45-second wall timeout, 512-MiB address-space limit
and 16-MiB per-file limit. Resource limits are conservative execution controls,
not a proof of universal practical termination or a continuous machine-wide
memory ceiling.

Exports include `REQUEST.json`, `RESULT.json`, `REPORT.html`, `REPORT.md`,
`SOURCE-IDENTITIES.json`, `CHECKER-PINS.json`, execution receipts/logs,
`journal/` and `ARTIFACTS.json`. Exact union widths are rational; displayed
decimals are only for reading. Every retained cell is exported. Child processes
receive a minimal environment without application credentials. Use stable,
trusted package files and avoid concurrent edits during a run.

## Optional Rust diagnostic and baseline reproduction

The default computes an authenticated Python pair diagnostic after checking.
Rust is optional and compares every ordered pair of checked cover cells with
that reference. It cannot change the cover, substitute for the producer or
establish a speedup. Diagnostic failure preserves the complete checker result.

Reproduce the pinned Rust 1.90.0 build and all 39 signed-nine differential
cases in new scratch (Python 3.11+, Linux x86_64, C/linker tools and network
needed for initial checksum-verified provisioning):

```sh
python3 -B research/2026-10-09-codex-practical-release-0207z/coordinator/native_replay.py --scratch /tmp/solver-native-1
python3 -B applications/practical-solver/run.py run --example informative --native-binary /tmp/solver-native-1/runtime/signed-target/release/signed-nine-probe --output /tmp/solver-native-demo-1
```

Provisioning uses public network downloads verified against official component
and Cargo.lock checksums; subsequent Cargo commands use `--locked --offline`.
Toolchains, dependency archives and binaries remain outside the repository.
The fresh release replay matched 39/39 cases, comprising 13 completed
geometries and 26 refusals, plus transport and row-cap controls. This is finite
native/reference compatibility evidence, not a universal arithmetic proof.

## Research report, review and original sources

The same entry point includes an optional offline molecular demonstration:

```sh
python3 -B applications/practical-solver/run.py molecular --output /tmp/solver-molecular-1
python3 -B applications/practical-solver-biology/ingestion.py
```

The molecular report compares matched REF/A/B/AB contexts with the inherited
deterministic synthetic provider. Expression, splicing and the derived
polyadenylation proxy remain separate. No network or credentials are used;
predictions do not become experimental validation or ancestry observations.
The **archived-panel audit** command (`ingestion.py`) freshly recounts the
pinned archived 1,024 loci, once-only mean conversion and exact 3/55
obstruction. It accepts no new panel, alignment or observation bands and
creates no new confidence event. Its result carries
`audit_kind: ARCHIVED_PANEL_AUDIT`; forward enclosures remain inherited
authenticated evidence, with containment freshly rechecked.

The [biological contract and official-source audit](../../research/2026-10-09-codex-practical-release-0207z/biology/BIOLOGICAL-INPUTS.md)
records current AlphaGenome SDK capabilities. Substantive current service terms
could not be retrieved beyond a shell/sign-in page; no acceptance is inferred.
Live activation remains separate: verify eligibility and terms, authorize the
account/data/budget and configure credentials through a secure environment or
secret manager. Do not send keys in chat or store them in reports or source.

Read the [full research report](../../research/2026-10-09-codex-practical-release-0207z/RESEARCH-REPORT.md),
[independent review](../../research/2026-10-09-codex-practical-release-0207z/validation/INDEPENDENT-REVIEW.md)
and [Nolan walkthrough](../../research/2026-10-09-codex-practical-release-0207z/validation/NOLAN-WALKTHROUGH.md).
The packet includes G1–G7/theorem-to-code contracts, biological assumptions,
method comparison, source/version manifests, fresh receipts and preserved
failed attempts. The [inherited baseline](../../research/2026-10-08-codex-integration-0825z/practical/README.md)
retains original provenance, mathematical results and source pins.

General G3/G4 and useful admitted finite-data all-nine localization remain
open. Neither is hidden by the application. Owned code follows the parent
[Apache 2.0 license](../LICENSE); external data, libraries and service outputs
retain their own terms. No live service or deployment is activated.
