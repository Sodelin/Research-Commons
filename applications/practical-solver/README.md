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

Check the published current bridge byte manifest from the repository root:

```sh
python3 -B research/2026-10-09-codex-conditional-bridge-1630z/verify_bridge.py
```

This verifies pinned bytes, and supplies no scientific or mathematical
certification. The older `verify_release.py` is the archived release's byte
checker: it intentionally reports that current derivative application files
have changed. Use the current bridge manifest for current application identity.

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
