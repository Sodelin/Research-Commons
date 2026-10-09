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
contains exact bounds and the complete retained solution cover. Defaults save
under `runs/`; choose explicit fresh directories for reproducible demonstrations:

```sh
python3 -B applications/practical-solver/run.py run --example informative --output /tmp/solver-informative-1
python3 -B applications/practical-solver/run.py run --example finite-data --output /tmp/solver-finite-1
python3 -B applications/practical-solver/run.py run --example unsupported --output /tmp/solver-refusal-1
```

Output directories must be absent. Reusing a path is refused to preserve
previous results. Paths shown here are examples; use new names for later runs.

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
The input audit freshly recounts the archived loci, once-only mean conversion
and exact 3/55 obstruction without issuing scientific confidence.

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
