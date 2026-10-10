# Supplied-fit component: optional attributed coefficient reference

Contributor: `/root/rust_implementation`, 10 October 2026, 22:28 UTC.
Status: implementation and static syntax review; derivative execution pending
the sole scheduler. This extends the [native-only contract](SOURCE-FIT-COMPONENT-CONTRACT-20261010T2216Z.md).
The exact native-only adapter is preserved in
`rust/evidence/source-fit-component-freeze-1/native_source_fit_component.py`,
SHA256 `6f02d176aaa25a723796496a01ebdaafd5b4b842a4853f94befd419133a0f2ff`.
Its six application controls passed separately in the preserved receipt
`rust/evidence/source-fit-application-native-controls-20261010T222259.832312Z/FINAL-RECEIPT.json`,
SHA256 `68ba3f1c205300957b8d8b1fe306c99b19306446300a81d22cc13c1d0ffa76d0`.
Neither receipt establishes this derivative's execution.

The current adapter adds `--reference-python PATH` for readout only. Omitting
that option preserves the native-only execution/status contract, with both
`independent_all_coefficients_checked` and `independent_probabilities_checked`
false. Bank mode rejects the reference option. Root owns application dispatch,
documentation and derivative pins; no accepted core, frontend, old adapter or
helper source is changed by this contribution.

Four text sources are captured and hash checked before use:

| Source | SHA256 |
| --- | --- |
| `design/certificate_check.py` | `ec55b12c10b8e5fd2eec29f72b4d14138b57d84139239e04e0c8907602e58e24` |
| `design/chart_check.py` | `3de5f13954f6aa40b53c0cf5a8b57d8895046becfd36989087fb6ec0748b5e8a` |
| `design/source_fit_reference.py` | `0eedff2d9ab21514e3788ae5f9310e33bd57d8ce86e4cf038bb08520ccd99fc6` |
| inherited `research/2026-10-01-g7-continuous-design/law_compiler.py` | `eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7` |

The adapter imports no scientific backend and executes no helper/provider in
its parent process. A self-contained staged bootstrap registers the exact
captured base/chart/helper modules. It runs with the supplied Python's `-I -B`
options in a separate bounded process, after the native replay accepts. Mutable
provider fallback is disabled by an explicitly absent staging path. Only TABLE
installs the captured provider with its authenticated `install_baseline` API.
Only TABLE loads the required SymPy 1.14.0/mpmath 1.3.0 backend. UNKNOWN and
UNSUPPORTED retain lazy frame-only checking without those imports.

The verifier reconstructs every natural rooted whole-edge polynomial using
the attributed complete frontier compiler, including original occurrence IDs,
shared old inheritance assignment and numeric global copied-label embedding.
It also checks each supplied trace equation at the same rational assignment,
every exact probability and identical polynomial normalization. It does not
generate or authenticate observation equations. In particular, satisfying an
untrusted supplied zero trace is not proof of a fitted admitted source.

Successful TABLE requires the real reference process to start and exit0, a
`source_fit_reference_check_v1` result with `result_valid`, matching native
status, raw request and raw response SHA256, the pinned baseline SHA, and true
`baseline_called`, `independent_all_coefficients_checked`,
`independent_probabilities_checked` and `supplied_trace_arithmetic_checked`.
The complete captured/staged source, interpreter, native executable, request and
result identities are rechecked before component success. These four TABLE
flags become false for frame-only checks. `reference_checker_called` measures
actual process start; `reference_baseline_called` distinguishes actual backend
use. The separate process receipt and `reference_result_sha256` preserve stdout
identity even on failure.

A selected reference that cannot start, times out, rejects, changes bindings,
uses another backend version, or omits required flags cannot yield native-only
success. It becomes RESOURCE_OR_EXECUTION_FAILURE, exit1. A missing interpreter
is the same execution failure before native processes begin. A valid checked
UNKNOWN/UNSUPPORTED remains exit2 with no table, exclusion or exhaustion claim.
The helper verification process itself exits0 when it accepts such a frame; the
native status and its exit2 are passed separately and checked exactly.

`provider_work_checked`, `provider_exhaustion_verified`,
`bank_metadata_independently_checked` and helper `resource_exhaustion_verified`
remain false. Every source-admission/provenance/observation-fit/timed/full-Code/
universal-native-refinement/certificate/full-solver/confidence/census flag remains
false. Gamma orientation remains original P(parent1)=1−old P(parent0), with
original incoming occurrences retained; no new forced-control CLI is exposed.

Runtime evidence records requested and resolved interpreter paths/hash, actual
child version/executable hash, and, for TABLE only, package versions/origins and
initializer hashes. These are observed identities, not a trusted interpreter
pin or verification of the entire third-party runtime. The existing limits
apply independently to the new child: 30 CPU seconds, 45 wall seconds, 512MiB
address space and 16MiB per output file. Request64KiB and result4MiB remain.
Linux session handling is reused; no portable sandbox or arbitrary descendant
containment theorem is claimed.

New outputs include captured reference text, the byte-embedded bootstrap,
reference stdout/stderr/execution receipt, `REFERENCE-RUNTIME.json` and accepted
`REFERENCE-CHECK.json`. Output directories remain create-new. Existing evidence
is preserved. The focused new runtime controls are the three exact asymmetric/
permuted fixture tables, prelaunch missing interpreter, postlaunch failed
interpreter, frame-only zero-equation-cap UNKNOWN and a fake native producer/
replay whose balanced coefficient forgery preserves fitted probabilities and
total mass. These are distinct from the design helper's saved-output controls.
No old 117-case/native/compiler sweep is requested for unchanged binaries.

The scheduler may additionally supply `--four-copy-request` to the focused
harness, using the design's input-only ordinary fork fixture
`design/fixtures/source-fit-reference-four-copy-fork.request.json`, SHA256
`b5e8cede35e35568e01a085f058574332fd16d59da32e780511f657f9a4e5341`.
It exercises the declared four-copy boundary with permuted/large global labels;
its explicitly supplied zero trace establishes no observation-fit provenance.
No expected/native/reference table had been produced when that input was frozen.
