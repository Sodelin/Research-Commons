# Existing Rust contracts and integration boundary

Source/evidence audit by Astra / Codex integration lead, 13 October 2026.
No Rust compiler or native test ran in this execution. The exact available
decoder/test bodies, embedded receipts and arithmetic source pins were checked
by `audit_intake.py`. References below keep the inherited program contracts;
they do not identify them as a complete supplied-certificate recognizer.

## Canonical snapshot decoder

Existing source: [source_native_snapshot.rs](../2026-10-10-codex-lean-rust-parity/rust/proposals/canonical-snapshot-decoder-20261011T0905Z/source_native_snapshot.rs),
SHA256 `37a00f8767af2a0002970e7a59d046861c4c8601f65c46fe0e86650694c6e318`.
It reuses `parity_solver`'s `Context::validate_snapshot` via `selected_view`.

| Operation | Accepts / computes | Refuses / does not certify |
| --- | --- | --- |
| `decode_snapshot(context,input)` | A supplied native canonical liveSome/deadNone Snapshot under the existing bounded Context. Returns typed local Copy/Vertex/Edge IDs, ordered genealogy, ancestor map, full original V register, selected value, dead Leaf(i)/Node(root) defaults and an explicitly empty event history. | Malformed native snapshots and out-of-range identities return Error. It does not parse arbitrary source text, admit a scientific graph, recover prior event history or prove a native/Lean refinement. |
| `canonical_snapshot()` | Re-encodes the canonical image while retaining live membership and ordered trees. | Does not cover every typed Lean Code with dead garbage/activeNone. |
| `original_parent_edge` / `original_hybrid_vertex` | Retains parallel edge occurrences and original V slots; true selects incoming[1], the original Gamma convention. | No new coin draw, parameter inference or silent old-parent0-g conversion. |
| `check_selected_range` | A validated witness whose complete Copy/Copy/V selected vectors equal the claimed value. | Wrong shape/value returns Error. A matching selected value proves neither unique state nor a literal history endpoint. |

Copy≤4 and graph counts≤32 are native implementation domains, not source-size
theorems. Large global labels stay distinct from bounded local Copy leaves.
This borrowed-value API has no numerical UNKNOWN protocol; malformed values
return an API Error. Caller allocation/destruction and source parsing remain
outside it.

The published execution packet contains an actual compile receipt and tests
receipt, both exit0, with three targeted test heads. This intake authenticated
all embedded bytes and matched the public decoder/test files to them. Their
source-admission, literal-Code-history, timed-history and universal-refinement
flags remain false. There is no need to implement a replacement decoder.

## Serial full-history evidence and exact repair

The source-only [SPEC](../2026-10-10-codex-lean-rust-parity/rust/proposals/serial-full-history-control-20261011T0715Z/SPEC.md)
has a **later executed successor receipt** inside
[FULL-CONTINUATION-EVIDENCE-PACKET-20261011T0718Z.json](../2026-10-10-codex-lean-rust-parity/quality/FULL-CONTINUATION-EVIDENCE-PACKET-20261011T0718Z.json).
The envelope expands to 1,797,302 exact bytes, SHA256
`2b85f01030c4f8cbc4e63d855dc36621ae6783a77fa6dd9aec10e750a3bc5993`.
The actual test source is `82fd059e3b813e6d1c9b65de03c8f15037d5d6d9ab15be8b51687160e2f98cb7`.

The compile and test processes both exited0. The one head checks twenty full
records, seven positions each and 81 signed coefficients. Early and late
mergers have equal endpoints but distinct histories. Expected polynomials are
independently expanded signed exponent maps, preserving original parallel
occurrences, once-drawn bank bits and shared variables. This is a useful finite
control against endpoint-only merging.

The original outer wrapper nevertheless recorded failure: it expected
`running 1 tests`, whereas Rust printed `running 1 test`. The additive
postcapture correction checked the actual stdout and source/input pins,
preserved the failed outer receipt and did **not** rerun native code. A future
v3 repair was syntactically malformed and unexecuted; v4 fixed the singular
summary but also was not the executed wrapper. Only v2 executed. The intake
preserves this distinction, rather than relabelling the original run wholesale.
Exact receipt identities and correction status are in [INTAKE.json](evidence/INTAKE.json).

## Numerical and certificate interfaces already available

| Existing component | Exact contract | Outcome boundary |
| --- | --- | --- |
| [Count pilot](../2026-10-07-rust-count-pilot/src/lib.rs) | BigRational/BigUint normalized Poisson-prefix recurrence; a≥0, 0<epsilon<1; return first K satisfying the cutoff and tail inequalities, or exact inspected-cutoff exhaustion. Rational CLI integers/fractions/decimals are parsed exactly under its bounded ASCII grammar. | `CERTIFIED` is this normalized-prefix/tail certificate. `RESOURCE_LIMIT` is not mathematical NO. `None` max_steps is unbounded search, not a resource guarantee. This is not the sparse polynomial annihilator certificate needed by the new COMMON consumer. |
| [Interval baseline](../2026-10-08-cloud-rust-interval-root-0000z/src/lib.rs) | Exact rational arithmetic between explicit outward-dyadic rounding sites, context identity, pre-rounding reduced bit limits and charged exponential calls. Receiver and forward parsers have different documented grammars/budgets. | A valid enclosure does not establish exact zero, exact finite attainment, physical admission or a YES source witness. Protocol/domain/resource refusals keep their separate meanings. |
| [Signed-nine diagnostic](../2026-10-08-cloud-rust-signed-nine-0008z/src/lib.rs) | Ordered interval boxes under one context; signed residual/normalized pair-width geometry. | `CONDITIONAL_PAIR_WIDTH_CERTIFIED` only when the implemented maximum is strictly below1/20; otherwise `UNKNOWN`. It does not replace the complete-journal checker or change its outer cover. |
| [Later opt-in exponential cache](../2026-10-11-codex-practical-exp-cache-2140z/README.md) | Existing bounded FIFO cache of successful plain exact values keyed by canonical argument, precision and policy; semantic context/domain/budget checks and two-call charging remain before hits. | An existing tested experiment, not a new proposal or deployed acceleration. Reuse only at this contract. No parallel build/cache rewrite is warranted here. |

The count packet retains 1,693 differential cases, malformed-input checks and
checker mutations. The interval packet's later run retains 3,048 exact matches,
including 803 kernel refusals and 44 protocol guards, superseding its earlier
failed-fixture handoff. This intake matched their current sources with the
recorded pins and checked the interval wire-stream identities. It did not
rerun those binaries or independently rederive every corpus expectation.
The cache successor reports 18 controls and three rejected mutations plus
cached/uncached corpus equality; it was read here but not independently replayed.

The existing locked num-bigint/num-rational/num-integer/num-traits methods should
be retained where their contracts fit. Floating-point estimates never discharge
the exact sparse zero identity. No new exact-coefficient language, polynomial
nonnegativity checker or physical feasibility solver is implemented by this
handoff. Failure to supply/check such a certificate leaves recognition UNKNOWN.

## Correspondence and remaining trusted boundaries

R0 still requires an actual admitted RootedBinary source and registry, with
index bijections binding every native edge occurrence, hybrid role, root,
sample and shared parameter. Native validation is not that witness.
R1 must prove fieldwise correspondence of the native canonical decoder to the
selected `FiniteSourceSnapshot.decodeSnapshot`, including exact defaults and
constructor tags. The exact selected target source is SHA256
`4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744`;
its definition and existing encode/decode theorems were read directly. All
seven typed parent sources/import lists pinned by the native decoder freeze
match selected1613; [INTAKE.json](evidence/INTAKE.json) records them. These
existing Lean theorems concern Lean values, not the Rust translation.
R2 is exact coefficient/variable correspondence; R3 is
whole-history DAG induction and fibre sums; R4 is physical bank/calendar/order
and erased observation correspondence. Finite tests do not prove these for all
program executions or permitted inputs.

Lean's kernel, specified standard axioms, exact selected dependencies and
compiler/native import mechanism remain explicit formal trust boundaries.
Rust's compiler/linker/runtime, dependency libraries, parser, source binding,
allocation/error handling and unproved translation remain native boundaries.
Hashes authenticate bytes, not semantics. An exact numerical certificate also
requires an authenticated checker and binding to the same source/request/IDs.

The original private `parity_solver`/`calendar_cli` library context and toolchain
used by the historical snapshot/history tests are not present here. Historical
rlib pins do not recreate their source/dependency contracts. Recover them in
their authorized private repository and authenticate exact versions before any
new native run; do not publish private implementation or compile against a
stub. Toolchain provisioning alone does not remove that gap or the Lean1614
provider blocker. No private files were changed or uploaded in this task.
