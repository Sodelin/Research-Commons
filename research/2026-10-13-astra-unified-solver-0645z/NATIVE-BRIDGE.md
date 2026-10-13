# Recovered native solver and joint forward-law entry

**Tested component.** `native_bridge.py` exposes the existing recovered Rust
executable through the unified solver's `native_rc1` task. It preserves the
literal canonical RC1 request bytes and delegates solving, native source parsing,
and certificate checking to the frozen implementation. It does not add a new
Rust solver or claim that a formal source graph has a physically admitted image.

```json
{
  "schema": "unified_research_solver_v1",
  "task": "native_rc1",
  "input": {
    "schema": "native_rc1_operation_v1",
    "operation": "solve",
    "request": "RC1 AFFINE 1 2 1\nLT 0/1 -1/1\nLT 1/1 1/1\n"
  }
}
```

The Python API is
`native_bridge.consume(input, fresh_output_directory, binary, restored_sources)`.
Runtime paths are separate process configuration. The mathematical request
accepts no caller-provided proof/admission flags. `operation: "check"` requires
one additional `certificate` field containing a literal RC1 result. The exact
native checker binds this certificate to every byte of the request.

## Accepted operations and conclusions

| RC1 operation/result | Facade result | Exact conclusion |
| --- | --- | --- |
| `AFFINE`, `SAT` | `CERTIFIED_AFFINE_WITNESS` | One exact rational vector satisfies all original weak/strict affine rows jointly. |
| `AFFINE`, `UNSAT` | `CERTIFIED_AFFINE_EXCLUSION` | Checked nonnegative original-row multipliers give a contradictory bound for that supplied finite matrix. |
| `LAW`, `TABLE` | `CHECKED_SYMBOLIC_FORWARD_TABLE` | Complete formal joint terminal rooted-genealogy polynomial table and root-suppressed unrooted pushforward for the supplied bounded graph/sample/mechanism. |
| Either budget exhaustion | `UNKNOWN` | No feasibility or exclusion conclusion follows. |
| Malformed/unsupported input, wrong certificate or runtime identity | `REFUSED_REQUEST` | The operation is not certified. |
| Missing runtime or execution/time/resource failure | `UNKNOWN` | No mathematical negative conclusion follows. |

Every result reports `source_feasibility_certified: false` and
`unknown_size_exclusion_certified: false`. An affine matrix witness or exclusion
is scoped to that matrix. The existing actual-source backend remains the route
for a source witness. `CHART` and `COUNT` are not silently admitted by this new
facade; their earlier interfaces and certificates retain their own contracts.

For `AFFINE`, all rows share the same ordered vector. The selected native
checker verifies original-row evaluations or Farkas multipliers without running
the Fourier–Motzkin solver. `LAW` checking re-executes the **same** bounded joint
compiler; it is explicitly recorded as replay, not an independent law algorithm.
Existing older Python coefficient-checking adapters remain available at the
immutable recovery branch and are not claimed executed by this facade.

The two operations distinguish mathematical uncertainty from certificate
acceptance. `solve` preserves budget exhaustion as `UNKNOWN`. Supplying that
UNKNOWN output to `check` receives `REFUSED_REQUEST` because UNKNOWN is not a
feasibility or exclusion certificate; the result explicitly retains
`mathematical_decision: "UNKNOWN"` and `certificate_checked: false`. The native
checker deliberately rejects such inputs. This is a refusal to certify an
answer, not a mathematical NO. The original UNKNOWN budget statement itself is
not authenticated as a separate certificate. Any unexpected future acceptance
of UNKNOWN by the checker is guarded and still cannot become a positive result.

## Source and arithmetic contracts

RC1 uses canonical ASCII framing with one final newline, single spaces and exact
canonical rational `p/q` tokens where numbers occur. The Rust parser rejects
nonreduced fractions, floating-point notation, signed zero, malformed references,
duplicate/incorrect record ordinals, and inconsistent source structure. Input
rational magnitudes are bounded by 256 bits before exact arithmetic; intermediate
rationals are exact. The request limit is 65,536 bytes and the certificate limit
is 4 MiB. The unified JSON transport may impose its own tighter outer byte cap.

`AFFINE` allows up to eight coordinates, 64 original rows, and a projected-row
budget up to 4,096. The three affine examples demonstrate a witness, a strict
contradiction on the same shared coordinate, and explicit budget UNKNOWN.

`LAW` uses existing consecutive integer vertex, edge-occurrence, leaf, hybrid,
and sample-copy IDs. The facade forwards them without sorting, merging parallel
edges, relabeling sample copies, or introducing independent marginal products.
The graph caps are 32 vertices/edges and 32 combined bank coordinates; sample
copy count is 1–4. The declared caps are at most 4,096 states, 65,536 terms and
4,096 histories. Source structural validation belongs to the selected native
implementation; it is not a proof of its correspondence to Lean admission.

The ordered formal variable registry is `X:0 ... X:(edges-1)` followed by
`G:0 ... G:(hybrids-1)`. `X` are formal survival variables, not automatically
natural physical images. At a COMMON hybrid, all current lineages take the same
parent occurrence; INDEPENDENT routes them according to separate factors in
that existing mechanism. The original parent occurrence order is retained.
Each output tree is on the local sample-copy IDs. Arbitrary external global
labels from the separately tested snapshot decoder are not a feature of this
RC1 LAW wire. Full joint calendar/history readout and observation-law admission
are not inferred from a terminal formal table.

`examples/native-forward-fork.json` has two sample copies on leaf 0 and one on
leaf 1. The complete rooted table is checked against the independently stated
small formula:

* `((0,1),2)`: `1 - 2*X:0/3`;
* `((0,2),1)`: `X:0/3`;
* `(0,(1,2))`: `X:0/3`.

The two parallel-edge examples preserve distinct occurrences `EDGE 2` and
`EDGE 3` feeding the same hybrid. Both COMMON and INDEPENDENT mechanisms are
tested under their respective native contracts; neither is used to extend the
new conditional COMMON bounded-representative theorem to INDEPENDENT inputs.

## Authenticated reuse, actual execution and limits

The facade requires the exact observed executable SHA-256
`235520d47eaa95873729f2aa60b6f596f41859f1b1807ee58aeb1bd2ab0f876a`, the complete
recovered 51-file source inventory hash
`c5c84b5fa1755ae05830059353c184a77c52bd236b4053fe2668e6e30f066da6`, every selected
file hash, and the two successful core/population build receipts. Those pin the
25 historical decoder-related inputs and the precise compiler selection.
The controlled build/source relationship is an observed execution claim with
the compiler trusted; hashing is not a formal source-to-binary proof or signature.
A fresh build producing different bytes requires explicit review/update of the
runtime selection, rather than an arbitrary caller-asserted replacement hash.

One read of the authenticated binary is staged into an owned temporary directory
before execution. Only that temporary executable is cleaned up. Request,
response, native stdout/stderr, command, exit code, input/output identities and
per-child receipts remain in the result directory. Each native process has
128 MiB address-space, eight CPU seconds, ten wall seconds, eight MiB per-output
file, no core dump, and stays in the enclosing `guard.py` process group. No
native compilation occurs in this facade; it reuses the just-built exact binary.

`evidence/native-cli-help` records inspection of the real executable interface.
`evidence/native-bridge-first` records the initial six passing test groups.
`evidence/native-bridge-preserved` records six passing groups after adding
pre-encoding length checks and durable per-case evidence. Its `cases` tree
contains actual solve/check outputs for exact matrix witnesses/exclusions,
the known fork law, both parallel-edge mechanisms, malformed source/transport,
mutated coefficients, request substitutions, missing runtimes and wrong pins.
The final suite consumed approximately 21 MiB peak child RSS and 0.5 seconds;
there was no resource-pressure stop.

`evidence/native-bridge-unknown-review` adds explicit regression checks for both
AFFINE and LAW UNKNOWN outputs submitted as certificates. They remain
mathematically UNKNOWN while certificate acceptance is refused, with no
source-feasibility or exclusion claim.

These finite controls do not prove universal native correctness. Rust compiler,
exact arithmetic libraries, OS execution, Python framing and hashing, and native
to Lean semantic correspondence remain trusted boundaries. No new axiom,
caller-admission flag, physical source inference, or unknown-size exclusion is
introduced by the entry point.
