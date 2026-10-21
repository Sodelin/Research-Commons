**Execution hold:** prior hosted jobs persisted synthetic runtime traces in plaintext. New CI launches are disabled pending the existing encrypted-writer binding required before first persistence. See RECORD-WRITER-GAP.md. Mathematical/behavioral results below remain observed with that record-policy limitation; the full goal stays active.

# Rational candidate-support acquisition for the Lean/Rust solver

The native proposer, original Python certificate checker/emitter, unchanged
runtime and unchanged stdio MCP connector passed actual ONLINE verification in
[run 39673487466](https://github.com/Sodelin/Research-Commons/actions/runs/39673487466).
The source tested was 73ff92d4b768e929309a24da773d20a2c63199bc. The corresponding
[Lean source packet](https://github.com/Sodelin/Research-Commons/pull/3) was
independently read and matched byte-for-byte; its hosted Lean checking is
attributed peer evidence. See PUBLICATION.md and evidence/.

For r=1,2,3 proposed distinct rational values in (0,1], the native component
accepts exactly 2r+1 moments at exponents 0,1,3,...,r(2r+1). It constructs an
exact sparse polynomial with double zeros at the candidates, checks a
nonnegative rational quotient, emits the ORIGINAL weighted-square certificate
wire, and invokes the inherited exact checker before returning
GENERATED_AND_CHECKED.

Candidate nodes are auxiliary proposals. The old check_certificate task
independently validates the output. Candidate failure or rational/output bound
exhaustion returns UNKNOWN; malformed or domain-invalid input returns REFUSED.
The conservative old support cap remains L-1=2r. Physical source existence,
general all-input search and a formal native refinement are separate obligations.

## Reused components and ownership

The base is Research-Commons commit
1138a5b1a281caa00b38e0976db95b586938754b.

- rust/src/main.rs preserves the old exact parser, arithmetic, checker and
  singleton generator from research/2026-10-13-astra-unified-solver-0645z.
  Only module registration and one dispatch arm are inserted.
- The established exact-count-certificate path dependency and existing num-*
  versions/checksums are reused. The root package alone is renamed in the lock.
  Locked fetch, then offline test/build, passed with official Rust1.90.0.
- certificates.py, emit_lean.py, solve.py, the newer
  research/2026-10-13-astra-unified-runtime-2350z/runtime.py and
  applications/research-solver-interop are unchanged.
  applications/practical-solver is a distinct nine-parameter contract.
- The existing weighted-square Lean library and literal emitter are unchanged.
  The accepted general CM-T02 sparse-moment component at
  514648b697aeed8f46582109cfeefcd7707cd738 retains its original scope.

This proposal owns this directory and its uniquely named Rust CI workflow.
The existing Lean builder owns compiler/package assembly. Other research owners
and original G3/G4/P1/P5 completion standards remain in place. No local Git
writes, phone project checkout/build, new chat or sub-agent was used.

## Exact finite rational bank candidate

BANK-INTERFACE.md specifies a separate common-bank-moments executable plus
request-bound Python verification. It removes only zero masses, combines equal
rational values and derives all triangular moments from ONE law. When its
shape fits r<=3, it emits the existing acquisition request. [Run39675913869](https://github.com/Sodelin/Research-Commons/actions/runs/39675913869)
compiled it and passed194 banks/reversals,17refusals,onegrowth UNKNOWN,eight
codec negatives,eight actual CLI calls and both old-runtime fixture chains.
Its actual new binary identity and authenticated evidence are in evidence/bank-39675913869/. The existing proposer/main and interfaces stay
unchanged. No physical source admission or arbitrary-real computability follows.

## Input/output and reproducible execution

rust/src/support.rs implements acquisition. codec.py is strict transport:
JSON to native wire, then request-bound native stdout to the original
unified_research_solver_v1/check_certificate request. It authenticates and
executes the original Python checker source. It does not spawn the native
process or change certificate semantics. Literal moment spellings are retained.

fixtures/two-acquisition.json has candidates 1/3,2/3 and moments
(1,1/2,1/6,65/1458,1025/118098). fixtures/two-check-request.json and
fixtures/three-check-request.json are exact old-schema certificate inputs.
Both corresponding standalone Lean outputs are retained in generated/.

The bounded ONLINE workflow .github/workflows/rust-support-proposal.yml is the
reproducible execution recipe. Its essential native commands, from repo root:

    cargo test --locked --offline --manifest-path research/2026-10-21-lean-rust-solver-builder/rust/Cargo.toml
    cargo build --release --locked --offline --manifest-path research/2026-10-21-lean-rust-solver-builder/rust/Cargo.toml
    python3 -B research/2026-10-21-lean-rust-solver-builder/codec.py encode --repository . < research/2026-10-21-lean-rust-solver-builder/fixtures/two-acquisition.json

Feed the encoded wire to the fresh common-support-proposer binary. Decode its
complete stdout with codec.py decode --repository . --request followed by the
full acquisition fixture path. Submit that JSON through the original runtime
or MCP research_solver_run request_json interface. ci_verify.py and
ci_connector.py retain the actual commands and checks.

The new executable is an unadopted proposer. Passing it as a canonical
--rust-binary correctly returned authenticated UNKNOWN without executing it;
no whitelist was changed.

## Verification and resource scope

The final job passed 13 native unit groups, 556 unchanged original checker
cases, 158 new-binary/original-Python singleton cases, 205 acquisition cases,
12 codec negative controls, four actual codec CLI calls, direct original
runtime calls and six run calls through two real stdio MCP servers.
Results, refusals, UNKNOWN and authentication were checked separately.

The independent V8 BigInt reference covered the same 205 acquisition inputs,
252 false-certificate mutations and 84 node-order reversal pairs. Those counts
overlap the native checks and are not independently proved theorem counts.
Historical accepted executables were not replayed.

The serial hosted job has a 10-minute wall bound, read-only checkout token,
locked dependencies and scoped cleanup. hosted_guard.py resolves the actual
mounted cgroup membership and reuses the original guard's loop, thresholds,
floors and process cleanup. It does not claim a whole-machine 4GiB limit.
The unchanged MCP bridge runs in a fresh network-none, read-only-source,
2GiB/one-CPU/128-process Docker container. The final run asserted the actual
kernel limits, read-only mount, loopback-only networking, no-new-privileges and
zero effective capabilities. Its original guard counter existed inside that
namespace. Public synthetic fixtures contain no private phone records.

Two exact emitted-source hashes match all six direct/runtime/MCP instances and
the peer's published hosted Lean documents. That hosted context is Lean4.35.0,
Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679. Pinned Lean4.33.1 standalone
imports/Lake objects, the full package aggregate and canonical adoption remain
OPEN. Earlier failures and their corrective source commits are retained.

The exact executed Linux x86_64 objects are available in the authenticated
online bundle described by NATIVE-CUSTODY.md. PROPOSED-NATIVE-PROFILE.json pins
their auxiliary role and complete input/output route; canonical adoption and
new public API tasks are not supplied by that descriptor.

MOMENT-PROVENANCE.md proposes explicit mathematical-law provenance and separate
literal-request, scalar-law and L/order-sensitive moment identities. This NEW
metadata extension is source-only and unexecuted under the writer hold; earlier
jobs cover the recorded baseline, not the extension. The old certificate input
and native binaries remain unchanged.

## Literal bank Lean receiver source

LITERAL-BANK-LEAN.md and emit_bank_lean.py prepare a per-input all-exponent
raw-row/grouped-law witness against the peer's existing CM constructor. Both
literal fixtures and the Python emitter are UNEXECUTED source preparation.
Their exact source hashes are retained; the existing workflow stays disabled.

## Mathematical boundary

PROOF.md gives output soundness. The checked Lean finite_supported_bank theorem
requires one shared finite law and every literal moment equality. It concludes
that each positive-weight atom is a polynomial root in (0,1]. It supplies no
physical source admission or sharper r support cap. Independent routing, masks
or row-by-row fitted physical tuples cannot be pooled into one law by naming
the same bank.

OBLIGATIONS.md retains the remaining gates. Full G1/G2/binary-M3 G5 recovery,
G6/G7 assembly and original G3/G4 termination/forcing are separate master work.
