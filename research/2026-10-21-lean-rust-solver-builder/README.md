# Rational candidate-support acquisition for the existing Lean/Rust solver

Status: ONLINE SOURCE PROPOSAL; JavaScript exact-reference experiments passed;
Rust, Python transport, original Python replay and emitted Lean verification
remain pending. No solver profile, whitelist or canonical implementation changed.

This extends the useful native acquisition boundary beyond the existing
singleton rule. For r=1,2,3 proposed distinct rational survival values in (0,1],
the proposer accepts exactly 2r+1 supplied moments at exponents
0,1,3,...,r(2r+1). It constructs an exact sparse polynomial with a double
zero at each proposed node, checks a nonnegative rational quotient, emits
the ORIGINAL weighted-square certificate wire, and calls the inherited exact
checker before returning GENERATED_AND_CHECKED.

The supplied nodes are auxiliary proposals. They are not additional measured
observations, inferred physical parameters or certified source realizers.
The unchanged check_certificate task independently checks the result and
the unchanged Lean emitter can generate its conditional finite-bank proof.
An unsuccessful candidate, rational-growth bound or output-language bound is
UNKNOWN. Malformed/domain-invalid input is REFUSED. Neither result is global NO.

## Existing components reused

Base: Sodelin/Research-Commons commit
1138a5b1a281caa00b38e0976db95b586938754b.

- research/2026-10-13-astra-unified-solver-0645z/rust/src/main.rs:
  the exact parser, rational arithmetic, weighted-square checker and singleton
  generator are preserved in the derivative. Only support-module registration
  and one new dispatch arm are inserted. The original eight unit groups remain.
- The established exact-count-certificate path dependency and the exact existing
  num-* dependency versions/checksums are reused. The source-only Cargo lock
  derivative renames only the root package; Cargo validation has not run.
- certificates.py, emit_lean.py, solve.py and the newer
  research/2026-10-13-astra-unified-runtime-2350z/runtime.py are unchanged.
  applications/research-solver-interop remains the connected MCP entrypoint.
  applications/practical-solver is a separate nine-parameter contract.
- Astra.CommonCertificateKernel supplies squareTerm_nonnegative,
  square_identity_nonnegative and supported_atom_is_root. Its historical
  compilation is not a fresh proof for these new generated inputs.
- The accepted CM-T02 component at
  514648b697aeed8f46582109cfeefcd7707cd738 retains its general sparse-moment
  theorem and distinct cap-five application. It is not a native-refinement or
  physical-source-admission certificate.

The proposal owns only this new directory. Existing source/compiler/runtime
owners, old failed and consumed jobs, and mathematical research lanes remain
separate. No extra chat or sub-agent was created. No project source, Git
checkout, build or test artifacts were written on the phone.

## Files and reproducible input/output

rust/src/support.rs is the native implementation. rust/src/main.rs is the
explicit derivative of the pinned existing checker. codec.py only transports
strict JSON to native wire and request-bound native output back to the original
check_certificate request. It starts no child and changes no solver semantics.
It executes only the captured, SHA256-authenticated original checker source.
The original literal moment spellings must match when decoding.

fixtures/two-acquisition.json supplies candidates1/3,2/3 and the synthetic exact
moment vector (1,1/2,1/6,65/1458,1025/118098), obtained from equal weights.
fixtures/two-check-request.json is a concrete original-schema receiver input.
fixtures/two-certificate.wire is the exact corresponding original checker wire.
fixtures/three-check-request.json is a separate seven-moment example.

Under a NEW separately admitted ONLINE execution scope, from the repository
root, the exact component commands are:

    cargo test --locked --offline --manifest-path research/2026-10-21-lean-rust-solver-builder/rust/Cargo.toml
    cargo build --release --locked --offline --manifest-path research/2026-10-21-lean-rust-solver-builder/rust/Cargo.toml
    python3 -B research/2026-10-21-lean-rust-solver-builder/codec.py encode --repository . < research/2026-10-21-lean-rust-solver-builder/fixtures/two-acquisition.json

Feed the encoded wire to the freshly admitted common-support-proposer binary.
Decode its captured complete stdout with codec.py decode --repository .
--request fixtures/two-acquisition.json (using the full fixture path).
Submit the decoded JSON to the unchanged runtime.py or solve.py --request
path/to/decoded.json --output path/to/absent-output. Use the EXISTING owned
bounded runner and encrypted/private runtime-record route. These are proposed
commands, not executed or scheduled commands. Do not send the new proposer
binary as --rust-binary to a canonical whitelisted runtime.

## Actual verification

reference.mjs executed directly from its captured source string in the
functions.exec V8 environment, using BigInt exact rationals. There was no
phone execution or materialization of the reference. Results:

- 205 acquisition cases:183 generated certificates,3 UNKNOWN,19 refusals.
- 252 mutations of coefficients, moments and weights rejected by separate
  weighted-square expansion and exact annihilation checks.
- 84 node-order reversal pairs produced byte-identical certificate wires.
- Endpoint1, equivalent rational spelling, rational-cap UNKNOWN and invalid
  normalized/domain inputs are included.
- All valid literal requests in the proposed Rust unit source were additionally
  evaluated by the reference. This does not execute those Rust tests.

REFERENCE-RESULT.json records the execution tier and source identity.
fixtures/native-cases.json retains all205 deterministic replay inputs and
expected outputs; the oversized-input case uses an exact repeat description,
not a256KiB file of spaces. No unchanged historical test was rerun here.
The original checker/native differential corpus remains separate.

The initially transcribed three-node Rust test contained guessed high moments.
Before publication, exact reference values replaced them; no passing native
test is claimed for either version. Future compiler/API errors may remain.

## Proof and scope

See PROOF.md for a hand derivation of output soundness. The existing checker
reports only its original conservative support_cap=L-1 (2r). The proposer does
not upgrade this to r, does not apply a hybrid budget to search and does not
prove any candidate source exists. Every emitted proof remains uncompiled
until its own exact source/type/axiom/custody evidence is accepted.

Common-law moments must belong to ONE law across the selected copy levels.
Independent routing, different masks or row-by-row fitted physical tuples
cannot be pooled merely because a shared bank name is reused.

OBLIGATIONS.md carries the integration gates. G1/G2/full binary-M3 G5 recovery,
remaining G6/G7 assembly, original all-input G3 termination and finite legal
INDEPENDENT G4 forcing retain their own evidence and completion standards.
This bounded acquisition component does not replace those goals.
