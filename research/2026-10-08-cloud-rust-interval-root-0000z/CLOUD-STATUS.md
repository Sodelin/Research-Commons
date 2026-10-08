# Cloud continuation of Dot's native Rust interval kernel

Codex root, CLOUD-G6-SOL-ULTRA-20261007, observation 8 October 2026,00:02 UTC.
**Ten unit fixtures, doctests and release build PASS; differential and
independent review pending. Full solver remains OPEN.**

Dot's [17-file original handoff](../2026-10-07-rust-interval-handoff/HANDOFF.md)
at `f2fa0c33f926c0f8a2e90bc47379ea89b146fceb` was copied unchanged before
repair. [CLOUD-FORK.json](CLOUD-FORK.json) pins every original byte; the
original README, manifests and9-pass/1-fail logs remain historical.
The only Rust source change is the test fixture in [tests/core.rs](tests/core.rs):
`2^255/3` is genuinely non-dyadic, has a256-bit reduced numerator, and grows
beyond 256 bits on 128-bit dyadic rounding. Assertions check that input size
and denominator before confirming post-rounding growth and the subsequent
negation refusal. The library, parser and probe are unchanged.

Actual Cloud observations are preserved separately:

- [Original tests](reports/cloud-original-test.json): exit 101,9 PASS/1FAIL,
  reproducing Dot's fixture failure.
- [Repaired attempt 2](reports/cloud-repaired-build.json): all 10 unit tests
  passed, but cargo exited101 because the isolated rustdoc executable was
  not selected for doctests. This is an execution failure, not a passing
  complete check.
- [Attempt3](reports/cloud-attempt3-build.json): explicit Rust 1.90 rustc and
  rustdoc, locked/offline cargo tests and release build both exit 0. All10
  unit fixtures and doctests pass. Release-probe SHA256
  `1927426e00f8b0fc736954ef0fd3f449511b8c3054085e5298341985a2e0c4d0`,
  688344 bytes. Sources are identical before/after. Exact differential
  comparisons against the frozen Python buffers are the next gate.

Five exact Cargo.lock dependencies were fetched under Nolan's explicit
practical-build authorization before the offline commands. There is no
claim that the initial provisioning was offline. No binary/toolchain is
committed; source and complete logs are preserved. MinimumRust 1.74 is
untested; actualRust 1.90 was used. Timings are command observations, not
comparative benchmarks.

Forward arithmetic keeps exact rational endpoints until explicit dyadic
sites. The signed receiver checks emptiness, then reduced endpoint size,
then rounds; post-rounding growth is allowed and checked on later
operations. Context identity and exponential-call accounting remain
distinct from forward parsing. The probe is a bounded test adapter, not
a production protocol: it parses an unused second interval for unary
operations and checks line length after line allocation. Public
BigRational/fraction constructors require nonzero canonical denominators,
and unrestricted dyadic precision needs a validated production boundary.
These disclosed API gates remain open. Python source authentication is
reference provenance, not the identity of compiled Rust.

The independent C++/GMP interval port uses the same frozen reference
contract in its own packet. Rust exact-core and shared C/GMP FFI variants
are separate implementations. Backend selection and acceleration require
measured evidence after compatibility passes. Confidence, complete
frontier cover, all-nine widths ≤1/20, full physical model and Lean
executable correspondence remain open.


## Exact differential gate at 00:10 UTC

[The single native comparison](reports/cloud-differential/ACTUAL-RESULT.md) passed **3,048/3,048 exact cases**, with zero differences and zero reference-adapter errors:2,201 successful kernel outputs,803 kernel refusals and44 transport guards. Exact endpoints, refusal labels and exponential-call counts match the pinned Python buffers. Probe exit0, stderr empty, no timeout; all source, staged-provider and executable hashes match before/after. The complete [summary](reports/cloud-differential/run-once/summary.json), every expected/actual case, raw wire inputs/outputs and hash ledger are preserved. No rerun or source repair was needed.

This opens the next bounded signed-receiver implementation gate. It remains finite compatibility evidence; universal equivalence, production API admission, biological/source semantics, confidence and a complete useful solver remain separate. The original earlier review-pending observations are preserved. Primary immutable source/result review is next.
