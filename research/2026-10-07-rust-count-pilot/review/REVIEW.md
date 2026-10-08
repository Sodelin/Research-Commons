# Independent review: Rust normalized-count certificate pilot

Review date: 2026-10-07 UTC. Scope: read-only static Rust and checker review against the frozen Python reference, independent exact Python controls, and independent executions of the final frozen release binary. Reviewer did not compile Rust or edit the author's package. Initial source identities are recorded in `independent-report.json`; final replay identities are recorded in `binary-replay-report.json`.

## Final outcome after author fixes and frozen-binary replay

**No remaining mathematical correctness blocker was identified for the bounded count-only pilot.** The initial CLI transport finding was fixed and independently reproduced. This assessment supports retaining and further integrating the explicitly scoped pilot; it does not certify all inputs, all platforms, the whole solver or formal verification.

The author replaced `env::args()` with fallible `args_os()` conversion. A raw non-UTF-8 Unix argument now independently returns exit 2, an error on stderr and no JSON. The author added raw negative-denominator and unreduced-epsilon unit controls. README explicitly documents Boolean differences in both Python APIs, optional post-search weight allocation, token-profile restrictions, no allocator/wall-time guarantee, and normalized-prefix versus residual-lumped law. These findings are resolved.

Independent final release replay passed:

- 64 byte-exact expected-output cases computed by the reviewer's separate factorial-formula implementation, including cutoff/budget boundaries, exact equality, optional weights, large rational components, decimal spelling and long exponent-leading-zero forms.
- Eight invalid-transport/domain cases, including non-UTF-8, invalid a/epsilon with a zero budget, duplicate flags, negative-zero budget and transport-cap excess.
- One additional huge arbitrary-precision natural budget that terminates immediately at a=0.

The reviewer inspected the author's 10-passing-unit-test log and locked/offline optimized build log, then checked the current source, dependency lockfile, frozen reference, corpus and executable identities against the receipt. The reviewer did not rebuild the package. Core and binary hashes were checked both before and after the independent executions.

Final release executable: `target/release/count-certificate`, 636,256 bytes, SHA-256 `5f8afd1557623ebf889b2d2e6fdbcf84a8c5a75e55993e32600fb54ecad700d1`. Build receipt identifies Rust/Cargo 1.90.0 on x86_64 Linux, 1,693 differential field-and-byte checks, 22 invalid cases and five additional boundary checks. The reference remains SHA-256 `4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4`.

### Performance evidence boundary

The reviewer recomputed each reported median from its seven raw samples and verified the benchmark binary identity. Across five small workloads, Rust CLI median elapsed times are 1.15–3.43 ms, versus 24.10–26.13 ms for Python. These include process startup, parsing, arithmetic, serialization and operating-system scheduling. No arithmetic-kernel speedup or whole-solver gain follows from this evidence. All reported peak-RSS values are identically 14,204 KiB, so this run establishes no useful relative-memory conclusion. No benchmark was rerun by the reviewer.

### Remaining gates and limitations

- No universal mathematical proof, Lean verification, end-to-end simulator integration or production service hardening is established by the finite tests.
- Rust 1.74 minimum-version compatibility is declared in Cargo.toml but was not tested; the executed toolchain is 1.90.0.
- Cross-platform portability, resource-exhaustion behavior and package/dependency licensing or distribution readiness remain separate checks.
- Build logs and matching hashes are provenance for the observed build and executions; the reviewer did not perform an independent rebuild or demonstrate bit-for-bit reproducibility across machines.

Review artifacts: `independent_controls.py`, `independent-report.json`, `replay_binary.py`, `binary-replay-report.json`, and this report. The older initial-snapshot section below preserves the findings and their evidence level before Rust execution became available.

## Outcome at initial snapshot

No mathematical or first-cutoff correctness defect was found in the inspected core. This is a source review and bounded exact-reference testing result, not proof that the Rust source compiles, not executed Rust conformance, not a benchmark, and not Lean verification. The author's reference-only report correctly labels Rust build, Rust tests and differential comparison `UNEXECUTED`.

One concrete CLI-contract gap was reported to the author: `std::env::args()` can panic when an operating-system argument is not valid UTF-8. That would exit with Rust's panic code rather than the help text's advertised invalid-input/usage exit 2. `args_os()` with explicit fallible conversion can reject such arguments cleanly. This is a transport failure, not a false mathematical certificate.

An additional documented API difference is required: Python's `bool` subclassing `int` affects both `max_steps` and `weights(a, k)`. The Rust `BigUint` API has no Boolean cutoff representation. The existing checker recognizes the budget quirk; the independent controls also establish the weights quirk.

## Mathematical audit

Let `t_i = a^i / i!`, `S_K = sum(i=0..K) t_i`, and `T_K = t_(K+1)`.

- Before inspecting cutoff K, Rust has `term = t_K`, `prefix = S_K`, and `inspected = K`.
- It computes `next_term = t_K*a/(K+1) = T_K`, `U = S_K + 2*T_K`, and `delta = 2*T_K/U`.
- It increments `inspected` once before checking success. A successful certificate at K therefore reports K+1 inspections.
- The two success tests include equality and match the frozen reference: K+2 >= 2a and delta <= epsilon.
- On failure, incrementing K and then setting term to the old T and adding that term to prefix restores the invariant.
- `Some(0)` inspects no cutoffs. A finite budget N returning `RESOURCE_LIMIT` means exactly K=0 through N-1 were inspected and failed, with `inspected=N` and `next_K=N`. It gives no negative implication concerning a source or target. Invalid a or epsilon is rejected before the budget check, including budget zero.
- Scanning all natural cutoffs in order preserves first qualifying cutoff semantics. There is no unreported numerical cutoff cap.

For a >= 0 and the guard K+2 >= 2a, subsequent Taylor ratios are at most a/(K+2) <= 1/2. Therefore the infinite omitted Taylor tail R satisfies R <= 2*T_K, while exp(a) = S_K + R. Its Poisson probability mass is R/(S_K+R) <= 2*T_K/(S_K+2*T_K) = delta. The normalized prefix q_i=t_i/S_K for i<=K is the Poisson distribution conditioned on that prefix. Its total variation distance to the full Poisson law equals the omitted probability mass; its unhalved l1 distance is twice that mass. A statement that l1 distance is at most delta would be incorrect; no such claim occurs in the reviewed core.

For a=0, K=0 yields S=U=1, T=delta=0 and weights [1], if at least one cutoff can be inspected. Exact unlimited mathematical search terminates: after a finite guard threshold, T shrinks geometrically while S>=1. This is not a wall-clock or allocator guarantee.

## Arithmetic and input-domain audit

- BigInt/BigUint/BigRational avoid machine overflow in the mathematical state, cutoff counters, guard conversion and rational recurrence.
- Every rational supplied to `certify` or `weights` is normalized through `Rational::new` after testing its denominator for zero. This matters because the exposed rational alias supports `new_raw`, which can otherwise contain unreduced fractions or negative denominators.
- Under the valid domain, S>=1, U>=1 and every recurrence divisor K+1 is positive. Hence the mathematical divisions cannot divide by zero.
- The parser is exact, never converting through binary floating point. Mantissa digits are concatenated and scaled by an integer power of ten.
- The byte limit is checked before trimming whitespace and before conversion. The token is ASCII, so accepted exponent split indices and substrings are valid string boundaries.
- With a maximum 4096-byte token and absolute exponent at most 4096, the fraction-length-to-i32 conversion, scale subtraction and u32 power exponent conversion are safely bounded. These parser machine integers are not unbounded mathematical counters.
- Parser-profile restrictions are deliberate compatibility limits rather than changes to the count law: ASCII only, no underscores, positive unsigned fractional denominator, token/exponent limits, no negative-zero max_steps, and stricter duplicate flags. Python can accept additional forms and dynamic types. Broad claims of universal Python CLI interchangeability would therefore be too strong.
- CLI parsing allocates arbitrary precision numbers within the transport profile; the mathematical API itself has no such token cap.

## Weights and output audit

- The optional weight vector is computed only after a successful outcome when output is requested. `RESOURCE_LIMIT` JSON does not include weights even with the flag present.
- q_i=t_i/S_K is exact, nonnegative and sums to one. This is the normalized-prefix law. It does not move omitted probability mass to count zero, so it cannot replace a residual-lumped backend without declaring a change of law.
- Weight generation is additional post-certification work, not included in the candidate inspection budget. The Vec and serializer require memory and can fail or abort under resource exhaustion. That does not create a RESOURCE_LIMIT output or an invalid certificate.
- Success fields are private. External callers can inspect/clone a certificate but cannot freely construct or mutate the successful fields through the public API.
- The manual legacy JSON serialization only interpolates canonical exact-number strings and natural integers. There is no user-controlled arbitrary string escaping issue in these fields. Key order matches sorted Python keys, with `weights` last when included.
- Legacy counters remain JSON integers, rather than decimal strings. Consumers restricted to IEEE-754 number precision must not assume arbitrary-size integer fidelity.

## Independent controls

`independent_controls.py` uses direct factorial/power formulas rather than the recurrence. It checks the exact frozen reference hash before execution and does not import the author's checker.

Passed:

- 546 distinct exact (a,epsilon) pairs, including exact guard thresholds and epsilon equality with rational perturbations on either side.
- 2,695 complete reference-output comparisons at unlimited, zero, immediately-before-success, success, and immediately-after-success budgets.
- 546 exact weight-formula, nonnegativity and sum-to-one checks.
- 546 finite-extension checks of geometric-tail bound, delta bound and normalized-prefix total-variation identity.
- Four explicit Boolean-domain controls covering Python weights and inspection budgets.

Finite-extension controls support the implementation audit; they are not themselves proof of the infinite-series bound. The bound is justified separately above. These tests do not execute Rust.

## Author's test evidence and blindspots

The initial author's report records 1,693 reference cases, 16 reference invalid-input checks and eight checker mutations. These are appropriately separate from unexecuted Rust build/test/differential stages.

The source checker independently recomputes every certified rational field using factorial formulas, verifies output schema and budget semantics, checks all earlier cutoffs, and verifies exact optional weights. It byte-compares Rust CLI output with Python's sorted JSON in the planned differential stage. The mutation checks demonstrate rejection of altered S/T/U/delta/K/inspected/weights/law, rather than mere fixture agreement.

Suggested additional controls communicated to the author:

- Invalid non-UTF-8 operating-system argument handling.
- Raw ratios with negative denominators and an unreduced epsilon, alongside the existing unreduced-a and zero-denominator tests.
- Record final source, lockfile, compiler and binary identities; report an attempted failing stage as FAIL, rather than UNEXECUTED.

Still outside this review and the current bounded corpus: every possible rational input, denial-of-service bounds for huge exact inputs, allocator failure behavior, Windows argument encoding, other architectures, minimum-declared-Rust-version builds, performance regressions and downstream simulator integration. A current-toolchain pass alone would not verify the Cargo manifest's Rust 1.74 minimum version.
