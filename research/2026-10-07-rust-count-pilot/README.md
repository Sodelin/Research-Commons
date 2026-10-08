# Exact count-certificate Rust pilot

A small standalone Rust library and CLI port of the exact normalized
Poisson-prefix component. This is the first bounded experiment toward a Rust
solver core. It does not replace the other research programs, their providers,
shared CI, or the Lean verification driver.

## Executed status

Rust 1.90.0 release build and 10 unit tests passed. All 1,693 deterministic
corpus cases matched the frozen reference exactly, including complete JSON
bytes; 22 invalid CLI cases and 5 extra boundaries passed. The five-workload
full-CLI benchmark is recorded separately and includes process startup.
See [executed results](evidence/RESULTS.md) and raw evidence for limits.
Independent review and cross-platform/distribution gates remain separate.

## Scope and mathematical contract

For exact `a >= 0` and `0 < epsilon < 1`, start `t_0 = S_0 = 1`.
At candidate `K`, compute exactly:

- `T = t_K * a / (K + 1)`
- `S = sum_{j=0}^K a^j/j!`
- `U = S + 2*T`, `delta = 2*T/U`

Return the **first** candidate satisfying both `K+2 >= 2*a` and
`delta <= epsilon`. Both comparisons include equality. A successful result is
`CERTIFIED`, with law `normalized_prefix`, exact canonical rational strings
for `a, epsilon, S, T, U, delta`, and integer `K, inspected`.

`--max-steps N` limits inspected candidate cutoffs, not recurrence updates or
wall time. `N=0` returns `RESOURCE_LIMIT`, `inspected=0`, `next_K=0` without
inspecting a candidate. A success at `K` requires `K+1` inspections. A limit
returns `inspected=next_K=N` and carries no negative source/target conclusion.
An omitted budget permits the same unbounded mathematical search as the
reference. Counters are arbitrary-precision `BigUint`; rationals use
`BigRational`, not fixed-width or floating-point approximations.

`--weights` adds exact `q_j=(a^j/j!)/S_K` only after success. Weights sum to one;
no residual tail mass is moved to zero. Weight generation happens after the
cutoff search and is not charged against the inspected-cutoff budget.

This numerical input-layer certificate does **not** construct a biological
source, constrain hidden source parameters, establish scientific admission,
prove a physical-source claim, or establish Lean verification. The older
residual-lumped backend defines a different count law.

## Layout and interfaces

- `src/lib.rs`: typed exact core; private certificate fields with read-only accessors
- `src/parse.rs`: separately named bounded ASCII CLI transport profile
- `src/main.rs`: standalone CLI; never invokes Python
- `reference/count_certificate.py`: byte-preserved independent Python reference
- `scripts/check.py`: deterministic differential/adversarial checks and direct-factorial checker
- `scripts/benchmark.py`: bounded Linux full-CLI measurements after passing differential checks
- `evidence/`: actual check reports, corpus, logs and provenance; unrun work is explicitly marked

Library entry points are `certify(&Rational, &Rational, Option<&BigUint>)`
and `weights(&Rational, &BigUint)`. `Outcome` is either `Certified` or
`ResourceLimit`; invalid mathematical inputs return `Err(InvalidInput)`.
Raw rational values are canonicalized; a zero denominator is rejected before
arithmetic. Booleans, floats and negative natural cutoffs are not values of
these typed inputs.

CLI usage:

```sh
count-certificate 1 1/2 --weights
count-certificate 2.5 1e-8 --max-steps 100
```

Both `CERTIFIED` and `RESOURCE_LIMIT` exit 0. Invalid transport, invalid domain
or bad usage exits 2, writes a diagnostic to stderr, and emits no JSON.
JSON key order, spacing, rational rendering and trailing newline intentionally
match `json.dumps(result, sort_keys=True)` on the supported input profile.
The legacy numeric cutoff fields remain JSON numbers; clients requiring
arbitrary-size transport must parse them as integers, not JavaScript doubles.
There is no new JSON request envelope or GUI in this pilot.

## Explicit parser and operational differences

This pilot preserves the mathematical Fraction-input contract, not every
Python/argparse syntax quirk. Its version-1 ASCII transport profile accepts:

- signed integer numerators; fractions `n/d` with positive unsigned denominator
- finite decimals such as `1.`, `.5`, `-0.25`, and `e`/`E` exponents
- surrounding ASCII whitespace, leading zeros, and explicit leading `+`
- `--max-steps N` or `--max-steps=N`, with unsigned decimal N or leading `+`

Each numeric token is limited to 4,096 bytes before conversion; exponent
magnitude is limited to 4,096. Internal whitespace, Unicode digits,
underscores, duplicate flags, unknown options and Python's boolean-as-integer
API behavior are not supported. The Python library accepts `True`/`False` as
`max_steps` and `weights` cutoffs; Rust's natural-number API has no such
boolean coercion. Negative zero `--max-steps -0`, which Python accepts as zero,
is intentionally rejected by this unsigned transport profile. Python float
objects are not accepted by the reference `certify` API, even though Fraction
construction elsewhere can accept floats. This CLI never converts through a
float. Some Python-version-specific Fraction spelling extensions are outside
this explicitly documented profile. Negative-domain validation and malformed
arguments use one deterministic exit code rather than reproducing traceback
and argparse diagnostic text.

The input caps are **transport rejections**, not a new mathematical
`RESOURCE_LIMIT`. They do not change the library's recurrence schedule. The
pilot has no wall-time limit, memory cap, signal checkpoint, subprocess
supervisor or allocation-failure recovery. Even a small cutoff budget can
involve costly huge-rational arithmetic, and optional weights consume memory
proportional to K. Use bounded inputs and external process limits for service
use. This is not yet a hardened multi-tenant runtime.

## Reproduce checks

Use the approved official Rust 1.90.0 toolchain and the pinned dependencies
in `Cargo.toml`. No check script installs software or changes global settings.
Once the dependency lockfile and cached crates are present:

```sh
cargo test --offline --locked --all-targets
cargo build --offline --locked --release
python3 scripts/check.py --build
python3 scripts/benchmark.py
```

For the isolated project-local toolchain, set `RUSTUP_HOME` to
`$PWD/.toolchain/rustup`, `CARGO_HOME` to `$PWD/.toolchain/cargo`, and prefix
this shell's PATH with `$CARGO_HOME/bin`. No global PATH edit is needed.
`python3 scripts/check.py --reference-only` verifies the source identity,
generates the fixtures, checks them independently and explicitly records
Rust work as UNEXECUTED. It cannot establish Rust/reference agreement.

The deterministic corpus covers zero, tiny/large exact rationals, values
beyond 128-bit representation, exact inequality equality and adjacent
values, first cutoff, limits immediately before/at/after success,
no-step budgets, optional weights, decimal/scientific parsing and seeded
rational inputs. Every expected result is independently checked using direct
`a**j/j!` formulae, including all earlier rejected cutoffs. Mutated S/T/U/delta,
cutoff/inspection counters, weights and law are rejected. Candidate checks
compare both every JSON field and complete legacy output bytes.

Differential agreement on a finite corpus is evidence about these executions,
not a proof for all inputs. Benchmarks include CLI startup, parsing and output;
they are neither kernel-only measurements nor a claim about the whole solver.

## Provenance and current release gate

Reference: [Sodelin/Research-Commons at c9a6934ecb09ea22dc0204def2ad6398dfb43fa2](https://github.com/Sodelin/Research-Commons/blob/c9a6934ecb09ea22dc0204def2ad6398dfb43fa2/research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py).

- Original path: `research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py`
- Git blob SHA-1: `85935eb2c7b07c111b5a5bb54004e7f101b4dc1a`
- SHA-256: `4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4`
- Exact byte length: 3,101

The new Rust implementation and test tooling were produced by OpenAI's dot
for Nolan's authorized integration experiment on 2026-10-07. The preserved
reference remains attributed to its source repository and pinned revision;
no new ownership or license claim is made over it or the dependency code.
No package-publication license or redistribution review has been completed.

Consult `evidence/check-report.json` for actual tested status and identities.
The reference hash is never presented as the Rust binary identity. Rust source,
lockfile, compiler, flags and binary have separate provenance. There is no
full-solver verification certificate or cross-platform release claim.

Before adopting this core: finish independent review, investigate any
findings, preserve exact differential results and source/build identities,
and decide the package/distribution/license gate. Later arithmetic/provider/
betting/Lean stages remain separate work, not an implied completion of this
count-only pilot.
