# Exact interval pilot: paused engineering handoff

Author: dot (OpenAI), 2026-10-07. This packet was paused when the user assigned Rust application/publication work to the Codex work team. No publication or production changes were made.

## Status first

- Reusable library and line-oriented test probe implemented locally.
- Cargo check: PASS after the probe was added. The initial check failed only because the declared probe file had not yet been created.
- Offline locked unit run: **9 PASS, 1 FAIL**. This is not an accepted stage.
- Offline locked release build: PASS.
- Differential tests: **not implemented or run**.
- Independent arithmetic/exponential validation: **not run** beyond the focused unit tests.
- Benchmarks, formatting/lint audit, independent reviewer audit, and fresh-root rebuild: **not run**.
- Signed receiver scientific formulas, full 330-feature evaluator, production adapters, active Cloud provider changes, CI changes, Lean verification, and publication: **not performed**.

The failed test is `budget_checked_before_rounding_not_after` in `tests/core.rs`. Its input is `(2^256 - 1)/3`, which reduces to an integer because the numerator is divisible by 3. Consequently it does not exercise the intended non-dyadic, post-rounding bit-growth condition. This is a diagnosis, not an executed fix. The test and failure log are preserved unchanged. Review a corrected non-dyadic fixture, compare it with frozen Python, then rerun every check. Do not describe this packet as passing until that happens.

## Frozen reference identities

Repository: Sodelin/Research-Commons
Commit: c9a6934ecb09ea22dc0204def2ad6398dfb43fa2

1. `reference/signed_receiver.py`
   - Original path: research/2026-10-07-cloud-practical-signed-guard-2159z/signed_receiver.py
   - Git blob: d3c8680a7f06f53d38de46ad28d0d8f9cc1f7790
   - SHA-256: 61db9997db84b925c6eff405744726e01dcec14d0090192e834f33a75aeafc1f
2. `reference/certified_forward.py`
   - Original path: research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py
   - Git blob: f982f671c80f50a8995cee56b61ac3655730cf7b
   - SHA-256: c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace

Both source files were fetched at the exact commit, read in full, and frozen as exact bytes. The forward provider contains its own interval and exponential implementation; it imports no separate interval-provider module. Its SHA-256 agrees with the receiver's embedded provider identity.

## Implemented mathematical boundaries

`src/lib.rs`:

- `Rational` aliases `num_rational::BigRational` and uses arbitrary-precision signed integers. Callers must obey that type's canonical nonzero-denominator invariant; this packet does not add a sealed rational wrapper. The convenience `fraction(i64,i64)` follows the dependency's zero-denominator panic behavior and is currently used by unit fixtures. Review public API choices before promoting it.
- `floor`/`ceil` use Euclidean mathematical floor/ceiling through num-integer, including negative values.
- `ForwardInterval` has private endpoints, exact construction and ordinary arithmetic, scalar-only division, explicit dyadic rounding and unit intersection. No receiver-style intermediate bit cap is added.
- `exp_neg` implements the frozen exact scalar Taylor/range-reduction/squaring schedule, bits 8..192, zero and x>=bits shortcuts, the 512-term cap and exact width check. It has not yet been differentially tested. It omits the Python memoization cache, so performance equivalence is not claimed.
- `ReceiverContext` uses identity-bound Rc state and explicit precision/bit/exponential-call bounds. Cloning shares identity and count. Fresh equal-looking configurations cannot mix intervals.
- `ReceiverInterval` checks empty first, endpoint bit lengths next, then rounds every construction outward. Negation and reciprocal construction remain separate rounding/check sites. Scalar coercion and reverse subtraction/division are explicit methods.
- Receiver exponential reverses endpoints because e^(-x) is decreasing; checks context/domain before budget; charges two calls before either endpoint computation; and rounds the returned enclosure through the receiver context.
- No Python source-byte hash is represented as the Rust implementation identity. This library replaces neither reference source authentication nor compiled provenance.

`src/parse.rs`:

- Receiver text parser follows bounded ASCII grammar, character/raw digit caps, zero denominator refusal and pre-reduction 256-bit checks.
- Forward text parser follows the separate reduced-value 256-bit check and frozen Unicode decimal-digit behavior; denominator first digit is ASCII 1..9. Unicode Nd zero-codepoint table was generated from this environment's Python Unicode database; `src/parse.rs` records its version.
- Forward typed value entry accepts a BigRational; transport distinctions such as Python bool versus int, floats, JSON types, surrogate strings, duplicate keys and full model-input validation are not production-ported.

`src/main.rs` is a bounded differential-test adapter, not a production wire protocol. It accepts tab-separated one-line operations and returns exact rationals or explicit errors with receiver call counts. It rejects lines over 131072 bytes and has its own probe-specific bounds; it parses an unused second interval even for unary operations, so the future differential oracle must mirror the harness before comparing outcomes. Avoid interpreting probe-specific refusals as reference API behavior.

## Dependency/toolchain reproduction

The source packet includes Cargo.toml and Cargo.lock. Direct pinned dependencies are num-bigint 0.4.6, num-rational 0.4.2, num-traits 0.2.19 and num-integer 0.1.47; the only additional transitive package is autocfg 1.5.1. These were already approved and cached by the count pilot. No dependency/tool installation or download occurred here.

Actual build used Rust 1.90.0 and the existing count-pilot cache through `scripts/env.sh`. That script's default absolute path is an executor-local convenience, not an availability guarantee. For another executor, separately transfer/provision an approved Rust 1.90.0 toolchain and the exact locked packages through that executor's supported transfer/setup route, then set `TOOLCHAIN_BASE` or the equivalent Cargo/Rustup environment. Do not assume this executor's filesystem exists there. An absent cache is a setup blocker; do not silently fetch dependencies without the applicable approval.

Executed commands (from the packet root):

- `. scripts/env.sh`
- `cargo generate-lockfile --offline`
- `cargo check --offline --locked`
- `cargo test --offline --locked` (failed: 9 pass, 1 fail)
- `cargo build --release --offline --locked` (passed)

Preserved logs: reports/dependency-lock.log, reports/rust-tests.log and reports/rust-build.log. The successful cargo check appeared in task output, not a dedicated log. The failed test's subsequent successful build does not convert that test run into a success.

## Next bounded steps for the receiving team

1. Inspect both frozen Python sources and this Rust candidate; correct/review the failed fixture without hiding its prior failure log.
2. Build an independent Python differential harness that imports the frozen providers (place the forward file at its original nested path under a temporary root for receiver authentication). Execute exact endpoint/refusal/call-count comparisons, including negative intervals, signed scalar operations, zero-crossing denominators, mixed context, empty meet, budget/refusal order, raw versus reduced rational limits and Unicode grammar.
3. Cover exp_neg at zero, around x=1 and binary range-reduction boundaries, around x=bits, bits 8/192 and receiver precision 64/128, repeated calls and exhausted budgets. Compare exact rational endpoints, not decimal tolerance.
4. Add independent enclosure checks based on rational corner arithmetic and a different positive-series reciprocal exponential bound; preserve a reproducible corpus, seeds, hashes and complete output reports.
5. Review resource schedules, public rational invariants, input transport boundaries, Rc/non-thread-safe context choice, lack of exponential caching and provenance representation. No safe-looking extra arithmetic check may silently alter legacy refusal behavior.
6. Run offline locked tests, release build, format/lint if available, independent review, and an isolated source-only rebuild. Record toolchain, dependencies, source and executable hashes; add modest benchmarks only after correctness gates.
7. Only after accepted arithmetic stage proceed to a separately bounded signed-receiver formula port and model-specific evidence gates. Publication is owned by the parent/Codex work team and is not authorized by this handoff itself.

No full-solver completion, scientific admission, formal proof, Lean certificate, Rust/Python equivalence or performance gain is claimed.
