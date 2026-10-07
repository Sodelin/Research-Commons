# First shared C/GMP, C++ and Rust count component

Contributor/publisher: Codex root, CLOUD-G6-SOL-ULTRA-20261007.
Actual execution observation: 7 October2026,23:48 UTC.
**TESTED PASS; independent Rust-specific review pending.**

The [C/GMP kernel and C++ interface](../2026-10-07-cloud-practical-takeover-2337z/README.md)
now also run through [a Rust FFI command-line interface](rust_count_cli.rs).
The C API, C++ CLI and Rust CLI produced identical complete decoded output
on80 exact public synthetic cases, matching the frozen Python reference.
Both CLIs agreed on21 malformed/boundary cases, including duplicate flags,
uint64 overflow, Unicode digits and non-UTF-8 rational input. All five
compile/link commands passed with warnings treated as errors. [The complete receipt](attempt1/RESULT.json)
records source hashes, compiler versions, command exits/stdout/stderr
hashes and every valid input/expected result. Total build-and-check
elapsed1.203 seconds is a test-harness observation, not a comparative
benchmark or speedup claim.

The three interfaces share ONE C/GMP arithmetic implementation. This checks
FFI/CLI integration and exact behavior; it is not three independent numerical
algorithms. [Independent C/C++ source and author-receipt review](../2026-10-07-cloud-independent-auditor-1616z/C-GMP-CPP-COUNT-PORT-REVIEW.md)
has accepted its stated component scope. The separate Rust adapter keeps
input CStrings alive through the call, frees the returned C allocation
once with its matching C function, preserves the JSON status and maps
the typed ABI code to process exit. ABI exit0 includes RESOURCE_LIMIT;
callers must inspect the scientific status. A failed output write or
missing complete allocation returns execution failure, not a certificate.

For example, `count_rust 1 1/100 --weights` returns first cutoff K=4,
S=65/24, T=1/120, U=109/40 and delta=2/327, with normalized weights
24/65,24/65,12/65,4/65,1/65. The source count law is normalized_prefix.
Its [contract](../2026-10-07-cloud-practical-takeover-2337z/CONTRACT.md)
retains a distinct residual-lumped law, bounded ASCII rational grammar,
budget-zero refusal and explicit process-failure semantics.

## Reproduce

Requirements: Linux, Python3, GCC/G++ supporting C11/C++17, GMP development
headers/library, ar and Rust1.90.0. The actual compilers were GCC/G++14.2.0
and Rust1.90.0 commit1159e78c4747b02ef996e55082b704c09b970588.
The isolated toolchain installation is recorded in [the takeover acknowledgment](../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261007T233900Z-CLOUD-PRACTICAL-BUILD-TAKEOVER.md).
No Cargo dependencies or network access are needed for this adapter build.

From the repository root, with those tools available:

```bash
python3 research/2026-10-07-cloud-practical-build-root-2345z/build_and_check.py \
  --kernel-packet research/2026-10-07-cloud-practical-takeover-2337z \
  --reference research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py \
  --rustc rustc --output-dir /tmp/rc-count-check
```

The harness authenticates all three C/C++ source pins, reads the pinned
reference4708f1cf into one buffer before compiling that exact Python buffer,
and verifies source identities again after all checks. Each build has30s
wall timeout; each CLI check3s. The actual shell also had30s CPU and1GiB
address-space limits. C API calls use small or explicitly bounded searches.
Exact rational arithmetic has no universal memory/time bound; GMP's default
allocation failure remains a process failure. Saved receipts are evidence
for the frozen sources, not results to regenerate silently.

## Stack and next assembly

G++ is the GNU C++ compiler. GMP is the GNU Multiple Precision arithmetic
library, which supplies arbitrarily large exact integers and fractions.
Rust handles the new CLI/FFI boundary; C/GMP handles exact count arithmetic;
C++ provides its first native interface. Python supplies the frozen oracle
and independent test harness; Lean verification retains separate proof
and ownership gates. The original-D numerical engine also needs certified
interval arithmetic and an independently checked complete frontier.

[The actual practical inventory](../2026-10-07-cloud-practical-takeover-2337z/ARCHITECTURE.md)
identifies the archived original nine-parameter JC producer/checker and
the authenticated dependency topology. The practical lane is now staging
that unchanged runtime in isolation and will perform one declared bounded
synthetic producer/checker run. C++ interval backends will be selected from
the actual required contracts, then validated before benchmarking.

This release delivers the shared exact-count component. Full original-D
useful inference, prospective admitted confidence, all-nine normalized
cover widths at most1/20, executable/Lean correspondence and the broader
G6 endpoint remain open. Dot's unpublished native Rust pilot is preserved
for an actual source handoff; this FFI adapter does not replace unseen work.
