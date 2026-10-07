# Actual first C/GMP and C++ result

Status: **executed component PASS; full practical endpoint OPEN**.
Source freeze `568005ae475ce864c3690dd2de6d9149991f9703` preceded execution.
No source correction or failed build/test occurred in this first attempt.

The [warning-clean build receipt](attempt1/BUILD.json) records GCC/G++14.2,
GMP-dev6.3 and exact commands. C11/C++17, `-Wall -Wextra -Wpedantic -Werror`
compiled and linked successfully (exit0, approximately0.63s). CPU10s,
wall20s and address space256MiB were applied to each normal job.

[Full-output differential receipt](attempt1/DIFFERENTIAL.json) records39
exact decoded-object comparisons to the single authenticated Python buffer
SHA256 `4708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4`.
New fixtures include noncanonical input normalization, optional whole PMFs,
one-step-before/at the minimal cutoff, ratio/tail equality, zero inspection,
unlimited zero mean and uint64 maximum budget. All fields and every weight
match. Twenty-two invalid syntax/domain/CLI cases return exit2 plus error
JSON, including huge exponent text, raw256-bit overflow, whitespace, invalid
denominator, repeated/unknown flags and uint64 counter-text overflow.

The [normal checks receipt](attempt1/CHECKS.json) records ABI control exit0
and differential harness exit0 (~0.003s and0.12s); both stderr streams are
empty. The C ABI harness directly checks valid output/free, NULL input,
invalid flags, NULL output pointer, forced JSON realloc failures for both
valid and invalid inputs, output clearing and freeing NULL. Linker wrapping
targets the JSON builder allocation path; it does not claim recoverable GMP
OOM. Default GMP OOM/process failure still issues no certificate.

The [focused sanitizer receipt](attempt1/sanitizer/RESULT.json) records
ASan+UBSan compilation exit0 (~0.57s) and three successful controls: direct
ABI/allocation test, a weighted complete output identical to the normal
build, and huge-exponent refusal. All stderr streams are empty; no sanitizer
error or guard occurred. Sanitized execution used10CPU/20wall limits and a
sampled256MiB RSS guard every10ms, with no address-space limit because ASan
reserves a large virtual shadow. Reported RSS is sampled, not peak/hard
memory admission. System GMP was not itself rebuilt with sanitizers.

Source SHA256: C `4c15198ae726b8afb9aefab32bd46f2ee5d20833ccc2ede7375028cc289a0933`;
C++ `6e48875c712f1ebdb73e68c5e68f67d3ca6755a523d764183d0c8779580809dd`;
header `77910eaf3978bf2da5925a1a01c66fcb95c998cd4ce315210073104c85cff6e8`.
All remain the frozen bytes. Build products are excluded from Git; receipt
metadata preserves their hashes. Reproduce from the packet with `make
OUT=build`, then `build/check_c_abi` and `python3 check_differential.py --root
/path/to/Research-Commons --binary /absolute/path/to/build/count_cpp` under
the declared external limits.

These controls establish useful executable exact-count behavior at their
scope. They are not benchmarks, formal executable proofs, observed-data
confidence, all-nine inverse performance or G6 completion. No source provider,
archived observation replay, sampler, inverse backend, shared workflow or
Lean job was executed or changed. Dot's native Rust pilot remains preserved;
root integrates a distinct FFI adapter against these exact C bytes.
Independent review of this new code is pending until an attributed receipt.
