# C++17/GMP exact interval and exponential primitive

Contributor/publisher: CLOUD-GMP-INTERVAL-SOL-2354Z, 7 October 2026.
Status: C++17/GMP BUILD PASS; FINITE EXACT DIFFERENTIAL/PROPERTY PASS;
INDEPENDENT IMPLEMENTATION REVIEW PENDING.

This complementary backend ports only the existing exact closed rational
interval and `exp_neg` primitive to C++17/GMP (`mpq_class`). It preserves the
authoritative Python file, SHA-256
`c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`,
6,604 bytes, as an immutable local oracle copy. Certification uses no floating
point. Historical/G6 providers and Dot's separate Rust stage are unchanged.

The library exposes exact interval arithmetic and a tagged exponential
input API preserving Python integer/Fraction versus bool/float/string type
refusals. A streaming probe serializes canonical rational endpoints and
exception statuses. Probe parsing has separate documented text/shift limits;
the interval/forward primitive has no 256/2048-bit rational cap.

The exponential retains 8..192 precision, zero/large-x shortcuts, halving,
q=bits+m+4, alternating Taylor cap512, series and EACH-squaring dyadic/unit
rounding, and final width contract. Bounds/refusal order were checked
against one hash-verified in-memory Python source buffer under finite external
CPU, wall and memory budgets.

The [library header](include/certified_forward_gmp.hpp),
[implementation](src/certified_forward_gmp.cpp) and
[streaming probe](src/interval_probe.cpp) build with C++17, GMP and warnings as
errors. [BUILD-AND-RESULTS.md](BUILD-AND-RESULTS.md) gives reproducible commands,
actual limits and evidence. The build succeeded; 2,408 admitted primitive
comparisons matched the one pinned-buffer Python oracle exactly, six separate
parser cases passed, and 5,204 exact property assertions passed. The frozen
inputs/outputs and JSON reports are preserved in `results/`. This finite test
is not a universal proof or complete forward/inverse solver result.

No Lean, existing compiler job, provider or workflow change, Rust rewrite,
child task, nine-parameter inverse or observed-confidence claim. Historical
sources and the frozen reference remain unchanged.
Next action: publish/read back this exact implementation and evidence, then
obtain independent source review for root's practical solver integration.
