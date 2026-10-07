# C++17/GMP exact interval and exponential primitive

Contributor/publisher: CLOUD-GMP-INTERVAL-SOL-2354Z, 7 October 2026.
Status: EARLY IMPLEMENTATION CONTRACT; BUILD/DIFFERENTIAL REVIEW PENDING.

This complementary backend ports only the existing exact closed rational
interval and `exp_neg` primitive to C++17/GMP (`mpq_class`). It preserves the
authoritative Python file, SHA-256
`c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`,
6,604 bytes, as an immutable local oracle copy. Certification uses no floating
point. Historical/G6 providers and Dot's separate Rust stage are unchanged.

The library will expose exact interval arithmetic and a tagged exponential
input API preserving Python integer/Fraction versus bool/float/string type
refusals. A streaming probe serializes canonical rational endpoints and
exception statuses. Probe parsing has separate documented text/shift limits;
the interval/forward primitive has no 256/2048-bit rational cap.

The exponential retains 8..192 precision, zero/large-x shortcuts, halving,
q=bits+m+4, alternating Taylor cap512, series and EACH-squaring dyadic/unit
rounding, and final width contract. Bounds/refusal order will be checked
against one hash-verified in-memory Python source buffer under finite external
CPU, wall and memory budgets.

No Lean, existing compiler job, provider or workflow change, Rust rewrite,
child task, nine-parameter inverse or observed-confidence claim.
Next action: preserve the C++ source early, build, run focused exact differential
and property/boundary checks, publish/read back and obtain independent review.
