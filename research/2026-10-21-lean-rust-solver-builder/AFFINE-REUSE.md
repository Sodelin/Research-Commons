# Existing affine engine and proposed Lean certificate receiver

The existing Rust engine at4e556c4ae6225d18fabf30bc7d3347a468749ebc
already implements strict Fourier--Motzkin projection, deterministic rational
back-substitution and independent original-row witness/Farkas checking.
It is reused, not replaced. Exact inspected pins and interface limits are in
evidence/EXISTING-AFFINE-REUSE.json. No compiler, replay or benchmark ran here.

Its ordered projection and coordinate choices match the retained executable
Lean solveList design. That source comparison is not a universal Rust/compiler
refinement theorem. The existing original native_rc1 facade admits AFFINE/LAW;
CHART remains outside this entrypoint even though the old core contains a chart
module. AFFINE witness/exclusion concerns its supplied finite matrix, and LAW
checking is same-compiler replay. Neither acquires source admission.

lean/AffineCertificateReceiver.lean is NEW UNCHECKED SOURCE. It reuses the
original Row, checkRationalWitness and rationalWitness_real. Its positive
receiver retains every original row through finite-image membership. The new
finite rational checkFarkas predicate matches the existing Rust check_exclusion
algebra: nonnegative weights, zero combined coefficients, negative bound OR
zero bound and a strict original row with POSITIVE multiplier. Ordered original
row indices remain distinct for multipliers, including duplicate rows.

The proposed theorem concludes infeasibility of that exact finite real matrix.
It does not certify a native parser, binary execution, original source/chart
translation, complete source registry or unrestricted physical NO.
lean/AffineCertificateExamples.lean prepares an interval witness, a strict
contradiction and the essential zero-multiplier strictness control. They are
authored proof candidates, not new native runtime reports or checked theorems.

The existing Lean owner retains compilation/assembly scheduling. Any future
check must bind these exact source bytes, imports, complete selected types and
axioms to its actual context. Native execution remains held for the existing
encrypted first-writer/controller binding; no old job/profile is replayed.
