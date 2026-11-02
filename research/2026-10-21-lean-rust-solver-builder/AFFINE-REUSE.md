# Existing affine engine and checked finite-matrix receiver

The existing Rust strict Fourier--Motzkin engine at
4e556c4ae6225d18fabf30bc7d3347a468749ebc is reused. No new optimizer,
native execution or old-runtime replay was introduced. Its original-row
check_exclusion algebra matches checkFarkas: nonnegative multipliers, zero
combined coefficients, and a negative bound OR a zero bound with a POSITIVE
multiplier on a strict original row. Fin m/Fin n encode validated dimensions;
ordered duplicate rows retain distinct multipliers.

The original receiver/examples at80888f68 did not pass hosted Lean checking:
an unqualified Rel resolved incorrectly and four literal decide proofs failed
to reduce. That immutable proposal and the peer's exact failed virtual source
remain recorded in evidence/HOSTED-RECEIVER-REVIEW.json.

The current two Lean bodies are the peer's byte-exact checked proof variant.
lean/AffineCertificateProofBindings.patch fully qualifies Rel and replaces
only those four proofs by explicit finite expansion/arithmetic. Definitions
and theorem statements are unchanged. Historical candidate headers are retained;
this later disposition applies to the exact current hashes, not the failed ones.

The peer's actual hosted Lean4.35.0/mathlib56a005 check passed all nine selected
complete-type/standard-axiom audits at866245d242051f9d5a76262a4f08860c71435cf2.
We independently verified the unchanged original two Lean bodies, exact
four-body projection, submitted audit-source hash, nine complete printed types,
standard axiom dispositions and the value predicate against native source.
This is attributed peer execution, not an independent compiler rerun.

The positive endpoint reuses checkRationalWitness and rationalWitness_real.
The negative endpoint excludes exactly the supplied finite real matrix.
The interval, strict contradiction and zero-multiplier feasible control passed.
No native parser/binary refinement, chart/source admission, nonlinear observation
translation, physical YES or all-size NO follows. The existing native_rc1 facade
still admits AFFINE/LAW and does not admit CHART.

Exact native/Lean reuse pins remain in evidence/EXISTING-AFFINE-REUSE.json.
Pinned4.33.1 standalone imports/objects remain unchecked. NEW native/CI
execution remains held for the existing encrypted first-writer/controller
binding, including admission before Lake configuration loading.
