# Private rational compression: executable checkpoint

Contributor: Codex Rust implementation role, 10 October 2026, 16:58 UTC.
Claim labels: **tested result** for the native checks below; **sourced finding**
for the separately audited mathematical consumer. This is an additive private
component under the [reviewed contract](G6-RATIONAL-COMPRESSION-CONTRACT-2-20261010T1632Z.md),
not a public runtime or source-admission promotion.

The [crate](../rational-compression/README.md) now returns exact positive weights
on original input indices for M=2,3,4. It reproduces the existing Fraction
first-pivot/first-free RREF and elimination, filters zero weights without merging
equal atom identities, and preserves common mass plus every required geometric
tail moment. Its independent native certificate checker calls no elimination.

The [attribution inventory](G6-RATIONAL-COMPRESSION-READINESS-20261010T1613Z.md)
distinguishes the compatible Oct1 geometric cone reduction and current
4760fcd Fraction implementation from the Sep30 probability-mixture operator.
The latter supplies earlier Fraction RREF precedent but different moments.
No approximate Bernoulli-factor or positive network reconstruction is imported.

## Actual executable checks

The separate offline release [build receipt](../evidence/rational-compression-build-1/RECEIPT.json)
records build success and **10 focused Rust tests**: nine certificate/resource
tests and one encoding-failure exit test. Existing unused-import warnings in
the frozen dependency are preserved; that dependency was not edited. The
formatter component was unavailable, recorded as a preparation observation.

The fresh [native review](../evidence/rational-compression-review-2/RECEIPT.json)
passed **8 successful certificate cases and 25 controls**. The three inherited
M=2,3,4 cases have identical selected indices/weights and elimination-step
counts to the attributed Fraction implementation. A separate direct Fraction
checker validates original-index membership, positivity/cardinality, mass and
all tail equations. Applying each one common compressed list to every eligible
saved actual original-source literal row passed **331 transfers** (8+65+258).
The existing actual Lean/Rust population tables were reused without executing
either old producer or rerunning their kernel audit.

Controls cover domain-before-budget validation, all-zero/empty and repeated
atom values, matrix-before-coordinate generation, exact/one-below limits,
rational exhaustion at INPUT/MOMENTS/RREF/UPDATE/CERTIFICATE, malformed JSON,
foreign raw binding, index and positivity errors, a positive same-mass wrong-tail
forgery, explicit-null result extras and the M=2 input-bit checker gap. The
checker deliberately permits an alternative valid certificate while leaving
producer-work and exhaustion flags false. Arithmetic checks every operand and
reduced result; certificate integer decoding derives its length guard from the
explicit rational-bit budget before gcd normalization.

The [CLI review](../evidence/rational-compression-cli-review-1/RECEIPT.json)
also checks no-argument stdin output against the bound file result, and confirms
refusing an existing review-output directory preserves all 162 existing files.
Controlled native runs used 45-second wall, 30-second CPU and 768 MiB address
limits. These finite checks are not a general runtime/bit-complexity theorem.

## Preservation and identities

The private ELF remains outside the repository:
`/workspace/scratch/lean-rust-parity-native/runtime/rational-compression-candidate-1/rational-compression-probe`.
SHA256: `f5822d80fdc9a68d967edf95406f9d9a3cc4f6bb56b104418a19ee69e72671d8`.
[Final identity inventory](../evidence/rational-compression-review-2/FINAL-IDENTITY.json)
pins every new source, contract, build and review.

The [final derivative freeze](G6-RATIONAL-COMPRESSION-SOURCE-FREEZE-3.json)
has SHA256 `d9b62b46f0319bd782f922ca00b297fc2dfc4c9866dd4c1294e95399693802ec`.
All **100 accepted source guards and 29 existing native guards remain unchanged**;
16 registry archives and 624 unpacked files were checked against their archive
bytes. No accepted library/frontend/helper/app/PINS source was edited. No old
117-case suite or unchanged calendar native tests were repeated.

Freeze1 and its reviewer bytes remain in history. Freeze2 records the reviewer
fresh-output error-receipt correction. Freeze3 records the reviewer argument-name
correction (`atoms` conflicted with the `limits.atoms` keyword); the
[first failed review](../evidence/rational-compression-review-1/FAILURE-RECEIPT.json)
is preserved. Both corrections affect only the Python review harness. Rust
compile-input bodies and the private ELF are identical across all freezes.
Root's earlier source-review mismatch against freeze1 is a historical observation,
not overwritten by this derivative.

## Formal scope and next consumer

The separately accepted
[rational mathematical consumer](../../reuse/sources/G6RationalCompressionCertificate.lean)
has source SHA256 `353521bc18e3fab1fce6fe6141bc4d5006ceb3d07cc27b9728d66b921abedd3e`;
its [98-module certificate](../../lean/RATIONAL-COMPRESSION-CERTIFICATE.json)
has SHA256 `d1e18087da091b29dcd52b57fb559f6a21597858cf1af129f984c109ee3f3607`.
It casts checked rational mass/tail identities to the accepted real compression
theorem and its whole original-population-row consumer. This does not establish
JSON/parser/RREF producer refinement, totality or arbitrary-real extraction.

Six exact request/result pairs were handed to reuse and the sole Lean scheduler:
`historicalM2`, `historicalM3`, `historicalM4`, `empty`, `allZero`,
`sameMassWrongTail`, under the accepted native review folder. The last retains
positive weights and total mass while perturbing its two distinct selected
weights by +1/1000 and −1/1000. Actual finite Lean check evaluation of these
saved certificates is the next action; it is pending at this checkpoint.

Rational supplied survival atoms are not automatically the generally
transcendental survivals of a rational physical calendar. Successful certificates
do not admit a source graph, construct common-bigonom positive factors, prove
resource exhaustion or close the full solver's remaining G6/G7 assemblies.
