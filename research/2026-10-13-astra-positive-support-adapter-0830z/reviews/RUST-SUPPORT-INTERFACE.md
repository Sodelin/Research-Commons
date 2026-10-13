# Rust support-cap interface: scoped source review

Reviewer: Astra Rust integration lane, 2026-10-13 08:46 UTC.

**No blocking mathematical interface mismatch found in the pinned sources.**
This is a source-level review of the conditional distinct-support consequence.
It is not a Lean execution receipt, axiom-dependency receipt, native-code
refinement proof, or evidence of publication. The new adapter was uncompiled
at this review cutoff; its separate build lane owns that verification.

## Exact correspondence

| Obligation | Source-level finding |
| --- | --- |
| Levels and coefficients | The accepted provider defines `momentLevels L` as levels 1 through L and `sparsePolynomial` as the sum of `c k * x^(k.choose 2)`. Rust places zero-based coefficient `i` at exponent `(i+1)*i/2`; Python uses one-based `k*(k-1)//2`. These are the same indexing, including exponents 0,1,3 for L=3. |
| Polynomial identity | `positive_support_card_le_pred` requires a pointwise identity with the exact selected sparse polynomial. Each emitted wrapper proves that identity for its literal coefficients through `threeCoefficients_eval`; it does not substitute a polynomial with merely the desired roots. |
| Nonzeroness | The adapter derives polynomial nonzeroness from a concrete evaluation `p testPoint != 0`. The three wrappers reuse their emitted `p 0 != 0` proofs. Their nonzero constants are respectively 1/32,1/4,2. Rust rejects the all-zero coefficient vector; because the selected exponents are distinct, that arithmetic condition has the intended mathematical meaning. A general formal bridge from Rust's coefficient test to the adapter's evaluation premise is not supplied here. |
| Nonnegative certificate | Rust checks exact rational equality to a sum of `w*x^left*(1-x)^right*q(x)^2`, with `w>=0` and endpoint flags in {0,1}. The shared Lean kernel establishes the same factors' nonnegativity on [0,1]. The emitted proofs establish the literal polynomial identity by ring arithmetic. No floating-point premise appears. |
| Annihilation and moments | The general theorem takes exact zero weighted expectation, then derives roots; it does not take the cardinality bound. The three wrappers obtain zero expectation from the emitted proofs and their explicit moment equations at exponents 0,1,3. For a new runtime input, `sum(c*y)=0` alone does not bind `y` to a candidate bank: its actual moment equations remain a necessary premise. |
| Root interval | Both the general root premise and accepted `positiveCertificateGrid` use (0,1]. Endpoint 1 is retained, and the endpoint wrapper uses the certificate for moments (1,1,1). The larger [0,1] interval is used only for nonnegativity. |
| Meaning of support | `positiveSupportValues` filters positive-weight atoms and then applies `Finset.image value`. Repeated values count once. The conclusion bounds distinct positive-mass survival values, not the number of underlying atoms, configurations, graph vertices, or hybrids. |
| Zero mass | The direct `supplied_certificate_support_bound` separates the weight-zero case before applying the value-domain/nonnegativity premises. Zero-weight values can lie outside (0,1] and are excluded without renormalizing any weights. The three emitted wrappers preserve the stronger original `hv` premise on every atom, including zero-weight atoms; they do not by themselves implement the general zero-weight relaxation. |
| Numeric cap | The accepted `positiveCertificateGrid_card_lt` proves grid cardinality < L from polynomial nonzeroness. Subset cardinality and natural-number arithmetic yield <= L-1, matching Rust's `support_cap`. Rust restricts L to 1..8; the Lean theorem is conditional for arbitrary natural L. No bound is assumed as an input. |

For the three examples, the exact polynomial is
`p(x)=2*a^3-3*a^2*x+x^3=2*a*(x-a)^2+x*(x-a)^2`, with a equal to 1/4,1/2,1.
These prove the common sparse bound <=2, even though these particular
polynomials have just one positive root. The statement preserves the general
provider's bound and does not infer native acquisition of all certificates.

The low-level root-to-cardinality theorem intentionally accepts roots as an
intermediate premise. The direct supplied-certificate theorem derives them from
nonnegative summands and exact zero expectation. Neither assumes an unknown
source exists, a bounded representative exists, or the requested cardinality
conclusion. This packet alone supplies no source-faithful bank/moment binding,
physical admission, graph compression, future-row transport, or arbitrary-input
G3 decision. The native `source_existence=false` contract remains necessary.

## Reviewed source pins

Paths in the first group are relative to this packet. SHA256 values are source
bytes, not certificate IDs. Certificate IDs below name the preserved emitted
files and must not be confused with their source hashes.

| Source | SHA256 |
| --- | --- |
| `lean/Astra/PositiveSupportAdapter.lean` | `29782b7ff42fefd5b1634e20ea1f0c695714e5cd625c2730a255bbda656ab479` |
| `lean/Astra/EmittedSupportExamples.lean` | `953a4052074df758d3f832bd66d7237263d90325e50fc70a54fafa0ced602648` |
| `lean/Astra/CommonCertificateKernel.lean` | `1f35f9e11cef727b27ed30230a390ada2a32dfc50733ea0d4cb172fb7c053266` |
| `lean/Certificate_6a8a01d9ac2d8bbd890548efe86d75f823dc556163ba0159cc41a7790b3be8f7.lean` | `e06de07c68a4b2596b47deba5d46bc7d492ceabd0037a5e2b92c0d1c8536a16a` |
| `lean/Certificate_b20429b232b1124d54e85a7edeb6704cedae26a893a066a33e4556f774821d1b.lean` | `7f3818afac78dd66642eaf4971ae949f68818f85c1f096404c1fae4d86feb0bc` |
| `lean/Certificate_c083f0e7578cab70491391dbedd5ede62321198d6b43c100ce315896cabd75e0.lean` | `03514f3f24b5ab3473159ea105ca521a6977668f89c76a02f8b4e36f10d2859e` |

The exact accepted provider sources were read from
`research/2026-10-12-dot-accepted-connected-union1613-1737z/predecessor-check493/source-store/<SHA256>.lean`.
They agree with this packet's [selection](../PROVIDER-SELECTION.json):

| Selected module | SHA256 |
| --- | --- |
| `G4ActualObservableBankCertificate` | `9f177f98be496b02d981199f1b837f8eddadc77cc171307a0b1747a103806f8b` |
| `G4ActualSparseCertificateExistence` | `9ea04cbe390030381624d25b20be10751dff62f75d5d6e7752b88b9599a46418` |
| `G4ActualPositiveGridUniqueness` | `ee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787` |

The compared frozen implementation is in
`research/2026-10-13-astra-unified-solver-0645z`:

| Source | SHA256 |
| --- | --- |
| `rust/src/main.rs` | `c95189327d4d497c6536998a3451a31d69370049db7ca177d230aa3fc35b5e60` |
| `certificates.py` | `ce6ba92566e5ee009ca565476744db65555160f0e4a7d32b70ee07505b57f0b3` |

The review read the selected provider definitions, the complete adapter and
wrappers, the shared certificate kernel, and the three emitted proof bodies.
A literal-token scan found no `sorry`, `admit`, `axiom`, `unsafe`,
`implemented_by`, or `native_decide` in the new adapter/wrappers or emitted
files. Such a source scan does not replace `#print axioms` on compiled results.
No compiler, native executable, or finite-test corpus was run for this review;
the previously published implementation receipts retain their original scope.
