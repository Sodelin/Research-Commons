# Native acquisition from three supplied moments

**Tested increment, 2026-10-13 08:20 UTC.** The existing
`common-certificate-checker` crate now has an explicit bounded singleton
generation mode. It reuses its exact rational parser, `BigRational` arithmetic,
and complete supplied-certificate checker. The original `COMMON_CERT_V1`
checking wire, output, caps and refusal semantics remain unchanged. No new
crate, dependency, Cargo lock selection, solver backend or approximate arithmetic
was introduced.

The prior published source/checker baseline remains available at commit
[`9031b31be9d831199b5e8ccedcf98045df82d720`](https://github.com/Sodelin/Research-Commons/tree/9031b31be9d831199b5e8ccedcf98045df82d720/research/2026-10-13-astra-unified-solver-0645z).
Its executable was retained in the original target directory and independently
hash-checked before compatibility testing. The new version was built into a
different, initially fresh target.

## Exact wire and outcomes

```text
COMMON_GENERATE_SINGLETON_V1 1 1/2 1/8
```

This mode consumes exactly three supplied rational tokens `(y1,y2,y3)` after
the version tag. They are the moments at sparse exponents `0,1,3`, not three
additional observations inferred from a source. Input uses the existing
80-byte/128-bit-after-reduction exact rational profile and the same 256 KiB
ASCII wire cap. Missing/extra tokens, floats, invalid denominator/sign/spelling,
invalid UTF-8 and over-cap input are refused with exit 1 and `REFUSED` on stderr.

If `y1=1`, `a=y2` lies in `(0,1]`, and the supplied `y3` is **exactly** `a^3`,
the program constructs

```text
p(x) = 2*a^3 - 3*a^2*x + x^3
     = 2*a*(x-a)^2 + x*(x-a)^2.
```

It constructs the two weighted-square terms, keeps the original three input
token spellings in the emitted moment fields, renders computed coefficients
as exact reduced rationals, and sends the complete resulting certificate
through the existing checker. For the input above the exact successful output
is two lines, with exit 0:

```text
GENERATED_AND_CHECKED support_cap=2 source_existence=false
COMMON_CERT_V1 3 1/4 -3/4 1 1 1/2 1/8 2 1 0 0 2 -1/2 1 1 1 0 2 -1/2 1
```

The second line is directly accepted by both the preceding and current native
checker. The reported support cap is the existing `L-1` bound with `L=3`; this
increment does not silently tighten or replace the selected provider statement.
Successful certificate generation does not establish that an actual source
realizes the supplied moments, and it does not certify source existence.

Exact rational data which do not fit this sufficient profile return exit 2:

```text
UNKNOWN supplied_moments_do_not_fit_singleton_generator source_existence=false
```

If the supplied moments fit their input caps but computed certificate
coefficients exceed the accepted language, the result is also exit 2:

```text
UNKNOWN generated_certificate_exceeds_supported_exact_language source_existence=false
```

For example `a=6000000000000/6000000000001` and its supplied exact cube fit the
128-bit moment caps, while the computed constant `2*a^3` needs an additional
numerator bit. This is bounded acquisition exhaustion, not evidence that such
a moment profile or source is impossible. Zero survival is not admitted by the
singleton generator; endpoint one is admitted. Unsupported profiles and
transport refusals never become a mathematical NO.

The unified solver exposes this as optional `--native-generation` alongside
the existing Python `generate_singleton` task. Root integration requires exact
agreement with the independently constructed Python certificate wire, then
rechecks the emitted certificate through the existing native checker. Without
that flag, the former checker-only invocation remains supported. The exact
native interface itself does not accept a latent target or request more data.

## Formal correspondence and trusted boundary

The cubic identity, nonnegativity, exact annihilation and nonzero polynomial
facts correspond to the existing
`Astra.CommonCertificateKernel.singleton_generator_identity`,
`singleton_generator_nonnegative`, `singleton_generator_annihilates`, and
`singleton_generator_nonzero` declarations. Their formal source and actual
Lean execution remain in the selected package receipt; this Rust increment
does not change those declarations or strengthen the conditional physical
representative result.

The code computes over exact rational arithmetic. Its parser, coefficient
construction, string emission, Rust compiler, exact arithmetic libraries and
correspondence to Lean remain trusted native implementation boundaries. Finite
agreement and a semantic Lean theorem do not constitute a universal refinement
proof. The missing physical representative/admission/observation bridges and
general G3 remain separate obligations.

## Execution and provenance

| Evidence | Actual result | Fresh/reused distinction |
| --- | --- | --- |
| `evidence/rust-generator-unit` | Eight Rust test groups passed; exit 0, 3.50 s, peak child RSS 211,775,488 bytes | Fresh compiler output and exact dependencies in the new target. Includes the five previous checker groups and three generator groups. |
| `evidence/rust-generator-binary` | Executable build exit 0, 0.50 s | Fresh executable, using dependency objects just built for the unit tests. |
| `evidence/rust-generator-differential` | All 158 bounded cases passed | 125 exact generated-wire agreements, eight UNKNOWN cases, 17 rational/transport refusals, eight malformed-frame refusals. Each generated certificate also passed both old and new standalone checkers. |
| `evidence/rust-generator-checker-regression` | All previous 556 process comparisons passed | Tests the unchanged default checking protocol with the new executable. |

`test_native_generator.py` retains exact finite-case inputs, native outputs,
exit codes, Python outcome, and both checker results incrementally in
`evidence/rust-generator-differential/CASES.json`, SHA-256
`1b9dd46065d8d0a24479432a0a447ff1358b77c5e284264ff6d73b7d674d2483`.
The deterministic corpus includes small rational singleton laws, near-cap
coefficients, reducible token spellings, endpoint one, zero/negative/out-of-range
survival, unsupported cubic moments, derived overflow, input overflow, malformed
ASCII/UTF-8, wrong versions and oversized frames. There were no failed builds
or resource-pressure stops in this increment.

* New `rust/src/main.rs` SHA-256:
  `c95189327d4d497c6536998a3451a31d69370049db7ca177d230aa3fc35b5e60`.
* New executable SHA-256:
  `3d7678fac5ba8138b28a08e40c6ca8ac2b3a6e13267350d48480997e53f27ef7`.
* Preserved prior executable SHA-256:
  `1a508f23613bb527e5605c806fb8215ed6a16adeed4c4147658236790064d805`.

The current executable is at
`/workspace/scratch/astra-certificate-generator-target/debug/common-certificate-checker`.
The prior executable remains at
`/workspace/scratch/astra-certificate-target/debug/common-certificate-checker`.
These are local execution artifacts rather than public binary-distribution
claims. Source, build configuration, finite tests and receipts are the published
reproduction artifacts. All native builds were locked, offline and single-job;
all Rust test harnesses used one test thread under the existing resource guard.
