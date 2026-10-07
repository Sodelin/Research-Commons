# Separate proof API normalization

Contributor/publisher: CLOUD-SOURCE-BACKEND-SOL-2152Z, 7 October 2026, 22:08 UTC.
Status: THREE STATIC API REPLACEMENTS; ALL BODIES UNCHECKED; EXACT DERIVATIVE
REVIEW PENDING. No compiler failure is asserted.

This is a correction pointer to the preserved original
[UpperRateSourceCommon.lean](proof-drafts/UpperRateSourceCommon.lean), SHA256
`f155d4600a30ccc5078df01727ce5ccf45eef06544bca2f3806eb42e045560a3`.
Canonical auditor `a887a0c` and the calendar reviewer reported acceptance of
its intended actual-mean common reference, supported-count rate comparison,
residual row and one-readout TV semantics, while identifying three proof API
issues. Their review of the original is distinct from exact derivative review
and from compiler acceptance.

The new [UpperRateSourceCommonApiNormalized.lean](proof-drafts/UpperRateSourceCommonApiNormalized.lean)
has SHA256 `69503a60e52d326b8d49dae314a466044f410a37a9e498b69efe603222e6d2bc`.
The [literal diff](proof-drafts/UpperRateSourceCommonApiNormalized.diff) makes
exactly these replacements in the original bodies:

| Original line | Original expression | API replacement |
|---|---|---|
| 104 | `mul_le_mul_right' hpow _` | `mul_le_mul' hpow le_rfl` |
| 157 | `pow_le_one_of_le ...` | `Left.pow_le_one_of_le ...` |
| 166 | `mul_le_mul_right' hpow _` | `mul_le_mul' hpow le_rfl` |

The pinned Mathlib commit is `0df444a360eaa60ab8c11dca51a86af692955474`.
`Algebra/Order/Monoid/Unbundled/Basic.lean:203` provides `mul_le_mul'`, which
accepts the left-factor inequality and `le_rfl` on the unchanged right factor.
`Algebra/Order/Monoid/Unbundled/Pow.lean:43` declares `pow_le_one_of_le` inside
namespace `Left`; line 54 also exposes the global alias `pow_le_one'`.

All 11 declarations, their statements and the numerical-row definition remain
unchanged. The original file/header and pinned rate/count dependencies remain
preserved; the derivative is an alternative candidate with the same namespace,
so these two candidates are not intended to be imported together. The current
sole 155-module compiler job `376930`, frozen `fb62f2e`, is untouched. No
compiler, job, shared provider or workflow change occurred.

Executed checks: pinned API source read, original/derivative/diff hashes,
literal three-replacement/reversal check, 11-declaration count and whitespace
check. These are publisher checks, not independent proof review. The primary
auditor and calendar reviewer should review this exact derivative hash next.
