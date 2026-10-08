# Rational residual coefficients: independent source and API review

Reviewer: Cloud Sol `/root/source_backend_review_sol`. Candidate author: Cloud internal Lean lane. Observation: 8 October 2026, 03:01 UTC. **SOURCE/API ACCEPT: all three definitions and eleven proof bodies inspected; no blocking semantic or definite static API issue found. Compiler UNCHECKED; outside176.**

The immutable candidate is [RationalResidualCertificate.lean](../2026-10-07-cloud-g6-sol-ultra-1601z/verification/preparation/rational-residual-certificate-0245z/RationalResidualCertificate.lean) at `0ace76f0d81cc61f379852399bec39f163b0d354`, SHA256 `49eba2288f7e32b415b8409c2ddeb8a39f192374d31cad40132a5ae6771a7386`, 6,989 bytes. There are fourteen selected declarations: three computable rational definitions and eleven proof bodies. The source's print commands were read, never evaluated.

This is a scalar coefficient correspondence and one same-source vector bound at an exactly supplied rational mean. It does not prove the returned Python certificate invariant, runtime program semantics, source-state table enumeration, arbitrary-real input access, or the full G6 master. [Exact pins and read depths](REVIEW-PINS.json) preserve these distinctions.

## The law being checked

Write `t_k=q^k/k!`, `S=sum(k=0..K)t_k`, `T=t_(K+1)`, and `U=S+2T`. The candidate's retained mass is `S/U`. Its count coefficient is `t_k/U` for `k<=K`, zero otherwise, plus `2T/U` **only at count zero**. Thus the finite sum is `S/U+2T/U=1`. This is the original residual-lumped law, distinct from the existing normalized coefficient `t_k/S`.

For nonnegative `q`, `S>=1` and `T>=0` prove `U>0`, so the divisions used in the probability properties are legitimate. Normalization and support do not require the tail-ratio guard. That guard is required later to compare the common retained mass with the actual Poisson prefix and certify the TV error. Zero mean is included; at `q=0` the error is zero. At `K=0` all retained and residual mass is at count zero, consistently with the stated coefficients.

## Complete body and API check

| Declaration / source lines | Finding |
|---|---|
| Three definitions, 19–28 | Denominator is exactly `S+2T`; retained mass is `S/U`; residual coefficient has cutoff support and a separate zero-count error term. No normalization by `S` is substituted. |
| `rationalDenominator_pos`, 30–35 | Actual `rationalPrefix_one_le` and `rationalTerm_nonneg` give a strictly positive denominator; the linear argument has the right sign. |
| `rationalRetained_bounds`, 37–47 | Nonnegative division and the pinned `div_le_one hU` direction reduce the upper bound to `S<=U`. Both use the proved positive denominator. |
| `rationalRetained_deficit`, 49–54 | The explicitly nonzero denominator is definitionally the same `U`. Clearing it proves `1-S/U=2T/U`, matching the actual `rationalError` definition. |
| `rationalResidualCount_nonneg`, 56–66 | Both finite retained terms and zero residual are nonnegative. The local denominator/term/error facts cover all four cutoff/zero branches. |
| `rationalResidualCount_support`, 68–72 | `K<k` gives both `not(k<=K)` and `k!=0`; both summands vanish. The residual at zero cannot introduce support above a natural cutoff. |
| `rationalResidualCount_sum`, 74–94 | Membership in `range(K+1)` yields `k<=K`. Rewriting **backwards** with actual `Finset.sum_div` changes the sum of quotients to `S/U`. Actual `Finset.sum_ite_eq'` has index equality `k=0`, the needed orientation, and `0` belongs to this range even at `K=0`. Add the deficit identity to obtain one. |
| `rationalDenominator_real`, 96–100 | Pinned `Rat.cast_add`, `Rat.cast_mul`, `Rat.cast_ofNat` and the actual rational term/prefix correspondence produce the real denominator in the same order. |
| `rationalRetained_real`, 102–105 | Actual `Rat.cast_div` and denominator correspondence give precisely `ResidualPrefix.residualMass`. This is an algebraic cast identity; it is not an identification with normalized prefix mass. |
| `rationalResidualCount_actual`, 108–113 | Original `residualCountReal_coefficients` has the same cutoff conditional, denominator and zero error. Cast/conditional simplification and `(a:Real)=(q:Real)` match both retained and residual terms, including count zero and counts above `K`. No desired coefficient equality is supplied as an assumption. |
| `cutoff_residual_deficit`, 115–118 | The deficit is rewritten to the existing rational error. The second component of actual `cutoff_accepts` bounds that error by `epsilon`. Leastness and termination are inherited from `RationalCertificate`, not newly executed here. |
| `actual_source_residual_tv_cutoff`, 128–145 | The first component of `cutoff_accepts` is `2q<=K+2`; exact casts and the exact mean identity yield the guard required by original `actual_source_residual_tv`. The second component casts to the real error bound. The existing same-source theorem then bounds the stated vector TV; transitivity gives `<=epsilon` in the correct direction. |

The underlying actual source is unchanged: `sourceTimeKernel` is `countPMF(globalClockRate(r)*t).bind sourceIteration`, and count-zero `sourceIteration` is `PMF.pure` of the same entering state. `residualSourceVector` scales the normalized finite actual-source prefix by residual mass and adds the residual to that same count-zero iteration. Network, original sample map, Code state, rates and duration are the same on both sides. The candidate assumes exact numerical mean equality, not a desired law, domination or approximation conclusion. Its finite carrier assumptions match the inherited APIs.

The candidate allows any positive rational error budget. The preserved Python reference additionally requires tolerance less than one. No equality of their complete input/refusal contracts or returned runtime objects is established by these scalar bodies.

## Exact source and evidence boundaries

All three candidate files equal their immutable Git blobs. All eight contextual source pins equal the candidate and frozen166 input `4456ed1e340872b8a5de31b14974f4c45163cb6f`; their hashes also match [the preserved166 input manifest](../2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37716267154-PASS/inputs-recovered.json). The saved receipt reports that inherited build passed. I authenticated these source identities and inspected its leading result; I did not replay compilation or freshly audit its full terminal/inventory. That inherited result does not compile this new candidate.

`RationalCertificate` and `ResidualPrefix` were read completely. `SourcePrefix`, `TaylorCertificate` and `SourcePoissonKernel` were read at the actual coefficient, tail/guard and source-law APIs recorded in the manifest. `ResidualProgram` and `UpperRateSourceCommon` are contextual identities, not newly accepted full bodies in this review. This is not a fresh transitive audit of all eight providers. Five local Mathlib files were pinned to `0df444a360eaa60ab8c11dca51a86af692955474`, including the generated additive `sum_ite_eq'`, `sum_div`, positive-denominator `div_le_one`, and rational casts. Their relevant static signatures and directions agree.

Both preserved Python reference files were authenticated against their immutable pins. Targeted source reading confirms that `PrefixCertificate.weights` divides by `upper_exp=S+2next` and adds its deficit at zero, while `count_certificate.weights` returns the different normalized law. Neither implementation was imported or run. This reading is not a program-semantics proof.

Only source reads, Git/SHA/byte/blob checks and owned review-note preservation were performed. No compiler, print command, test, numerical or solver harness, workflow/Actions, API/SDK, or private product activity occurred. Failed176's frozen inputs and all providers remain unchanged. The exact new candidate remains **compiler UNCHECKED**.

The next executable implication is a proved invariant of the returned Python object: initial term one, length `K+1`, exact Taylor recurrence, identified partial/next/upper endpoint, and therefore weights equal to these rational coefficients. Actual source-state enumeration and its encoding, arbitrary-real or certified enclosure admission, a shared feasible source/bank across observation rows, and effective outer-cell/Hausdorff assembly remain separate. A scalar source/API acceptance or future successful compilation does not close those obligations or full G6.
