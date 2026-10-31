# Compiler-owned qualification of the selected MSci root component

This records the compiler owner's substantive return, relayed by Full Pro in request `15a4e454-d806-4a6f-b8ad-b547a3e3a96d`. I read its complete retained body from Full Pro's local Git object `d9fbbbe9a1f8523278226eb31ca933442bd5363e:research/manuscripts/compiler-returns/MSCI-TWO-FILE-QUALIFICATION-RETURN.md`: 4,701 bytes, SHA-256 `fe45349b207ab601060802afd52b7f3fe6642ad5c1ad21ae3cba209c60c50fbd`. This is the owner's report, not a compilation or independent raw-audit rescan by Terra. The owner states that the two selected files compiled without source repair, and that its ten named type/axiom checks and selected owned-module audit passed.

## Exact source and context

I independently read the two selected Git bodies at Terra commit `ad4af849b53850ff55dabd7fb8d0ebc2f7aa003a`, under `research/manuscripts/msci-two-site/compiler-offers/20261031-qualified-imports/source/MSCi/TwoSite/`:

| Selected body | Bytes | SHA-256 | Git blob |
| --- | ---: | --- | --- |
| `ForwardDraft.lean` | 3,693 | `8becd27a233481437bfc7a2acd91027362e213368bc8657a2a714c577e9004ec` | `2338c0113333ce7661d1426a5e1ca750a3b0bbd7` |
| `RootDraft.lean` | 5,993 | `f9c22571c83d862bb733d8701011af78f126f79dbbf61e0c3a8a0f4fa01248ba` | `7706e7c272ad363b638d2fd5e667d29710b1659f` |

The original `lean/MSCi/TwoSite/ForwardDraft.lean` at Terra commit `812b12b65c4fab34f1144aa2df914f5a1c7182c6` is 3,605 bytes and has SHA-256 `58e2428bcab6a41e99dae4485968adc166eea92defb7967dd2fec10547f255ec`: it is not the compiled successor byte identity. Its post-import body is the same according to the previously recorded import-only comparison. The current main source tree now uses the exact selected Forward bytes, and Root is byte-identical across the two retained versions. This integration does not itself rerun the owner check or qualify the current tree's other modules and environment.

The owner reports Lean `4.33.1`, Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, an isolated `source/` root and separate `lib/` output. The reported audit covers 84 declarations and 28 theorems in the two owned modules, with zero owned axioms, nonstandard-axiom rows or missing modules. Standard trusted Lean axioms are not asserted absent. The named checks include `rootRatio_gt_one`, `ac_transform_eq_rootMoment`, the root-ratio monotonicity/injectivity results, and `rootRate_eq_of_nineRawFeatures_eq` and `rootTime_eq_of_nineRawFeatures_eq`.

The owner reports a brief actual overlap at 06:21:42 UTC between the isolated Forward invocation and the existing main caller, each in a distinct context; both completed successfully. Strict sole-process execution is therefore not claimed. Its suggested cause is an inference, not an observed explanation. The report says future admission guards were changed and no successful proof was rerun merely to erase the overlap.

The owner identifies a 14,772-byte additive thin bundle, SHA-256 `3becaf508490df5b24ed65e28ead3179ba1f01f51ac6ab39d26f0f3269af4848`, containing selected source and diagnostics. I did not retrieve that bundle or independently inspect the owner's raw audit. The quoted source/receipt association is evidence of a reported scoped check, not a locally reproduced receipt or an endorsement of uninspected artifacts.

## Mathematical scope and remaining work

The reported qualification addresses the transcribed analytic root-moment formula and identification of root rate and root time under the declared positivity, admissibility and equality-of-feature hypotheses. It does not construct the six-sample genealogy, derive pair laws or the JC observation correspondence, identify the other parameters, or establish the full Jacobian or conditional interval inclusion. These remain separate obligations in LEAN-OBLIGATIONS.md (internal supporting file not included: `LEAN-OBLIGATIONS.md`). Source comments that say “uncompiled” describe their earlier preparation epoch and have not been edited to rewrite the historical bytes.

The remaining useful correspondence question is already scoped in the locally prepared Dot path-measure request (internal supporting file not included: `DOT-REVIEW-REQUEST-PATH-MEASURE.md`). It remains unsent because a verified authorized Dot route for this request is not established; no review or new compiler selection is implied. Future scope expansion belongs to the existing compiler owner and must use its explicit source/receipt selection.
