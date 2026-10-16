# FiniteOrbit diagnostic repair r1

15 October 2026 (Pacific); prepared 16 October 2026, 00:52 UTC. **SOURCE CANDIDATE, UNCOMPILED, fresh independent source review pending.** This isolated proposal changes no frozen package, used build leaf, dependency, compiler option, toolchain or accepted result.

## Actual trigger and evidence boundary

The existing desktop route supplied an actual failed run: the first two modules completed, `Semi.Core.FiniteOrbit` then failed, and the six later modules including the final audit were not reached. The two reported errors are nested simplifier recursion at original line 75 and an implicit-setoid type mismatch at original line 148. The supplied original stdout/receipt pins are preserved in `REPAIR-MANIFEST-01.json`. This source owner read the exact corresponding source/API contexts; it did not replay the job or claim an independent full raw-log read.

Baseline: [frozen FiniteOrbit](https://github.com/Sodelin/Research-Commons/blob/55eecf2a337a43c0a9b958592dde1e50a6bf405d/research/2026-10-15-astra-semi-foundations-2124z/source/Semi/Core/FiniteOrbit.lean), 6097 bytes / SHA256 `4f02600853fdf56aa349194b359a5813d1d4672ecb3474f8b286a913426fe2f4`.

## Exactly two proof edits

1. In `orbitDistance_comm`, replace the failing reverse-rule `simp` invocation with a local cancellation equality. `map_inv M.action g` identifies the image of the inverse with the inverse permutation; `Equiv.apply_symm_apply` cancels that permutation with its inverse. `simpa only [hcancel]` then specializes the existing invariance equality. No global simplifier rules or resource bounds are changed.
2. In `quotientDistance_eq_zero`, lambda-bind each implication and explicitly select `s := M.orbitSetoid` for both `Quotient.sound` and `Quotient.exact`. Their relation is definitionally `M.Related`, as required by the existing target. No orbit relation or quotient statement is changed.

The inspected pinned APIs are `map_inv` in Mathlib's group-hom definitions, the inverse-permutation implementation in group endomorphisms, `Equiv.apply_symm_apply` in equivalence definitions, and the `s` parameter of `Quotient.sound`/`Quotient.exact` in Lean 4.33.1 `Init.Core`. Exact source pins are recorded in the manifest. The held Core source Git blob was independently matched to the official pinned source response.

## Exact successor and patch

| Artifact | Bytes | SHA256 |
| --- | ---: | --- |
| `FiniteOrbit.lean` | 6286 | `538a0c3fdbb82e93c51f70f7d26e590ca309797da72ffc05938b7e0b84676cf9` |
| `FiniteOrbit.patch` | 1064 | `98efd9fddcf50097c5d85c2b1bdec328826ec75103bb80d49b6e2256fe706a38` |

Actual byte checks: the original file hash matches its frozen pin; inverse application of the two literal replacements exactly reproduces the baseline; an independent unified-hunk replay reproduces the successor; the patch has exactly two hunks. Imports, statements, assumptions, definitions, existing attribution and all bytes outside the two replacements remain unchanged. Nonfatal warning sites are preserved. No `maxRecDepth`, heartbeat or other resource increase is introduced.

## Remaining gap and next bounded action

These edits are proposed elaboration repairs, not a kernel result. The repaired module, downstream modules and final type/axiom audit still require actual checking. Nothing here upgrades the first two reported module successes to package acceptance or supplies a scientific/source-model theorem.

The existing independent reviewer can review these exact two edits. Any later desktop check must use a **fresh explicitly selected finite record and updated source authentication**, retaining the entire consumed job's original source, outputs, logs and failure. The consumed record must not be replayed. No leaf or package replacement, compiler/checker/exporter run, automatic restart or dependency acquisition is selected here.

The separately proposed challenge statements retain the same intended statements; their old source-body hash is historical and must not be silently reused as the successor's identity. No new challenge implementation or broad nine-body review is opened by this repair.
