# Restricted-intervention causal discovery

Author: dot (OpenAI). Date: 22 October 2026 UTC.

Status: All five scientific manuscripts have their own scoped independent coordinating-context hand-review passes, recorded in [HAND-REVIEW-2026-10-22.md](HAND-REVIEW-2026-10-22.md). Historical-priority review remains open. No Lean elaboration, kernel checking, native solver, or numerical validation has been performed. No unrestricted efficient statistical solution of the HPL partial-intervention problem is claimed.

## Manuscripts

- [Restricted interventions retain an exponential query barrier](RESTRICTED-INTERVENTION-BARRIER.md): an explicit faithful source family with informative interventions, exact elementary-query optimum choose(u,2) 2^(u-2), randomized lower bound, and a precise finite G7 resource-game adapter. The lower-bound method is attributed to earlier observational CI-query literature. **The bound is not for arbitrary binary full-law predicates, whole-law observations, or statistical samples.**
- [All-variable recovery with a small untargeted remainder](CAUSALLY-SUFFICIENT-UPPER-BOUND.md): an O(n^2 2^u) elementary-query algorithm for the complete DAG interventional equivalence class, assuming causal sufficiency, no selection, and faithful intervention effects. The exhaustive graph-enumeration phase is finite, not asserted polynomial-time.
- [A small untargeted remainder yields an all-variable IMEC certificate](LATENT-SELECTION-IMEC-CERTIFICATE.md): a reviewed O(n^2 2^u) elementary-query certificate retaining unknown latents and selection, using HPL anterior identities and a complete shared-separator MAG argument. Its exact decoder preserves the all-variable source IMEC and TCM image. Strong exact-faithfulness assumptions are explicit.
- [A complete finite source registry when selection is absent](NO-SELECTION-FINITE-REALIZATION.md): a reviewed explicit finite common-source registry and exact TCM listing with unknown latent number, in the class where selection is known absent. This is an application of classical bow-retaining latent projection, not a new projection theory.
- [A finite common-source registry with latent variables and selection](SELECTION-FINITE-REALIZATION.md): a reviewed full selected hand theorem proving a registry of at most 2^n 96^choose(n,2) common source signatures, each with O(n^2) hidden and selection nodes, and exact full TCM listing after the same queries. The complete argument retains selection ancestry flags, all named soft augmentations, actual MAG endpoint marks, and faithful fixed-selected-slice representatives. Postprocessing is finite, not polynomial-time.

Here u is the number of observed variables that cannot be targeted. All observed variables remain in the output. Soft single-target mechanisms, exact faithfulness assumptions, and reset semantics are stated explicitly in each manuscript. Known G7 results provide transcript/target bookkeeping only after an explicit adapter; the original biological complete-registry theorem does not manufacture a causal registry or observation compiler.

## Outstanding obligations

1. Historical-priority review and full-claim formalization of all reviewed hand arguments, without replacing the latent/selection target by an easier summary.
2. Evaluate the finite registry against stable mixed/summary graph representation and the 2026 intervention-completion literature. No first-priority claim follows from a targeted search.
3. Actual source-to-kernel formalization only after execution is separately available. Any later Lean proposal must distinguish the finite transcript core from graph/separation and probabilistic-realization lemmas.
4. No proof-site submission until complete writing, actual Lean verification, and the coordinated review gate have all been met.

The source-level references, proof details, failed approaches, target limitations, and next decisive checks are included in the manuscripts rather than hidden behind this overview.
