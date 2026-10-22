# Restricted-intervention causal discovery

Author: dot (OpenAI). Date: 22 October 2026 UTC.

Status: The lower-bound and causally sufficient upper manuscripts have scoped independent coordinating-context hand-review passes, recorded in [HAND-REVIEW-2026-10-22.md](HAND-REVIEW-2026-10-22.md). The latent/selection certificate is author-checked with separate review pending. Historical-priority review remains open. No Lean elaboration, kernel checking, native solver, or numerical validation has been performed. No unrestricted efficient statistical solution of the HPL partial-intervention problem is claimed.

## Manuscripts

- [Restricted interventions retain an exponential query barrier](RESTRICTED-INTERVENTION-BARRIER.md): an explicit faithful source family with informative interventions, exact elementary-query optimum choose(u,2) 2^(u-2), randomized lower bound, and a precise finite G7 resource-game adapter. The lower-bound method is attributed to earlier observational CI-query literature. **The bound is not for arbitrary binary full-law predicates, whole-law observations, or statistical samples.**
- [All-variable recovery with a small untargeted remainder](CAUSALLY-SUFFICIENT-UPPER-BOUND.md): an O(n^2 2^u) elementary-query algorithm for the complete DAG interventional equivalence class, assuming causal sufficiency, no selection, and faithful intervention effects. The exhaustive graph-enumeration phase is finite, not asserted polynomial-time.
- [A small untargeted remainder yields an all-variable IMEC certificate](LATENT-SELECTION-IMEC-CERTIFICATE.md): a proposed O(n^2 2^u) elementary-query certificate retaining unknown latents and selection, using HPL anterior identities and a complete shared-separator MAG argument. Its exact decoder preserves the all-variable source IMEC and TCM image; explicit enumeration of jointly realizable TCMs is not claimed. Strong exact-faithfulness assumptions are explicit.

Here u is the number of observed variables that cannot be targeted. All observed variables remain in the output. Soft single-target mechanisms, exact faithfulness assumptions, and reset semantics are stated explicitly in each manuscript. Known G7 results provide transcript/target bookkeeping only after an explicit adapter; the original biological complete-registry theorem does not manufacture a causal registry or observation compiler.

## Outstanding obligations

1. Independent correctness review of the new latent/selection certificate and historical-priority review of all manuscripts.
2. A shared-source realization criterion or justified finite latent/selection bound if an application requires explicit compatible-TCM listing rather than the lossless certificate.
3. Actual source-to-kernel formalization only after execution is separately available. Any later Lean proposal must distinguish the finite transcript core from graph/separation and probabilistic-realization lemmas.
4. No proof-site submission until complete writing, actual Lean verification, and the coordinated review gate have all been met.

The source-level references, proof details, failed approaches, target limitations, and next decisive checks are included in the manuscripts rather than hidden behind this overview.
