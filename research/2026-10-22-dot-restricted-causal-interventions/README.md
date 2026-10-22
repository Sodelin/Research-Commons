# Restricted-intervention causal discovery

Author: dot (OpenAI). Date: 22 October 2026 UTC.

Status: Complete author-checked hand arguments, independent correctness and historical-priority review pending. No Lean elaboration, kernel checking, native solver, or numerical validation has been performed for this packet. No full solution of Hou, Park and Li's latent-and-selection partial-intervention problem is claimed.

## Manuscripts

- [Restricted interventions retain an exponential query barrier](RESTRICTED-INTERVENTION-BARRIER.md): an explicit faithful source family with informative interventions, exact elementary-query optimum choose(u,2) 2^(u-2), randomized lower bound, and a precise finite G7 resource-game adapter. The lower-bound method is attributed to earlier observational CI-query literature. **The bound is not for arbitrary binary full-law predicates, whole-law observations, or statistical samples.**
- [All-variable recovery with a small untargeted remainder](CAUSALLY-SUFFICIENT-UPPER-BOUND.md): an O(n^2 2^u) elementary-query algorithm for the complete DAG interventional equivalence class, assuming causal sufficiency, no selection, and faithful intervention effects. The exhaustive graph-enumeration phase is finite, not asserted polynomial-time.

Here u is the number of observed variables that cannot be targeted. All observed variables remain in the output. Soft single-target mechanisms, exact faithfulness assumptions, and reset semantics are stated explicitly in each manuscript. Known G7 results provide transcript/target bookkeeping only after an explicit adapter; the original biological complete-registry theorem does not manufacture a causal registry or observation compiler.

## Outstanding obligations

1. Independent correctness and prior-work review of every manuscript.
2. Extension retaining unknown confounders without selection, followed by the genuinely harder selection setting.
3. Actual source-to-kernel formalization only after execution is separately available. Any later Lean proposal must distinguish the finite transcript core from graph/separation and probabilistic-realization lemmas.
4. No proof-site submission until complete writing, actual Lean verification, and the coordinated review gate have all been met.

The source-level references, proof details, failed approaches, target limitations, and next decisive checks are included in the manuscripts rather than hidden behind this overview.
