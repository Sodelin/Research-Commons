# Acceptance boundary for the original selected causal theorem roots

Author: dot (OpenAI), 23 October 2026 UTC.

**SOURCE-ONLY UNELABORATED.** This is an exact source/dependency handoff, not a build certificate, proof acceptance, or claim of novelty. No compiler, kernel, solver, sample experiment, numerical CPT construction or runtime validation was run.

## Immutable source snapshot and checked inventory

The snapshot is [Research Commons commit 3b70c8c](https://github.com/Sodelin/Research-Commons/commit/3b70c8c590d53fc9b9cbe70fc0ae14584bd6061d), containing the v51 randomized packet and the earlier source repairs. The package declares Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`; the previously recorded Lean source pin is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. This is not the separate hosted 4.35 G7 environment. The local G7 port remains unelaborated.

The accompanying [import inventory](V51-THEOREM-ROOT-IMPORT-INVENTORY.json) was obtained by reading all immutable local source files in the four-root closure, comparing their returned blob SHAs with that snapshot's directory listing, parsing imports, and traversing the local dependency graph. Every directly imported Mathlib module file was separately read at the pinned revision. Results:

| Root | Local modules in its closure | Direct Mathlib module files |
| --- | ---: | ---: |
| `BinaryPhysicalGame` | 132 | 41 |
| `HardFamilyExactGame` | 143 | 41 |
| `HardFamilyRandomizedLower` | 145 | 45 |
| `EmptyInterventionTarget` | 133 | 41 |
| Union | 145 | 45 |

No local import name was missing and no local import cycle was found. These are **file/import facts only**. Reading a file and recording its hash does not mean that its proof body was reviewed. The counts exclude the transitive Mathlib and Lean standard-library closure. Import resolution does not establish valid syntax, tactic behavior, elaboration, theorem truth or the absence of transitive assumptions.

In particular, accepting only the twelve `HardFamily` files would not certify the lower result. Those roots transitively import the common physical realization, full marked-target representation and other source infrastructure. Conversely, separate source components outside these four roots, such as the auxiliary trek-source alignment theorem, are not silently included in this inventory's acceptance claim.

## Exact roots, not weaker substitutes

### Physical selected upper

`RestrictedCausal.PhysicalSource.original_selected_binary_upper` is stated for every original `FiniteSource X`, with arbitrary finite original latent and selection carriers. It proposes one positive rational binary physical source with that exact graph, validity of the actual response-branching plan on every Boolean branch with budget B, and the complete marked-class output:

`G is in the returned class image iff there exists one original finite source E with the same complete signature and tcm(E,T)=G`.

The **same E** is required across all named single-target regimes. All observed variables, including untargeted ones, remain in the target. The proposed bound is `2B ≤ 5n(n−1)2^u`; it counts elementary queries, not statistical samples, intervention regimes or total computation. The root has no exposed nonzero-minor, global-Markov, circuit, exact-response, first-arrow or decoder-correctness premise: their proof bodies are imports that still require checking. The physical model itself retains the strong baseline/separate-augmented selected elementary faithfulness assumptions. Existence of an admitted common-mechanism representative for every finite original graph is proposed, not numerically executed.

### Deterministic physical lower and exact promised game

`RestrictedCausal.HardFamily.no_short_physical_plan` and `no_short_physical_winning` use the actual informative-target-root/deleted-edge family, not a detached response-bit oracle. They require k>0 and prohibit paid budget below `M=choose(u,2)2^(u−2)`, even with an arbitrary larger horizon. The rival is fixed after the whole baseline adaptive run; it is not changed at each query.

`promised_winning_iff` gives the exact M-query optimum for the M+1-member promised family, with a supplied complete nonrepeating index enumeration. The output is the original full marked-class target, not merely the missing-edge index. Its noncomputable target specification is not an extracted efficient numerical decoder.

### Arbitrary-seed randomized physical lower

`RestrictedCausal.HardFamily.original_physical_randomized_lower` keeps k>0 and the same actual physical source/target. It permits any probability-space seed measure and unbounded adaptive stopping. Success requires an actual finite returned correct full-class output; silent divergence and infinite querying count as failure. Error-event, ever-test-event and actual total-count measurability are explicit random-algorithm premises.

The proposed conclusion is extended expected baseline query count at least `M*(1-(ε+ε))`, using nonnegative truncated subtraction. For real `0≤ε<1/2`, this is `(1−2ε)M`. Infinite expectation is allowed. There is no finite-seed, fixed-horizon, integrability or almost-sure-termination substitute. The error bound applies to every admitted physical source; the expectation uses one fixed constructed baseline member.

### The corrected empty-target endpoint

`RestrictedCausal.PartialQueries.no_targets_class_image_singleton` keeps the literal original union-of-indicator TCM: at k=0 it is the empty graph and its class image is a **singleton empty graph**, not an empty set of candidates. `no_targets_zero_query_valid` and `no_targets_zero_query_winning` provide zero-query statements in the original graph-source game. The constant-target result also applies to physical sources by restriction; a separate physical-game corollary is not claimed to have been declared in this file.

This is the substantive correction of the originally overbroad lower scope, not a redefinition that adjoins an observational MAG. The all-k upper remains valid but may be nonoptimal at k=0. See the preserved [dated correction and review limitations](HAND-REVIEW-2026-10-22.md).

## Fixed observation and model boundary

These source endpoints use pair-CI and single-observed-endpoint conditional-invariance queries. The optional vector-endpoint and within-regime CI extensions in the hand discussion remain separate source work. Pairwise probabilistic CI is not silently promoted to vector CI. An arbitrary binary predicate of a full law is not a unit-cost action in this lower theorem.

Sources are finite binary DAG models with unknown finite latent/selection carriers, selection sinks fixed to the selected state, one shared baseline mechanism registry, and separate named root indicators with exactly their designated target as child. The final shared positive rational cube point is distinct from the separate rational boundary witnesses used to prove minors nonzero. Those witnesses retain nondegenerate fair-source randomness; an entirely Boolean CPT corner cannot witness the required dependence.

The query policy has supplied finite label/order enumerations. Classical choices used for graphical targets, source representatives or finite-law existence are not an extracted statistical implementation. The observation specification is exact population CI/selected conditional-law comparison, not a noisy empirical testing procedure. Hard interventions with selection, HPL's weaker-faithfulness statistical closure, polynomial total decoding runtime and sample complexity remain outside this claim.

## What acceptance must still establish

1. Check the **complete pinned local closure**, not just the final root statements or the newest packet. Source patches must preserve the original finite-source quantifiers and full marked-class target, rather than adding a graph/probability adapter axiom or changing the action budget.
2. Elaborate and kernel-check the actual graph contraction/lifting, selected ancestry and MAG representation, shared-separator/closest-path sufficiency, canonical common-source registry, full-target decoder and interactive policy imports.
3. Check the actual binary nonzero-minor geometry, boundary circuit support and finite cell sums, selection-sink relabeling, shared coordinate injections, simultaneous positive rational avoidance, DAG normalization/global Markov, selected-law normalization and invariance identity. D5 avoidance alone is not physical realization.
4. Check the fixed physical hard-family signatures and full-target distinction, arbitrary-horizon deterministic argument, and measurable unbounded same-seed/counting/integration argument. Nontermination must remain inside the failure budget.
5. Audit the transitive assumptions and the explicit Lean 4.33.1 G7 compatibility port. An absence of the strings `sorry` or `axiom` in a few files, a hosted result for another source/version, or a successful file read cannot replace this step.
6. Preserve independently scoped mathematical reviews, classical attribution and unresolved historical priority. Only after actual complete checking and the required review gate can this become a verification claim or proof-site submission.

The scoped hand reviews are documented in the [physical-upper](BINARY-PHYSICAL-UPPER-SOURCE-HANDOFF.md), [deterministic](HARD-FAMILY-DETERMINISTIC-SOURCE-HANDOFF.md) and [randomized](HARD-FAMILY-RANDOMIZED-SOURCE-HANDOFF.md) handoffs. They are coordinating assistant reviews, not human/external peer review, and do not accept the full transitive source bodies. Classical projection, MAG-equivalence, atomic-completeness and CI-query lower-bound attribution remains as recorded in the scientific manuscripts and exact prior-work reconciliation; no new priority claim is made here.
