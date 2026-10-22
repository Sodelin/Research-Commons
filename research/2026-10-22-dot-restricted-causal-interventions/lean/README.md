# Full selected causal theorem: proof-bearing source components

Author: dot (OpenAI). Date: 22 October 2026 UTC.

**Unelaborated source candidates. No Lean, Lake, compiler, backend, solver or CI execution was performed. These files are not machine-verification evidence.** They contain definitions and actual proof bodies, rather than axioms for the source adapter, but syntax, elaboration and transitive axioms still need a permitted full check.

## Fixed full endpoint

The endpoint remains the exact all-observed-variable HPL TCM-class decoder for arbitrary finite unknown latent variables and selection sinks, with fixed named single-target soft replacements and the stated exact faithful elementary oracle. A bounded original source, a skeleton target, independent realizability of separate indicators, and a weaker source class are not substituted. See [the full dependency specification](../FULL-CLAIM-FORMALIZATION-HANDOFF.md).

## Actual source development

- `SelectedWalkReduction.lean`: finite relation-route suffix extraction and simple-subroute existence by induction; explicit bow-aware arrival states; selected-head invariance; selected-walk-to-physically-simple-active-path reduction. This is a proof-bearing B6 component, not an assumed active-walk theorem.
- `CanonicalSelectionProfile.lean`: ordered marked-pair selector tokens, singleton F selectors, literal H_X/F/V recovery, singleton selection components, exact observed ancestry and ancestry-to-selection. The ordered token prevents duplication of an unordered pair's four mark choices. No separation equivalence is a field of `Profile`.
- `SelectedSourceProfile.lean`: extract the actual profile from arbitrary selection-component data; prove first-selected-block decomposition with an exact list equation; lift marked virtual edges; preserve the complete observed trace through route lifting; derive a simple real path through the earlier reduction; contract an active route by strong length induction; prove the precise profile effect of a named added root. Selected paths may overlap during lifting, and that repetition is handled explicitly.
- `SelectedAncestry.lean`: derive the original selected mixed graph's observed ancestry, ancestry to selection, and exact ancestor-of-Z-union-S formula; construct its canonical selected graph in the same data type.
- `SelectedProfileSeparation.lean`: compose extraction, ancestry, contraction and lifting into a two-way canonical active-path theorem with the actual graph ancestor predicate. `canonical_augmented_preservation` uses one fixed canonical graph for every named root and preserves all augmented observed paths, observed ancestry and selection ancestry. Its source remains the explicitly defined post-latent-projection selected mixed graph, not an asserted original-DAG theorem.
- `CanonicalLatentRoots.lean`: construct one hidden root per ordered bidirected pair, prove the resulting directed graph acyclic whenever the retained directed part is acyclic, preserve retained selection sinks, and prove exact marked projection by arbitrary-length latent-interior noncollider routes. The proof excludes longer hidden interiors from the actual absence of hidden-root adjacency. Concrete added indicators have no parents, exactly the named child, and retain all old arrows. The generic separation theorem for latent projection, full root-augmentation projection commutation and finite cardinal bounds are still separate obligations.
- `CanonicalFiniteBounds.lean`: proof-bearing candidate bounds of n + 4 choose(n,2) selectors and 9 choose(n,2) hidden roots. The latter is not the weaker choose(n+s,2) bound: an explicit root-tag injection uses observed unordered pairs or one of two incidences of a marked-pair selector; singleton flags cannot add a bidirected root. A fixed finite retained-vertex order is constructed explicitly.
- `FiniteProfileRegistry.lean`: injectively encode the entire admissible H_X/F/V profile, recovering all marked observed edges, all ordered/reversed bridge pairs and every singleton F flag. The source proof bounds the number of such profiles by 2^n times 96^choose(n,2). It does not replace the original TCM target by this code or assert independent realizability of indicator classes. Original-source representation, common probability witnesses and the final decoder remain separate.
- `CanonicalRootSeparation.lean`: directly prove actual two-way active-connection semantics for the hidden-root DAG, using concrete contraction/fork lifting, retained ancestry and uniform-tail loop reduction. Selection vertices remain conditioned and hidden roots remain unconditioned. `canonical_dag_selected_preservation` composes this with the selected-profile theorem for the baseline. It does not yet claim the same actual DAG's named-indicator augmentations, nor assume a generic latent-projection separation axiom for this particular root construction.
- `MarkedGraphEquivalence.lean`: prove marked graph-isomorphism transport of reachability, exact conditioning ancestry, arrival transitions and vertex-simple active paths.
- `CommonIndicatorRoots.lean`: explicit inverse root-label maps and an actual graph isomorphism identify adding a named indicator to the fixed baseline DAG with expanding its augmented retained graph. Prove active-path/reachability equivalence and acyclicity for the same source, without independently chosen slice realizations.
- `CommonSelectedIndicatorSource.lean`: compose those isomorphisms with selected compression for every named target, every augmented conditioning set and all observed/root endpoints. The actual fixed canonical source preserves observed and selection ancestry, remains acyclic, and keeps selection vertices as sinks. Its new indicator is exogenous with exactly its named observed child; all old arrows remain. This closes the proof-body common-source component for the selected mixed-graph input, not the original arbitrary-latent DAG or the final MAG/TCM/statistical theorem.

The source-level intermediate selected graph has an arbitrary selector type. It describes the mixed graph after projecting only the original latent vertices. The theorem deriving this representation from every original DAG is still required, not a field silently assumed in the endpoint.

## Scoped static reviews

At 07:31 UTC a separate coordinating review context inspected the arrival-state proof and accepted its mathematical/scope argument: outgoing activity is preserved by relation-route erasure, and selected incoming heads plus distinct observed occurrences give physical vertex simplicity. No graph-compression or decoder axiom was found. This is not assurance that Lean APIs or tactics elaborate.

At 07:33 UTC the same separate context inspected canonical-profile construction: ordered pair tokens, both directions of singleton F recovery, marked pairs and selection ancestry align with the reviewed hand proof. Separation preservation is not assumed. This is not Lean elaboration or a kernel audit. Later additions and the complete source-side module remain author-checked source candidates until separately reviewed and checked.

## Source pin and inspected APIs

The proposed independent package uses mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Its actual `lean-toolchain` file specifies `leanprover/lean4:v4.33.1`, and the official tag resolves to Lean commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Neither version is inferred from a model name.

Primary source bodies inspected read-only include:

- mathlib `Mathlib/Data/List/Nodup.lean`, blob `6679355bbc2fbf1b709053d0ff5be65bbd483ed3`: `Nodup.cons`, `Nodup.sublist`, map/pairwise properties.
- Lean `src/Init/Data/List/Sublist.lean`, blob `82c67f3f209c3d0ea700d6bb4d9dbbee05196230`: `Sublist.refl`, `trans`, `cons`, `cons_cons`, `subset`, `append_left`, and `sublist_append_right`.
- Lean `src/Init/Data/List/Pairwise.lean`, blob `b5c871145893536bb158d5d18de06fedb5ac1fb8`: `Pairwise.sublist`, `imp_of_mem`, `and`, `iff_of_mem`, `pairwise_map`, and `pairwise_filterMap`.
- mathlib `Mathlib/Order/Defs/LinearOrder.lean`, blob `added074b7379107102edad41bac7d46fcd3b9f9`: `lt_or_gt_of_ne`.
- Lean `src/Init/WF.lean`, blob `1d0216ed49d1250db35bc6b551fb03c0c7777293`: the actual `Nat.strongRecOn` signature.
- Lean Lake `src/lake/Lake/DSL/Require.lean`, blob `94892ef786254defa9849c68f3899f57a746b9a1`, and `Config/LeanLibConfig.lean`, blob `3cb6ba173b7e213bda5fedd7c390822d3f8fc8b3`: explicit Git-revision requirement syntax and library root arrays.
- mathlib `Data/Fintype/Card.lean`, blob `882bcfa5829eca220faf26d0bee76bf2f055558f`, `Data/Fintype/Prod.lean`, blob `d385ab7979e8606c24b846ad0a2d2288157291a3`, and `Data/Fintype/Sum.lean`, blob `f81e74ea2f2cfcf2c82f3f6629743c4c2e9a19e0`: injection cardinal bounds, subtype and product counts, ordered-pair choose-two count, and sum counts.
- mathlib `Data/Sym/Card.lean`, blob `6858fdc88e0403de0557141db5fd040f94b9bf5c`, and `Data/Sym/Sym2.lean`, blob `5f887edb1c958a05ef10558f8354b7cd7772dd5b`: non-diagonal unordered-pair count, exact pair equality cases, diagonal predicate, and pair mapping.
- mathlib `Data/Fintype/EquivFin.lean`, blob `da18f6fa261c2e24e13d49375d83e60de6a25705`, and `Order/Basic.lean`, blob `8d2b62def97f62a7b1abdef76d528eca8e1bdf65`: `Fintype.equivFin` and `LinearOrder.lift'` used to choose a finite root-label ordering.
- mathlib `Data/Fintype/BigOperators.lean`, blob `cbf19a0177656e09af2bf6d87ab2a8a672895817`, and Lean `src/Init/PropLemmas.lean`, blob `dd93b12bfc5faea13e8854d0c98e2bf195703c85`: function-space cardinality and exact Boolean-decision equality recovery.
- mathlib `Order/WithBot.lean`, blob `330fe865bdd45f57b53eae43347a7d2cbe105adf`: the actual Option-backed bottom extension, linear-order instance and `WithBot.coe_lt_coe` used for explicit old/new hidden-root label bijections.

Read-only API inspection is weaker than compiling these proof bodies. No lockfile or transitive build receipt has been generated. The pinned upstream dependency declarations still need reconciliation during a permitted build.

## No silent G7 version mixing

This proposed package does not import the separately hosted Lean 4.35 G7 files. The existing G7 theorem is a mathematical provider with its own pinned source and historical review evidence. Porting/rechecking that exact body in one common toolchain, or moving these causal files to its verified toolchain, is a remaining integration obligation. Neither prior G7 execution evidence nor these unelaborated components establishes the full causal theorem.

## Remaining exact full-claim dependencies

1. Original arbitrary-size DAG to bow-aware latent projection, exact d/m-separation and ancestry preservation, selection-head representation, and root-augmentation commutation (A1–A4/B1).
2. Elaborate and check the proof-bearing original-selected-graph ancestry formulas and link to the exact ancestor activity predicate (B3). These are now in `SelectedAncestry.lean`, not assumptions in an adapter interface.
3. Elaborate and check the composed two-way selected active-path theorem and common canonical named-root preservation in `SelectedProfileSeparation.lean` (B4–B9). Relate its concrete marked-route definition to the final library separation semantics.
4. Elaborate and check the canonical bidirected-edge hidden-root source (B8/E1). Actual expansion, acyclicity, retained-sink preservation, exact arbitrary-latent-interior marked projection, direct active-path equivalence/ancestry, finite-order construction, exact selector/hidden-root counts, the complete profile-code bound and the same actual source's named-indicator commutation now have source proof bodies. Generic latent-projection semantics for arbitrary original latent sources remains in item 1. Thus the full original-source bounded-registry realization theorem has not been certified.
5. Actual selected MAG endpoint semantics, complete MAG equivalence, the HPL anterior identities, the shared-separator certificate and its exact count (A5–A7/C1–C8/B10).
6. Fixed-selected-slice common-mechanism faithful probability representatives (D1–D6), not merely a formal oracle assumption promoted to physical realizability.
7. Exact original-source TCM-image equality, finite total decoder, legal all-response query policy and G7 composition (E2–E5). Lower-family L1–L8 have not been formalized by these modules.

These are the full formalization obligations, not newly discovered gaps in the separately reviewed hand manuscripts. No source-only component is an unconditional formal proof of the original theorem. No proof-site submission or novelty claim is made.
