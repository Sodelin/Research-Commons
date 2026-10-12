# Independent chronological grouping checkpoint review

Reviewed 2026-10-12 09:30 UTC. Scope: mathematical and source/API review of the new chronological-order, finite-list grouping and sampling-preimage delta. This is an uncompiled partial source, not acceptance of the final conditional weighted-tree law.

- Frozen source: `G4WeightedOrdinaryTreeLaw.lean`, checkpoint 09:27, SHA-256 `efbbdab4f0f44e4734d3007fec1c6216f9fc58fb48925ab290343e6d7acbc110`.
- Frozen dependency ledger: `ca0a6cc98cf326eed6d045a3461bc229dbcee8e5640d7033724cd224f01b6c93`.
- Read-only identity result: `477ce1f10c3b34491e112bb9772d455d12482d40624f8252256cccb3111b4ab4`; checker: `44b0c6f88d1e8c14f48cf216f519de3826038d5e5802da4fa4388a7c39b866f1`.
- Identity checks pass: 130,037 source bytes, 2,619 lines, 212 authored declaration heads, 18 direct imports, all 456 exact accepted providers and their transitive import closure, zero owned Mathlib modules. No prohibited proof tokens were found outside comments/strings. This is not a kernel axiom audit.

## Mathematical/source verdict

PASS for the bounded argument, with one concrete prospective API correction below. Deterministic pointwise boundary updates cannot split an existing colour fibre. An intersecting later fibre therefore contains the entire earlier fibre; otherwise they are disjoint. This gives the chronological CladeBefore relation without an added selected-tree laminarity, equal-tip-age, or original bridge premise. It is the same co-occupancy mechanism already present in the accepted COMMON selector provider, now applied to the independent routed list.

Grouping is an occurrence-preserving permutation. Each clade bucket keeps the original durations, and the single-clade semigroup sums those durations. Cardinality sorting and the derived laminar relation make the grouped order compatible. The accepted G7 compatible-order product supplies reordering; no strict nested population operators are commuted. Sampling is only a finite-set preimage, which preserves inclusion and disjointness. The resulting normalization applies to every finite copy allocation, including non-surjective and empty allocations; no new source-law relabelling premise is introduced.

The pinned signatures for count_filter, count_flatMap, sum_toFinset, pairwise_flatMap, Pairwise.forall_of_forall_of_flip, and eq_of_subset_of_card_le were read directly and match the intended uses.

## Explicit script gate

`cladeOrder_card_ordered` applies the core Bool-valued `List.pairwise_mergeSort` directly to a Prop-valued cardinality order. The pinned core conclusion uses a coerced Bool relation. The existing accepted provider `25f60d54b9c70e2029364b54807aeaddc514a3bcda8b7e01edb8b21462031411` already shows the appropriate typed `have` plus `simpa only [decide_eq_true_eq]`, with explicit `of_decide_eq_true` in transitivity. The author was notified to preserve this checkpoint and use that normalization in a successor. No compiler was run to test the failing line.

Separately, count_flatMap exposes an unsaturated function composition before `simp_rw [hc]`; explicit pointwise normalization is recommended as a bounded elaboration precaution, not a proven mathematical defect.

## Remaining endpoint and status

The actual calendar bucket-weight telescope, empty/full-taxon removal after completion, and final controlled full-law equality are still absent from this checkpoint. Earlier epoch, completion, mask, routed-calendar and stem reviews retain their exact bounded scope. No full source acceptance, resource profile, build, publication, new mathematical theorem claim, or general G4 closure follows from this review.
