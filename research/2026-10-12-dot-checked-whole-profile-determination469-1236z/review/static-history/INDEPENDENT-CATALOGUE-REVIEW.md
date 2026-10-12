# Bounded review of the laminar catalogue checkpoint

Reviewer: dot, independent G4 review lane. 12 October 2026, 10:59 UTC.

**Mathematical domain verdict: PASS. Lean status: UNCOMPILED, with one missing API and one occurrence-sensitive rewrite requiring correction before source acceptance.** This receipt applies only to checkpoint-1052z, not the owner's evolving successor.

Source SHA256: `7b9caaf4d981eb37ca4dd202f43328323ae6435c2eb09833e68389ee84e61c6a`.
Exact dependency ledger: `f6ce01ac7eb6a7ddceba253e54f3eddf7e5cb3509ae5094c4912b3046c11c35b`.
All 466 provider source hashes and literal import lists were reauthenticated against accepted connected1610. No compiler or external code was executed.

## Domain and proof

`CladeWeights X` takes values in NNReal. `LaminarWeights` additionally makes the empty and full clades zero and makes positive support laminar. These are sufficient conditions for the displayed covariance reconstruction. The covariance includes its diagonal, so singleton clades retain their information. For positive A and i in A, its cumulative ancestor height is a positive threshold whose row superlevel set is exactly A: inside points receive every ancestor contribution, while an outside point loses at least the positive weight of A. Conversely a nonempty positive threshold is the minimal positive common clade for a point of minimum covariance on that threshold.

These two directions identify positive support. A positive clade's ancestor height is attained by some pair in it, including diagonal pairs for singleton clades; comparing the two systems yields equal ancestor heights. Reverse inclusion induction subtracts already recovered strict-ancestor weights. This proves equality of weight functions, without pretending to recover arbitrary zero-weight binary resolutions.

For nontrivial X, every row has an outside point with zero covariance: take a maximal positive proper clade containing the row taxon, or use any other taxon if none exists. Consequently root exposure is the maximum directed exposure in the row. Equality of directed exposures therefore gives equality of the complete covariance matrix. Exponential injectivity gives the survival-coordinate version. The same covariance determines the quadratic form, and singleton/pair test vectors recover it from the quadratic form.

The empty/full exclusions are necessary. An empty-clade weight is invisible to both coordinates; a full-clade weight is invisible to all directed exposures. Their normalization is already appropriate for the completed evaluator. Zero pendant/internal coordinates cause no ambiguity for the normalized weight function. No source-domain weakening follows from allowing this conservative evaluator catalogue.

The finite catalogue theorem embeds the subtype of laminar weights with coordinates in supplied finite grids into a finite product of those grids. It proves semantic `Set.Finite`, not an executable enumeration, exact algebraic encoding, feasibility test or reconstruction routine. The actual-source inclusion reuses the accepted whole-pruning support and positive original edge exposures. The last source lemma merely regroups selected original edge exposures and reuses the checked cut/path telescope.

## Specific static corrections

1. `Finset.exists_notMem_of_ne_univ` used in `exists_zero_shared` is absent from the pinned Mathlib and Lean source. The argument is valid; derive an outside point using `Finset.eq_univ_iff_forall` and classical contradiction, or another verified equivalent API.
2. In the local `ht` proof inside `covariance_eq_positive_support`, backward rewriting the threshold theorem may replace A inside `ancestorExposure u A` before the intended outer right-hand A. Use an explicit intermediate equality between the two covariance thresholds at the unchanged scalar height, then the existing threshold theorem. This isolates the intended occurrences.

Other inspected APIs include finite minimum/maximum image, cardinality equality from subset, nonnegative finite-sum positivity, source pruning existence and actual pruned-clade support. No missing mathematical premise was identified. Remaining type/elaboration issues can only be settled by the separately admitted actual build; this review does not promise compilation.

## Independent bounded controls and remaining consumer

A separately authored exact-integer check examined all 189 laminar weight functions on three taxa with weights in {0,1,2}, and all 416 on four taxa with weights in {0,1}. It checked covariance/directed injectivity, every positive threshold reconstruction, ancestor-height attainment and zero-shared witnesses. These finite controls supplement the argument and do not prove its general Lean statement.

The checkpoint does not yet establish the uniform specified-comb history bound, positive integer separation of the finite quadratic catalogue, profile independence, full-rank row selection or the target-first legal finite-menu conclusion. Diagonal grid coordinates can be fixed to the known value 1; they should not create unnecessary physical queries. Catalogue completeness for every matching rival must precede rank-based finite row selection. Original n >= 4 and the admitted COMMON full rooted labelled observation/menu contract remain the intended master scope unless a stronger result is separately proved.

Classical hierarchy/covariance reconstruction and the Teicher–Chandra asymptotic mixture criterion remain prior mathematics. This is a source-composition/domain review, not a novelty claim or public build admission.
