# Checkpoint 11:33: whole-word mass and root reader bounds

Reviewer: dot, independent G4 review lane. 12 October 2026, 11:35 UTC.

Source `0913f09daf1a691413c9599944a6cf85739e65a83eff19b085531e3f1a9ce6f2`; ledger `6f0ece43909af7382d56c49e11f87680d74839076eb4db7373d9b073e755fbdd`. All 468 provider hashes/imports match accepted1610; no new external provider is recorded. PMF.map_comp and explicit real n-offset corrections are present.

**Bounded mathematical/source verdict: PASS for the implemented additions; all UNCOMPILED.** No compiler, new build admission or external write occurred. No new missing mathematical hypothesis or definite API-name blocker was found in this pass; elaboration remains untested.

The generic diagonal bound keeps the self-transition at every discrete step, with the full PMF diagonal sum bounding that path from below. Poissonization is justified using a summable upper envelope from PMF mass<=1. The clade diagonal is exactly one minus active ordered-pair count divided by padded-choice count because a genuine merger decreases forest cardinality. The padded rate cancels and gives the required exp(-choose(active,2)*t) lower bound. Composition keeps the same forest at each clade, then multiplies by its existing completion event mass. No backwards transition or independent-summand query is assumed.

The root coefficient uses l equal to remaining prescribed graft count. Its successor identity and induction give kappa_l <= kappa_(l+s)*(l+s+1)^(2s), hence kappa_l <= kappa_m*(m+1)^(2s) when m-l<=s. This is the correct polynomial factor relative to the original full-copy coefficient. On a good reachable forest, the earlier proper-clade loss bound supplies s=n-2; on a forbidden forest the previously checked opacity/exclusion gives zero completion event mass.

The positive-word transformation filters exactly zero clade kernels by their identity theorem. A nonzero full-clade weight is impossible under the explicit full-weight-zero assumption. Empty normalized clades also have zero weight when the actual LaminarWeights/normalization hypothesis is supplied later, so no empty-clade K>=n premise is needed. The current generic word theorem correctly retains K>=n only for nonzero scheduled weights. Zero-weight resolutions and zero durations are thus handled without a positivity shortcut.

The whole-word good-mass induction proves each support invariant and each clade row estimate, composes nonnegative exponential factors, and retains absorbing bad states. The final reader bound is applied only on supported forests. These generic intermediate premises are discharged by the actual-word theorem where claimed; no master endpoint is replaced by a supplied row-bound field.

The source still lacks the final sandwich packaging in the quadratic/linear coordinates, concrete all-taxon-first growing copy allocations, asymptotic-ratio proof, finite row selection and target-first legal finite-menu/source conclusion. The current ordinary evaluator bounds are useful progress toward those endpoints, not proof of profile independence, executable algebraic acquisition or general G4 closure.
