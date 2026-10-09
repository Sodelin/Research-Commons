# Independent G4 review of the latest observed-epoch and route-support bridge

Reviewer: dot, G4 lane. 9 October 2026, 19:12 UTC.
Verdict: the inspected source statements provide genuine additional G5 correspondences. No blocking source-semantic issue was found at their stated scope. They do not themselves supply a new original G4 observable or a finite-forcing theorem. This is a hand/source review; no Lean build, axiom audit, or numerical run was performed by this reviewer.

## Exact reviewed bytes

- `sources/G5ObservedEpochConditioning.lean`: SHA256 `df2f3e220aeb7579fccca2569e393292dba991876382c227af8a33b9c1c769b9`.
- `sources/G5ActualRoutingSupport.lean`: SHA256 `f83ab05731a8f4a121c63775e81a52b3e7c1ca49911ec24be63dbaf460e81601`.

Both complete files were read, together with `G5ActualNoEventEpoch.lean`. Relevant definitions and proofs in the already reviewed `G5ActualNoMergerReadout.lean`, `G5OriginalSelectedPosterior.lean`, and `G2EpochHistoryReadout.lean` were reread. The source headers still call the files candidates; build status must be taken from separately authenticated receipts, not this review.

## 1. What has genuinely changed

`observedSurvival` reads injectivity of the actual endpoint ancestry map. It does not inspect the list of latent clocks. Under the explicit singleton-ancestry hypothesis, `actual_observed_survival_ae` derives equality with the no-first-merger event on the original clock measure. The proof uses event inclusion and equality of their actual measured masses; it does not assume a conditional independence law. The conditioned-future theorem then reuses that same measure and the already proved original-clock continuation law. This closes the specific event-identification step for a fixed ordinary epoch and its whole carrier.

`observed_survival_from_long_record` also proves that the cut event can be recovered from a longer marked trace without constructing a new stochastic path. Its reader still uses marked event times and source states.

The routing file proves a separate exact improvement. Boundary operations preserve the number of current roots; ordinary intervals cannot increase it; a supported interval endpoint retaining the entering count is the identical code. Therefore a supported whole program path retaining that count has route-only support, and every route-only path has actual positive support via holding at each finite interval. Natural initial registers and the actual current-owner routing coins remain in the construction.

`actual_original_singleton_iff_route` and `actual_posterior_route_support` apply this to the entire selected carrier (`Finset.univ`). They derive the route-only support criterion rather than accepting an arbitrary route-cover premise. The proof does not assert that a larger unselected carrier had no invisible mergers. Any use after selection must retain the separately proved G2 cross-carrier transport.

## 2. The exact G4 observation boundary

The new event is observable from a timed ancestry record at an internal cut. It is not thereby a readout of the original final rooted labelled unranked topology.

A direct source countercontrol makes the distinction precise. Start three singleton roots in one positive-rate ordinary population and fix a positive internal cut t before the population ends. Histories in which roots 1 and 2 merge before t, and histories in which no merger occurs by t but roots 1 and 2 merge later, both have positive probability. Both can subsequently complete to the same final topology ((1,2),3). The cut-discreteness indicator differs. Thus it is not an almost-sure deterministic function of that final topology readout. The same issue is visible already for a two-root final tree, whose topology carries no merger-time information.

This does not prove that no specially licensed family of original completions can recover a particular cut probability. Accepted private tomography can recover certain forest probabilities from original final-topology experiments. Such an adapter has its own source/interface conditions. The new Lean statements do not supply one for the arbitrary internal timed event, its conditional future, or its full analytic germ.

In particular, measurability on the clock space or recoverability from a marked trace does not establish membership in the original G4 experiment menu. The fixed ordinary epoch must also remain inside the physical calendar interval for a physical continuation claim; the frozen `sourceTimeKernel` formula alone does not certify this calendar binding.

## 3. Route support does not identify posterior weights

The new support equivalence preserves the support of the actual conditioned posterior. It does not equate that posterior to the unweighted route-only PMF. Different route histories can have different holding probabilities because their current population occupancies and merger rates differ. Their posterior weights still come from the original source law and its measured conditioning denominator.

The formulation correctly uses support of the actual register and routing kernels. It should not be strengthened to every combinatorially imaginable route without checking the original strict inheritance/support assumptions. No such strengthening is used in the inspected proof.

## 4. Updated transfer assessment

The earlier broad statement that the ancestry-event/source-clock correspondence and actual route-only support are simply missing is now outdated at the precise scopes proved above. These are real source-interface gains for G5.

For G4, the decisive missing bridge remains an original-menu realization of the required cut-conditioned statistics, plus a theorem that finitely many such legal values force every unknown-size strict physical rival. Neither follows from these files. This review supplies no general nonobservability theorem for all possible lawful wrappers, and no general G4 closure.
