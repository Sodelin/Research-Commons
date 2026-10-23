/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Instantiate the EIGHT concrete physical guard entry predicates from the
ONE inventory invariant derived by the original all-word prefix.
-/
import PolytomyRestrictedVerifierGuardBoundary

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem restricted_unique_target_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) : UniqueEntry restrictedUniqueTargetPorts m A L s := by
  have hz (j : InclusionPort) : s.stk (.inr (.uniqueTarget j)) = [] := hs.fresh _ rfl
  refine ⟨⟨hs.target_length, hs.target_mask, hs.rows, hs.types, ?_⟩, hz _, hz _, ?_⟩
  all_goals
    simp [rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
      inclusionMatchPortMap, restrictedUniqueTargetPorts, restrictedUniqueTargetMap, hz]

theorem restricted_unique_cert_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) : UniqueEntry restrictedUniqueCertPorts m A L s := by
  have hz (j : InclusionPort) : s.stk (.inr (.uniqueCert j)) = [] := hs.fresh _ rfl
  refine ⟨⟨hs.cert_length, hs.cert_mask, hs.rows, hs.types, ?_⟩, hz _, hz _, ?_⟩
  all_goals
    simp [rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
      inclusionMatchPortMap, restrictedUniqueCertPorts, restrictedUniqueCertMap, hz]

theorem restricted_coverage_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) : UniqueEntry restrictedCoveragePorts m A L s := by
  have hz (j : InclusionPort) : s.stk (.inr (.coverage j)) = [] := hs.fresh _ rfl
  refine ⟨⟨hs.target_length, hs.target_mask, hs.rows, hs.types, ?_⟩, hz _, hz _, ?_⟩
  all_goals
    simp [rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
      inclusionMatchPortMap, restrictedCoveragePorts, restrictedCoverageMap, hz]

theorem restricted_set_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) : CellSetEntry restrictedSetPorts m A L s := by
  have hz (j : InclusionPort) : s.stk (.inr (.sets j)) = [] := hs.fresh _ rfl
  refine ⟨hs.target_length, hs.target_mask, hs.cert_length, hs.cert_mask, hs.rows, hs.types, ?_⟩
  simp [rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
    inclusionMatchPortMap, restrictedSetPorts, restrictedSetMap, hz]

theorem restricted_marker_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) :
    RowMarkersAllEntry restrictedMarkerPorts restrictedTargetWord (.inr .markerCounter) m A L s := by
  have hz (j : RowMarkerPort) : s.stk (.inr (.marker j)) = [] := hs.fresh _ rfl
  have hword : s.stk (restrictedMarkerPorts .word) = [] := hz _
  refine ⟨⟨⟨?_, ?_⟩, ⟨⟨?_, ?_, hs.rows, hs.types, ?_⟩, ?_⟩⟩,
    hs.target_length, hword, hs.fresh _ rfl⟩
  · simp [rowMarkerScopePorts, rowMarkerScopeMap, restrictedMarkerPorts, restrictedMarkerMap, hz]
  · intro j hj
    cases j <;> simp_all [rowMarkerScopePorts, rowMarkerScopeMap, restrictedMarkerPorts,
      restrictedMarkerMap, hz]
  · simp [matchRangePorts, rowMarkerQueryPorts, rowMarkerQueryMap, restrictedMarkerPorts,
      restrictedMarkerMap, hz]
  · simp [matchRangePorts, rowMarkerQueryPorts, rowMarkerQueryMap, restrictedMarkerPorts,
      restrictedMarkerMap, hz]
  · simp [rangeAllWork, matchRangePorts, rowMarkerQueryPorts, rowMarkerQueryMap,
      restrictedMarkerPorts, restrictedMarkerMap, hz]
  · simp [rowMarkerQueryPorts, rowMarkerQueryMap, restrictedMarkerPorts, restrictedMarkerMap, hz]

theorem restricted_mixed_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) : MixedAllEntry restrictedMixedPorts m A L s := by
  have hz (j : MixedPort) : s.stk (.inr (.mixed j)) = [] := hs.fresh _ rfl
  refine ⟨⟨hs.target_length, hs.target_mask, hs.rows, hs.types, ?_⟩, ?_⟩
  · simp [rangeAllWork, mixedOuterPorts, restrictedMixedPorts, restrictedMixedMap, hz]
  · refine ⟨⟨⟨?_, ?_⟩, ⟨⟨?_, ?_, hs.rows, hs.types, ?_⟩, ?_, ?_, ?_⟩⟩, hz _⟩
    · simp [scopedTypeScopePorts, scopedTypeScopeMap, mixedNodePorts, mixedNodeMap,
        restrictedMixedPorts, restrictedMixedMap, hz]
    · intro j hj
      cases j <;> simp_all [scopedTypeScopePorts, scopedTypeScopeMap, mixedNodePorts, mixedNodeMap,
        restrictedMixedPorts, restrictedMixedMap, hz]
    all_goals
      simp [scopedTypeCountPorts, scopedTypeCountMap, mixedNodePorts, mixedNodeMap,
        rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
        inclusionMatchPortMap, restrictedMixedPorts, restrictedMixedMap, hz]

theorem restricted_score_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) : ScoreAllEntry restrictedScorePorts m A L s := by
  have hz (j : ScorePort) : s.stk (.inr (.score j)) = [] := hs.fresh _ rfl
  refine ⟨⟨hs.cert_length, hs.cert_mask, hs.rows, hs.types, ?_⟩, ?_⟩
  · simp [rangeAllWork, scoreOuterPorts, restrictedScorePorts, restrictedScoreMap, hz]
  · refine ⟨⟨⟨?_, ?_⟩, ⟨⟨?_, ?_, hs.rows, hs.types, ?_⟩, ?_, ?_, ?_⟩⟩, hz _, hz _, hz _⟩
    · simp [scopedTypeScopePorts, scopedTypeScopeMap, scoreNodePorts, scoreNodeMap,
        restrictedScorePorts, restrictedScoreMap, hz]
    · intro j hj
      cases j <;> simp_all [scopedTypeScopePorts, scopedTypeScopeMap, scoreNodePorts, scoreNodeMap,
        restrictedScorePorts, restrictedScoreMap, hz]
    all_goals
      simp [scopedTypeCountPorts, scopedTypeCountMap, scoreNodePorts, scoreNodeMap,
        rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
        inclusionMatchPortMap, restrictedScorePorts, restrictedScoreMap, hz]

theorem restricted_clade_entry (m A B L : ℕ) (s : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) :
    AllCladesEntry restrictedCladePorts m A L (s.stk restrictedCertWord) (s.stk restrictedCertMask) s := by
  have hz (j : CladePort) : s.stk (.inr (.clades j)) = [] := hs.fresh _ rfl
  refine ⟨⟨hs.target_length, hs.target_mask, hs.rows, hs.types, ?_⟩,
    rfl, rfl, hs.cert_length, hs.cert_mask, ?_, ?_, ?_, ?_⟩
  · simp [rangeAllWork, cladeOuterPorts, restrictedCladePorts, restrictedCladeMap, hz]
  · intro j hj
    cases j <;> simp_all [cladeLeftScopePorts, cladeLeftScopePortMap,
      restrictedCladePorts, restrictedCladeMap, hz]
  · intro j hj
    cases j <;> simp_all [cladeRightScopePorts, cladeRightScopePortMap,
      restrictedCladePorts, restrictedCladeMap, hz]
  · simp [rangeAllWork, cladeInnerPorts, cladeInnerPortMap, restrictedCladePorts,
      restrictedCladeMap, hz]
  · simp [rangeAllWork, inclusionOuterPorts, matchRangePorts, inclusionInnerPorts,
      inclusionMatchPortMap, cladeSetPorts, cladeSetPortMap, restrictedCladePorts,
      restrictedCladeMap, hz]

/- These are proof terms for the actual fixed-port instances, not eight
new caller premises. The next theorem must use all eight Executes
contracts in the one success-gated sequence, preserve this same invariant
and both real parser observations, and identify the combined original
semantic result. All-word rejected-prefix mass and final packaging remain.
-/

end PolytomyReductionModel.WholeVerifierController

