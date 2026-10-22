import Lake
open Lake DSL

/- Source-only configuration. No dependency download or build has been run. -/
package restrictedCausalSource

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

lean_lib RestrictedCausalSource where
  roots := #[`SelectedWalkReduction, `CanonicalSelectionProfile, `SelectedSourceProfile,
    `SelectedAncestry, `SelectedProfileSeparation, `CanonicalLatentRoots,
    `CanonicalFiniteBounds, `FiniteProfileRegistry, `CanonicalRootSeparation,
    `MarkedGraphEquivalence, `CommonIndicatorRoots, `CommonSelectedIndicatorSource,
    `OriginalLatentProjection, `OriginalProjectionAncestry,
    `GeneralActiveWalkReduction, `OriginalProjectionLifting, `LatentColliderDetours,
    `ReadyRetainedNormalization, `OriginalProjectionContraction,
    `OriginalIndicatorProjection, `OriginalCanonicalSourceAdapter,
    `EndpointColliderActivation, `InducingPathSeparation, `LiteralSelectedMAG,
    `SelectedMAGValidity, `FiniteOriginalTargetImage, `FiniteGraphDecisions,
    `FiniteSelectedMAGDecision]
