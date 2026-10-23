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
    `FiniteSelectedMAGDecision, `ExplicitProfileDecoding, `ComputableCanonicalLabels,
    `FiniteTranscriptDecoder, `MarginalIndicatorAncestry, `RefinedObservedSeparator,
    `PartialObservedQueryFamily, `RefinedIndicatorSeparator, `PartialIndicatorQueryFamily,
    `CommonObservedMAG, `DiscriminatingSeparatorStatus, `InducingEndpointMarks,
    `MarkedActiveWalks, `ConditionedEdgeWalks, `MAGPathLifting,
    `MAGMaximality, `ObservedMAGAncestry, `ClosedColliderWalks,
    `WeakInducingEdges, `OriginalWeakConnection, `WeakRouteNormalization,
    `OriginalMAGConnection, `CommonDiscriminatingParents,
    `VertexActivePaths, `MinimalActivePaths, `AncestralShortcutGeometry,
    `MinimalPathChord, `DiscriminatingSectionExtraction,
    `ActivePathReversal, `VertexDiscriminatingSections, `IntervalDependency,
    `LiteralMAGInducingChains, `DiscriminatingIntervalGeometry,
    `IndexedDiscriminatingSections, `ReversedPositionTrace,
    `MinimalPathOrderDependencies, `FiniteDependencyInduction,
    `DiscriminatingStatusTransport, `IndexedPrefixColliders,
    `ShortestPathStatusInvariance, `MinimumDirectedPathTransfer,
    `ClosestFirstArrowGeometry, `ClosestFirstArrowBoundary,
    `ClosestFirstArrowFlank, `ClosestFirstArrowSplice,
    `ClosestFirstArrowPotential, `ClosestFirstArrowIncidence,
    `ClosestFirstArrowContradiction, `ClosestFirstArrowArms,
    `ClosestFirstArrow, `ClosestPathAncestry, `SharedSeparatorMEC,
    `RestrictedFamilyCertificate, `RestrictedQueryActions,
    `OrderedFamilyAgreement, `RestrictedHistoryCompleteness,
    `TwoPhaseRestrictedHistory, `RestrictedBudgetAndHonesty,
    `EffectiveQueryEnumeration, `G7ResourceGamePort, `FiniteQueryPlan,
    `FullClassQueryGame, `RestrictedInteractivePlan, `RestrictedQueryBudgetBound,
    `RationalPolynomialAvoidance, `BinaryCPTPolynomials,
    `ColliderMinimalActivePaths, `ActivationBranchDistances, `SafeDirectedBranches,
    `ColliderSpliceCosts, `DirectedBranchSplices, `ColliderMinimumReversal,
    `ActivationMainPathExclusion, `ActivationBranchPairSplice, `ActivationBranchPairExclusion,
    `BinaryBoundaryCircuit, `BinaryCircuitMinor,
    `BinaryTrekDecomposition, `FiniteDAGRank, `BinaryPathConstraintPropagation,
    `BinaryTraceIncidence, `BinaryActivationFamily, `BinaryWitnessCircuit,
    `BinaryActivePathMinor, `BinaryTrekSourceAlignment,
    `BinarySelectionSinkComplement, `BinarySharedMechanismRegistry,
    `BinaryCommonPositiveMinorFamily, `BinaryIndicatorLawFactorization,
    `BinaryConditionalIndependenceAlgebra, `BinarySelectedInvarianceIdentity,
    `BinaryAncestralMoralConnection, `BinaryAncestralElimination,
    `BinaryAssignmentElimination, `BinaryAncestralMarginal,
    `BinaryFactorElimination, `BinaryMoralFactorization, `BinaryNestedElimination,
    `BinaryGlobalMarkov, `BinaryCommonFaithfulSource, `BinarySelectedProbabilityLaw,
    `BinaryFaithfulInvariance, `BinarySelectionQuerySemantics,
    `BinaryOriginalSourceLabels, `BinaryPhysicalOracle, `BinaryPhysicalGame]
