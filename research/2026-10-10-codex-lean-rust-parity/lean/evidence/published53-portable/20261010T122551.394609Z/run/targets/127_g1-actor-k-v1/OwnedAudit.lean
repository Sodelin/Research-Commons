import G1CanonicalKActorCompletedHistory
import G1CanonicalKActorExteriorHistory
import G1CanonicalOriginalKOnlyActorRow
import G1KOnlyActorSameCompletedFuture
import G1KOnlyActorWholeExteriorHistory
import G1KOnlyCurrentRootExitView
import G1OriginalKActorWholeViewAssembly
import G1OriginalOpaqueKActorOutput
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["SourceNetwork", "GraphLeaves", "GraphCuts", "GraphBlobs", "GraphBridgeSplits", "GraphSwitching", "GraphBlobOrientation", "GraphBlobLeaves", "GraphSwitchingDegree", "GraphQuartetExistence", "GraphTreePorts", "GraphPorts", "GraphBlobPorts", "GraphGalls", "G1CutChildPorts", "G1BlobDegreeBalance", "G2LiveLineageRouting", "SourceLabelledForest", "SourceForestKingmanProjection", "SourceForestKingmanPopulationProjection", "UnifiedLean.Source.SourceForestSilentPruning", "UnifiedLean.Source.FiniteGenealogyEncoding", "UnifiedLean.Source.FiniteSourceSnapshot", "G5BridgeBarrier", "G5CalendarRoutes", "G5ProtectiveBlock", "G5MinimalGraphInterface", "G6BridgeCannotEnterHybrid", "G5BridgeComponentEntries", "G5NonbridgeRouteBound", "G5ComponentCalendarCoverage", "G5ActualComponentSupport", "G5RootRouteCurrentSupport", "G5CurrentPortTwoPositions", "G5OriginalTipCurrentSupport", "G5ParentChoiceCalendar", "G5CoupledQuartetKernel", "G5FairSelectorMoments", "G5FairOriginalCoinLaw", "G5OriginalCoinPMF", "G5ParentPositionPushforward", "G5SafePastHybridDisjointness", "G5PairOnlySureBlockChronology", "G5SafePastMeetingPermanence", "G5ExponentialGermIdentification", "G5UnknownRateSupport", "G5OriginalRouteHazard", "G4TwoRootSourceStopping", "G1SharedRegisterStress", "G4FourRootPositivity", "G4IndependentRoutingBridge", "G4AllRootPairClocks", "G4PathResolvedMeasurement", "UnifiedLean.Source.NativeParentRouting", "UnifiedLean.Source.NativePairClockLaw", "UnifiedLean.Source.UniformizedSourceStep", "UnifiedLean.Source.SourceForestGeneratorIntertwining", "UnifiedLean.Source.SourceForestIntrinsicGenerator", "UnifiedLean.Source.SourceStepGeneratorBinding", "UnifiedLean.Source.MatrixProjectionExponential", "UnifiedLean.Source.SourceFiniteProjection", "UnifiedLean.Source.SourceForestPulseTransport", "UnifiedLean.Source.SourceForestPulseMeasure", "UnifiedLean.Source.SourceForestCommonPulse", "UnifiedLean.Source.SourceBoundaryKernels", "UnifiedLean.Source.SourceBoundaryProjection", "UnifiedLean.Source.SourcePoissonKernel", "UnifiedLean.Source.SourceProgramTransport", "UnifiedLean.Source.SourceCalendarCompatibility", "UnifiedLean.Source.SourceCalendarCompiler", "UnifiedLean.Source.SourceBoundaryLocations", "UnifiedLean.Source.SourceCalendarTiming", "UnifiedLean.Source.SourceCalendarPhysicalSupport", "UnifiedLean.Source.SourceInitializedCalendar", "UnifiedLean.Source.NativeIndependentPairMixture", "UnifiedLean.Source.SourceNaturalInitialization", "UnifiedLean.Source.UnrankedGenealogyObservation", "G1OpaqueSourceGrafting", "G1ContextualForestReplacement", "UnifiedLean.Source.SourceGeneratorExponential", "UnifiedLean.Source.SourcePoissonExponential", "UnifiedLean.Source.SourceEpochSemigroup", "UnifiedLean.Source.SourceActualHoldingClocks", "UnifiedLean.Source.SourceFirstMergerMark", "UnifiedLean.Source.SourceFirstMarkDistribution", "UnifiedLean.Source.SourceExponentialRace", "UnifiedLean.Source.SourceExponentialRaceDensity", "UnifiedLean.Source.SourceExponentialResiduals", "UnifiedLean.Source.SourceWinningClockReset", "UnifiedLean.Source.SourceMergerClockCatalogue", "UnifiedLean.Source.SourceDestinationClockReset", "UnifiedLean.Source.SourceEpochRenewal", "UnifiedLean.Source.SourceFiniteJumpExpansion", "UnifiedLean.Source.SourceRaceWinnerSelection", "UnifiedLean.Source.SourceEmbeddedJumpLaw", "UnifiedLean.Source.SourceAncestralCompletion", "UnifiedLean.Source.SourceCompletedUnrankedTree", "UnifiedLean.Source.SourceAncestralDrift", "UnifiedLean.Source.SourceAncestralAbsorption", "UnifiedLean.Source.SourceCompletionHarmonic", "UnifiedLean.Source.SourceEventualCompletionLimit", "UnifiedLean.Source.SourceNaturalCompletedLimit", "UnifiedLean.Source.SourceCopyCarrierTransport", "UnifiedLean.Source.SourceSmallCarrierGenerator", "UnifiedLean.Source.SourceCrossCarrierEpoch", "UnifiedLean.Source.SourceSmallCarrierPulse", "UnifiedLean.Source.SourceCrossCarrierBoundary", "UnifiedLean.Source.SourceCrossCarrierProgram", "UnifiedLean.Source.SourceCrossCarrierNatural", "UnifiedLean.Source.SourceUnrankedCopyProjectivity", "G1OriginalCurrentRootReconstruction", "G1NonrootBigonKernel", "G1ActualTwoPortBlob", "G1FiniteTwoPortChain", "G1ExtractedComponentProgram", "G1BigonFootprint", "G1BigonSpliceGraph", "G1JointSeparatedSourceGeometry", "G1ComponentDescendantClosure", "G1ActualCutDescendants", "G1NaturalCalendarNodes", "G1ActualEnteringFrontier", "G1InitializedFrontierPrefix", "G1OriginalRegistryBigon", "G1ActualJointGenerator", "G1TensorExponential", "G1ActualJointEpoch", "G1ActualJointBoundary", "G1ActualJointProgram", "G1ActualComponentAgenda", "G1CanonicalComponentSegment", "G1ActualCurrentPanelInitialization", "G1JointUnrankedForestAssembly", "G1JointForestPreservation", "G1ActualJointOpaqueContext", "G1SameOriginalExteriorContinuation", "G1InitializedJointComponentReplacement", "G1OriginalCalendarDecomposition", "G1ActualJointStageHistory", "G1OriginalEpochRecomposition", "G1ExteriorBoundarySilence", "G1InterleavedEpochCompression", "G1OriginalEpochPanelSilence", "G1OriginalEpochPanelCompression", "G1OriginalNodeBatchBinding", "G1OriginalExitBatchBinding", "G1CanonicalThreeEpochList", "G1CompactSourceComposition", "G1OriginalComponentNodeIdentity", "G1CanonicalEpochBlockBinding", "G1CanonicalEpochSpecialization", "G1CompactComponentBlockRows", "G1CanonicalCompactComponentRow", "G1CanonicalSingleExitSupport", "G1UnrankedSourceView", "G1UnrankedActualGenerator", "G1UnrankedActualEpoch", "G1UnrankedNaturalPulse", "G1UnrankedActualBoundary", "G1UnrankedActualFuture", "G1ActualUnrankedAncestralCompletion", "G1ActualUnrankedCompletedFuture", "G1UnrankedSingleExitLabel", "G1ActualUnrankedKMacro", "G1ActualKProductInsertion", "G1ActualCompletedKInsertion", "G1OriginalCompletedForestReconstruction", "G1CanonicalCompletedFutureRootAdmission", "G1OriginalForestKOnlyInsertion", "G1UnrankedExteriorHistoryKInsertion", "G1CompletedExteriorHistoryKInsertion", "G1CanonicalOriginalCompletedKLaw", "G1CanonicalCompactCompletedReplacement", "G1SpliceCutTransport", "G1SpliceRootBlob", "G1SpliceDegrees", "G1SpliceLSA", "G1SplicedSourceAdmission", "G1ActualGraphNormalization", "GraphPortConsequences", "G1ReducedQuotientGeometry", "G1ReducedCoreCounts", "G1BinaryCoreBudgets", "G1OriginalDecoratedSpan", "G1DecoratedOriginalProvenance", "G1LiftedOriginalBigon", "G1DecoratedSpliceConstruction", "G1FiniteOriginalDecoratedCore", "G1DecoratedRootBlobRetention", "G1OriginalSpanCalendarDecomposition", "G1OriginalSpanAtomAdmission", "G1OriginalMultiSpanCalendarRow", "G1OriginatedSpanRegistryAdmission", "G1OriginatedBridgeCalendarAdmission", "G1OriginalSpanBridgeBookends", "G1OriginatedBridgeBookends", "G1OriginalSpanClosingPhase", "G1OriginalSpanClosingSourceRow", "G1OriginalClosingCalendarBinding", "G1OriginalExteriorCohort", "G1OriginatedClosingSourceAdmission", "G1OriginatedTaxonReachTransport", "G1OriginalSpanRegion", "G1OriginatedNeutralSpanRegion", "G1SpanRegionExitClosure", "G1SpanRegionOriginalOperations", "G1DerivedSpanSeparatedAgenda", "G1ClosingSpanSafeSyntax", "G1InitializedOriginatedSpanSeparator", "G1OriginalWholeCausalView", "G1ActualSourceKMacroTransition", "G1SourceMacroComposition", "G1SourceMacroInterfaceHistory", "G1SourceMacroActualCompletion", "G1OriginalOpaqueExteriorView", "G1OriginalExteriorHistoryProduct", "G1ActualHistoryEnrichedKMacro", "G1OriginalHistoryQuotient", "G1RepeatedOriginalExteriorHistoryMacros", "G1RepeatedExteriorHistoryActualCompletion", "G1CanonicalOriginatedMacroPlans", "G1CanonicalOriginatedHistoryPlanner", "G1KOnlyCurrentRootExitView", "G1OriginalOpaqueKActorOutput", "G1CanonicalOriginalKOnlyActorRow", "G1KOnlyActorWholeExteriorHistory", "G1CanonicalKActorExteriorHistory", "G1OriginalKActorWholeViewAssembly", "G1KOnlyActorSameCompletedFuture", "G1CanonicalKActorCompletedHistory"]
  let imported := environment.header.moduleNames.map Name.toString
  let indices := environment.header.moduleNames.map (fun n => names.contains n.toString)
  let mut declarations : Array Json := #[]
  let mut invalid : Array Json := #[]
  let mut ownedAxioms : Array String := #[]
  let mut theorems : Nat := 0
  for (name, information) in environment.constants do
    if let some index := environment.getModuleIdxFor? name then
      if indices[index.toNat]! then
        let axioms ← collectAxioms name
        let kind := match information with
          | .thmInfo _ => "theorem"
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .opaqueInfo _ => "opaque"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .quotInfo _ => "quotient"
        if kind == "theorem" then theorems := theorems + 1
        if kind == "axiom" then ownedAxioms := ownedAxioms.push name.toString
        let refs := match information.value? (allowOpaque := true) with
          | some expression => expression.getUsedConstants.map Name.toString
          | none => #[]
        let record := Json.mkObj [
          ("module", toJson imported[index.toNat]!), ("name", toJson name.toString),
          ("kind", toJson kind), ("axioms", toJson (axioms.map Name.toString)),
          ("type_references", toJson (information.type.getUsedConstants.map Name.toString)),
          ("body_references", toJson refs)]
        declarations := declarations.push record
        if axioms.any (fun ax => ! #[``propext, ``Classical.choice, ``Quot.sound].contains ax) then
          invalid := invalid.push record
  let missing := names.filter (fun n => ! imported.contains n)
  let result := Json.mkObj [
    ("selected_modules", toJson names), ("all_imported_module_names", toJson imported),
    ("declaration_count", toJson declarations.size),
    ("theorem_declaration_count", toJson theorems), ("owned_axioms", toJson ownedAxioms),
    ("nonstandard_axiom_rows", toJson invalid), ("missing_modules", toJson missing),
    ("declarations", toJson declarations)]
  liftIO <| IO.FS.writeFile "AUDIT-RESULT.json" result.pretty
  logInfo m!"Fresh closure: {declarations.size} declarations, {theorems} theorems, {ownedAxioms.size} owned axioms, {invalid.size} nonstandard rows, {missing.size} missing modules"
  unless ownedAxioms.isEmpty && invalid.isEmpty && missing.isEmpty do
    throwError "Fresh complete closure audit failed"
