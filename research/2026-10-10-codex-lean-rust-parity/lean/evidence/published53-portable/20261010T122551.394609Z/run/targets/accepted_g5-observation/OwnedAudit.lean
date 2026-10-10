import G5ActivatedPosteriorPlacement
import G5ActualActivatedPrefix
import G5ActualConditionalPartition
import G5ActualDiscreteCutEvent
import G5ActualFrozenTripleRow
import G5ActualNoEventEpoch
import G5ActualNoMergerReadout
import G5ActualPosteriorGerm
import G5ActualProtectiveOccupancy
import G5ActualRoutingSupport
import G5ActualTripleMoments
import G5ActualTwoCutPartitionLaw
import G5CompletionPairPersistence
import G5ConstantTagSource
import G5CutIntegrationAudit
import G5DirectUseAudit
import G5EnumeratedPosteriorGerm
import G5EnumeratedTripleRow
import G5IntegrationAudit
import G5NaturalCutAudit
import G5NaturalCutConsumer
import G5NaturalObservedCutMass
import G5ObservedBinHistory
import G5ObservedCutPosterior
import G5ObservedEpochConditioning
import G5ObservedTwoCutPartitionLaw
import G5OlderSideCutAudit
import G5OlderSideCutChart
import G5OlderSideCutConditionalLaw
import G5OriginalConditionedContinuation
import G5OriginalEpochChart
import G5OriginalInteriorCutLaw
import G5OriginalProgramSurvival
import G5OriginalSelectedPosterior
import G5PhysicalCutAudit
import G5PhysicalCutChart
import G5PhysicalCutConditionalLaw
import G5PosteriorAssemblyAudit
import G5PosteriorJointCell
import G5SelectedDiscreteSurvival
import G5SelectedSingletonCarrier
import G5SelectedSingletonRates
import G5SourcePairPersistence
import G5StrictBoundaryRoutes
import G5TaggedWordProgram
import G5ThreePhaseCompletion
import G5TimedCutReadout
import G5TripleMomentReconstruction
import G5TriplePartitionReadout
import G5TwoCutAudit
import G5TwoCutCompletedSource
import G5TwoCutPartitionDecoder
import G5TwoCutProgramSupport
import G5TwoCutSourceWord
import G5ObservedCompletedBins
import G2AssembledBoundaryNull
import G2RootedTimedOutputSupport
import G2TimedOutputForgetting
import G5ObservedForestBins
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["SourceNetwork", "G2LiveLineageRouting", "SourceLabelledForest", "SourceForestKingmanProjection", "SourceForestKingmanPopulationProjection", "UnifiedLean.Source.SourceForestSilentPruning", "UnifiedLean.Source.FiniteGenealogyEncoding", "UnifiedLean.Source.FiniteSourceSnapshot", "GraphLeaves", "GraphCuts", "G5BridgeBarrier", "G5CalendarRoutes", "G5ProtectiveBlock", "G5MinimalGraphInterface", "G6BridgeCannotEnterHybrid", "G5BridgeComponentEntries", "G5NonbridgeRouteBound", "G5ComponentCalendarCoverage", "G5ActualComponentSupport", "G5RootRouteCurrentSupport", "G5CurrentPortTwoPositions", "G5OriginalTipCurrentSupport", "G5ParentChoiceCalendar", "G5CoupledQuartetKernel", "G5FairSelectorMoments", "G5FairOriginalCoinLaw", "G5OriginalCoinPMF", "G5ParentPositionPushforward", "G5SafePastHybridDisjointness", "G5PairOnlySureBlockChronology", "G5SafePastMeetingPermanence", "G5ExponentialGermIdentification", "G5UnknownRateSupport", "G5OriginalRouteHazard", "G4TwoRootSourceStopping", "G1SharedRegisterStress", "G4FourRootPositivity", "G4IndependentRoutingBridge", "G4AllRootPairClocks", "G4PathResolvedMeasurement", "UnifiedLean.Source.NativeParentRouting", "UnifiedLean.Source.NativePairClockLaw", "UnifiedLean.Source.UniformizedSourceStep", "UnifiedLean.Source.SourceForestGeneratorIntertwining", "UnifiedLean.Source.SourceForestIntrinsicGenerator", "UnifiedLean.Source.SourceStepGeneratorBinding", "UnifiedLean.Source.MatrixProjectionExponential", "UnifiedLean.Source.SourceFiniteProjection", "UnifiedLean.Source.SourcePoissonKernel", "UnifiedLean.Source.SourceGeneratorExponential", "UnifiedLean.Source.SourcePoissonExponential", "UnifiedLean.Source.SourceEpochSemigroup", "UnifiedLean.Source.SourceCalendarCompatibility", "UnifiedLean.Source.SourceForestPulseTransport", "UnifiedLean.Source.SourceForestPulseMeasure", "UnifiedLean.Source.SourceForestCommonPulse", "UnifiedLean.Source.SourceBoundaryKernels", "UnifiedLean.Source.SourceBoundaryProjection", "UnifiedLean.Source.SourceProgramTransport", "UnifiedLean.Source.SourceCalendarCompiler", "UnifiedLean.Source.SourceBoundaryLocations", "UnifiedLean.Source.SourceCalendarTiming", "UnifiedLean.Source.SourceCalendarPhysicalSupport", "UnifiedLean.Source.SourceInitializedCalendar", "UnifiedLean.Source.SourceActualHoldingClocks", "G5ActualNoMergerReadout", "UnifiedLean.Source.NativeIndependentPairMixture", "UnifiedLean.Source.SourceNaturalInitialization", "G5OriginalProgramSurvival", "UnifiedLean.Source.SourceFirstMergerMark", "UnifiedLean.Source.SourceFirstMarkDistribution", "UnifiedLean.Source.SourceExponentialRace", "UnifiedLean.Source.SourceExponentialRaceDensity", "UnifiedLean.Source.SourceExponentialResiduals", "UnifiedLean.Source.SourceWinningClockReset", "UnifiedLean.Source.SourceMergerClockCatalogue", "UnifiedLean.Source.SourceDestinationClockReset", "UnifiedLean.Source.SourceEpochRenewal", "UnifiedLean.Source.SourceFiniteJumpExpansion", "UnifiedLean.Source.SourceRaceWinnerSelection", "UnifiedLean.Source.SourceEmbeddedJumpLaw", "UnifiedLean.Source.SourceAncestralCompletion", "UnifiedLean.Source.UnrankedGenealogyObservation", "UnifiedLean.Source.SourceCompletedUnrankedTree", "UnifiedLean.Source.SourceAncestralDrift", "UnifiedLean.Source.SourceAncestralAbsorption", "UnifiedLean.Source.SourceCompletionHarmonic", "UnifiedLean.Source.SourceEventualCompletionLimit", "UnifiedLean.Source.SourceNaturalCompletedLimit", "UnifiedLean.Source.SourceCopyCarrierTransport", "UnifiedLean.Source.SourceSmallCarrierGenerator", "UnifiedLean.Source.SourceCrossCarrierEpoch", "UnifiedLean.Source.SourceSmallCarrierPulse", "UnifiedLean.Source.SourceCrossCarrierBoundary", "UnifiedLean.Source.SourceCrossCarrierProgram", "UnifiedLean.Source.SourceCrossCarrierNatural", "G5OriginalSelectedPosterior", "G5ActualRoutingSupport", "G5SelectedSingletonCarrier", "G5SelectedDiscreteSurvival", "G5FrozenTriplePolynomialKernel", "G5TriplePartitionReadout", "G5SelectedSingletonRates", "G5ActualTripleMoments", "G5TripleMomentReconstruction", "G5ActualFrozenTripleRow", "G5EnumeratedTripleRow", "G5ActualDiscreteCutEvent", "G5FrozenTripleAnalyticSupport", "G5EnumeratedPosteriorGerm", "G5ObservedCutPosterior", "G1OpaqueSourceGrafting", "G1ContextualForestReplacement", "UnifiedLean.Source.SourceUnrankedCopyProjectivity", "G1OriginalCurrentRootReconstruction", "G1NonrootBigonKernel", "G5ActualActivatedPrefix", "G5PosteriorJointCell", "G5ActualConditionalPartition", "G5ActivatedPosteriorPlacement", "UnifiedLean.Source.SourceLiteralClockEndpoint", "G2LiteralMarkedClockTrace", "G2MarkedTraceRenewal", "G2LiteralEpochLaw", "G2LiteralCutResidual", "G2HistoryResidualAttachment", "G2CutFutureSourceBinding", "G2MarkedTraceCuts", "G2MarkedTraceBudgetStability", "G2SameClockContinuation", "G2SameClockPastFutureLaw", "G5ActualNoEventEpoch", "G5ActualPosteriorGerm", "G5StrictBoundaryRoutes", "G5ActualProtectiveOccupancy", "G2FaithfulPairAgeDecoration", "G2SourceGraftDecoration", "G2ActualDecorationFold", "G2DecorationMeasurability", "G2ActualCalendarTrace", "G2FiniteAncestralTrace", "G2AncestralTraceSourceLaw", "G2CompleteCalendarAttachment", "G2EpochHistoryReadout", "G2CompleteAncestralPath", "G2ChronologicalPathReadout", "G2CalendarDecoration", "G2CompleteDecoration", "G2CutResidualSourceMixture", "G2SourceFiniteHistory", "G2ActualEpochHistoryLaw", "G2EpochPathProjection", "G2ActualSegmentPathLaw", "G2FiniteFibreTransport", "G2CalendarHistoryBinding", "G2CalendarPathProjection", "G2CompletedCalendarPathLaw", "G2ChronologicalGluing", "G2ActualChronologicalPathLaw", "G2EventualPathReadout", "G2ActualPairCoalescence", "UnifiedLean.G6.BinHistory", "UnifiedLean.G6.BinFold", "G2PairBirthFold", "G2ClockBoundaryNull", "G2WholeMatrixAges", "UnifiedLean.G6.BinClock", "LiteralSameBinTrace", "G5SourcePairPersistence", "ActualCutTagRefinement", "ActualTailBinRow", "ActualCutJointLaw", "FiniteTagDecoder", "CompleteCalendarBinReadout", "CompleteCalendarJointLaw", "ActualCalendarCutContext", "ActualFiniteCutJointLaw", "UnifiedLean.G6.FiniteProbability", "UnifiedLean.G6.Conditioning", "UnifiedLean.G6.SourcePrefix", "UnifiedLean.G6.ProgramPrefix", "UnifiedLean.G6.HistoryPrefix", "ActualCalendarEndpointHistory", "G5ConstantTagSource", "ActualObservationCutRefinement", "G5TwoCutSourceWord", "G5TaggedWordProgram", "G5CompletionPairPersistence", "G5TwoCutCompletedSource", "G2ChronologicalDecoration", "G2StrictClockDecoration", "G2OriginalProgramSafety", "G2TimedBoundMeasurability", "G2CalendarPairSupport", "G2RationalAgeReadout", "G2PairBirthThreshold", "G2AncestralPairSupport", "G2AncestralAgeCertificate", "G2ChronologicalTraceCompatibility", "G2CalendarFirstAge", "UnifiedLean.Source.SourceUnrankedAllPanels", "UnifiedLean.Source.OriginalFixedIDControls", "UnifiedLean.Source.ControlledUnrankedSourceProjectivity", "G2ControlledTraceAssembly", "G2RegisteredPathProjection", "G2OriginalAbsoluteAges", "G2JointTimedObservation", "G2CompleteTimedSupport", "G2TimedDecorationPruning", "G2ChronologicalPruning", "G2SourcePairMatrixReadout", "G2CompleteTerminalReadout", "G2FaithfulTimedOutput", "G2LiteralTimedObservationPruning", "G2ActualTimedAllPanelLaw", "G5HiddenRegisterTimedProjectivity", "G5TimedCutReadout", "G5ObservedBinHistory", "G5ThreePhaseCompletion", "G5TwoCutProgramSupport", "G5TwoCutPartitionDecoder", "G5ActualTwoCutPartitionLaw", "G5ObservedEpochConditioning", "G5CutIntegrationAudit", "G5OriginalInteriorCutLaw", "G5DirectUseAudit", "G5OriginalConditionedContinuation", "G5IntegrationAudit", "G5NaturalCutConsumer", "G5NaturalObservedCutMass", "G5NaturalCutAudit", "G5ObservedTwoCutPartitionLaw", "UnifiedLean.G6.PrivateRegisterErasure", "UnifiedLean.G6.PrivateRegisterSourceStep", "UnifiedLean.G6.PrivateRegisterBoundary", "UnifiedLean.G6.PrivateRegisterProgram", "UnifiedLean.G6.PrivateRegisterCalendar", "UnifiedLean.G6.PrivateRegisterCalendarPrefix", "G5OriginalEpochChart", "G5PhysicalCutChart", "G5PhysicalCutConditionalLaw", "G5OlderSideCutChart", "G5OlderSideCutConditionalLaw", "G5OlderSideCutAudit", "G5PhysicalCutAudit", "G5PosteriorAssemblyAudit", "G5TwoCutAudit", "PrivateSeedFactorization", "UnifiedLean.G6.PrivateRegisterHistory", "PrivateSeedHistoryFactorization", "NaturalCalendarPastAdmission", "UnifiedLean.G6.CompleteObservationPrefix", "NaturalPastCompleteObservation", "NaturalAncestralCutExtension", "G5ObservedCompletedBins", "G2TimedOutputForgetting", "G2RootedTimedOutputSupport", "G2AssembledBoundaryNull", "G5ObservedForestBins"]
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
