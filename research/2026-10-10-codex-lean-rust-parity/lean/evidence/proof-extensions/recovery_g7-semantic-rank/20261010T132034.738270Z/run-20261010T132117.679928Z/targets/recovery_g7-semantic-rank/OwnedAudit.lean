import G7ExactLawResourceGame
import G7ActualExactLawResponses
import G7ExactLawRankCompression
import G7OriginalFamilyStrategy
import G7OriginalCarrierCoverage
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["G7ExactLawResourceGame", "SourceNetwork", "G2LiveLineageRouting", "SourceLabelledForest", "SourceForestKingmanProjection", "SourceForestKingmanPopulationProjection", "UnifiedLean.Source.SourceForestSilentPruning", "UnifiedLean.Source.FiniteGenealogyEncoding", "UnifiedLean.Source.FiniteSourceSnapshot", "GraphLeaves", "GraphCuts", "G5BridgeBarrier", "G5CalendarRoutes", "G5ProtectiveBlock", "G5MinimalGraphInterface", "G6BridgeCannotEnterHybrid", "G5BridgeComponentEntries", "G5NonbridgeRouteBound", "G5ComponentCalendarCoverage", "G5ActualComponentSupport", "G5RootRouteCurrentSupport", "G5CurrentPortTwoPositions", "G5OriginalTipCurrentSupport", "G5ParentChoiceCalendar", "G5CoupledQuartetKernel", "G5FairSelectorMoments", "G5FairOriginalCoinLaw", "G5OriginalCoinPMF", "G5ParentPositionPushforward", "G5SafePastHybridDisjointness", "G5PairOnlySureBlockChronology", "G5SafePastMeetingPermanence", "G5ExponentialGermIdentification", "G5UnknownRateSupport", "G5OriginalRouteHazard", "G4TwoRootSourceStopping", "G1SharedRegisterStress", "G4FourRootPositivity", "G4IndependentRoutingBridge", "G4AllRootPairClocks", "G4PathResolvedMeasurement", "UnifiedLean.Source.NativeParentRouting", "UnifiedLean.Source.NativePairClockLaw", "UnifiedLean.Source.UniformizedSourceStep", "UnifiedLean.Source.SourceForestGeneratorIntertwining", "UnifiedLean.Source.SourceForestIntrinsicGenerator", "UnifiedLean.Source.SourceStepGeneratorBinding", "UnifiedLean.Source.MatrixProjectionExponential", "UnifiedLean.Source.SourceFiniteProjection", "UnifiedLean.Source.SourcePoissonKernel", "UnifiedLean.Source.SourceGeneratorExponential", "UnifiedLean.Source.SourcePoissonExponential", "UnifiedLean.Source.SourceEpochSemigroup", "UnifiedLean.Source.SourceCalendarCompatibility", "UnifiedLean.Source.SourceForestPulseTransport", "UnifiedLean.Source.SourceForestPulseMeasure", "UnifiedLean.Source.SourceForestCommonPulse", "UnifiedLean.Source.SourceBoundaryKernels", "UnifiedLean.Source.SourceBoundaryProjection", "UnifiedLean.Source.SourceProgramTransport", "UnifiedLean.Source.SourceCalendarCompiler", "UnifiedLean.Source.SourceBoundaryLocations", "UnifiedLean.Source.SourceCalendarTiming", "UnifiedLean.Source.SourceCalendarPhysicalSupport", "UnifiedLean.Source.SourceInitializedCalendar", "UnifiedLean.Source.SourceActualHoldingClocks", "UnifiedLean.Source.SourceFirstMergerMark", "UnifiedLean.Source.SourceFirstMarkDistribution", "UnifiedLean.Source.SourceExponentialRace", "UnifiedLean.Source.SourceExponentialRaceDensity", "UnifiedLean.Source.SourceExponentialResiduals", "UnifiedLean.Source.SourceWinningClockReset", "UnifiedLean.Source.SourceMergerClockCatalogue", "UnifiedLean.Source.SourceDestinationClockReset", "UnifiedLean.Source.SourceEpochRenewal", "UnifiedLean.Source.SourceFiniteJumpExpansion", "UnifiedLean.Source.SourceRaceWinnerSelection", "UnifiedLean.Source.SourceEmbeddedJumpLaw", "UnifiedLean.Source.NativeIndependentPairMixture", "UnifiedLean.Source.SourceNaturalInitialization", "UnifiedLean.Source.SourceAncestralCompletion", "UnifiedLean.Source.UnrankedGenealogyObservation", "UnifiedLean.Source.SourceCompletedUnrankedTree", "UnifiedLean.Source.SourceAncestralDrift", "UnifiedLean.Source.SourceAncestralAbsorption", "UnifiedLean.Source.SourceCompletionHarmonic", "UnifiedLean.G6.AncestralRateFree", "G7AncestralPolynomialKernel", "UnifiedLean.Source.SourceEventualCompletionLimit", "G7AncestralRationalCompletion", "UnifiedLean.Source.SourceNaturalCompletedLimit", "UnifiedLean.Source.SourceCopyCarrierTransport", "UnifiedLean.Source.SourceSmallCarrierGenerator", "UnifiedLean.Source.SourceCrossCarrierEpoch", "UnifiedLean.Source.SourceSmallCarrierPulse", "UnifiedLean.Source.SourceCrossCarrierBoundary", "UnifiedLean.Source.SourceCrossCarrierProgram", "G7SinglePopulationPolynomialKernel", "G7WholeAncestorPanelCode", "G7PopulationPanelPolynomial", "G1OpaqueSourceGrafting", "G1ContextualForestReplacement", "UnifiedLean.Source.SourceCrossCarrierNatural", "UnifiedLean.Source.SourceUnrankedCopyProjectivity", "G1OriginalCurrentRootReconstruction", "G1NonrootBigonKernel", "G1JointSeparatedSourceGeometry", "G1ActualJointGenerator", "G1TensorExponential", "G1ActualJointEpoch", "G1ActualJointBoundary", "G1ActualJointProgram", "ActualPopulationPanelSplit", "G7PopulationForestReassembly", "G7FiniteForestReassembly", "G7FullEpochPolynomial", "G5ActualNoMergerReadout", "G5OriginalProgramSurvival", "G5OriginalSelectedPosterior", "G5ActualRoutingSupport", "ActualSerialSurvival", "ActualPulseSurvival", "ActualPopulationRate", "ActualPulseOccupancy", "ActualBigonRate", "ActualBigonSurvival", "G7OriginalBoundaryPolynomial", "G7SelectedKernelPolynomial", "G7SelectedCompletionPolynomial", "G7OriginalInitializationPolynomial", "G6NaturalCellInverseRates", "OriginalCalendarSchema", "G7SymbolicProgramPolynomial", "UnifiedLean.Source.SourceUnrankedAllPanels", "UnifiedLean.Source.OriginalFixedIDControls", "UnifiedLean.Source.ControlledUnrankedSourceProjectivity", "G7ControlledWordPolynomial", "StrictAffineElimination", "NaturalCellAffineCompiler", "GeneratedNaturalChronology", "OriginalCalendarPattern", "G7NaturalCalendarPolynomial", "G7ControlledCalendarPolynomial", "G7CompletedCalendarPolynomial", "G7ActualExactLawResponses", "G7ExactLawRankCompression", "G7OriginalFamilyStrategy", "G7OriginalCensus", "G7OriginalRelabelling", "G7OriginalFiniteEncoding", "G7SourceStateRelabelling", "G7SnapshotRelabelling", "G7CoinReindexing", "G7BoundaryRelabelling", "G7SourceStepRelabelling", "G7ProgramRelabelling", "G7NaturalWordRelabelling", "G7GlobalOwnerCoins", "G7NodeActions", "G7BoundaryExitCommutation", "G7BoundaryPhasePermutation", "G7CalendarNodeRelabelling", "G7CalendarAgendaRelabelling", "G7NaturalCalendarRelabelling", "G7CompletedUnrankedRelabelling", "G7OriginalControlRelabelling", "GraphBlobs", "GraphBridgeSplits", "GraphSwitching", "GraphBlobOrientation", "GraphBlobLeaves", "GraphSwitchingDegree", "GraphQuartetExistence", "GraphTreePorts", "GraphPorts", "GraphBlobPorts", "GraphGalls", "G1CutChildPorts", "G1BlobDegreeBalance", "G1ActualTwoPortBlob", "G1FiniteTwoPortChain", "G1ExtractedComponentProgram", "G1BigonFootprint", "G1BigonSpliceGraph", "G1SpliceCutTransport", "G1SpliceRootBlob", "G1SpliceDegrees", "G1SpliceLSA", "G1SplicedSourceAdmission", "G1ActualGraphNormalization", "G7OriginalCarrierCoverage"]
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
