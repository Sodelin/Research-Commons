import ResearchCommons.MSCI.JC69BoundaryOccupation
import ResearchCommons.MSCI.JC69CalendarOccupation
import ResearchCommons.MSCI.JC69WeightedTrace
import ResearchCommons.MSCI.JC69EndpointWeight
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["G1SharedRegisterStress", "G2ActualCalendarTrace", "G2ActualDecorationFold", "G2AncestralTraceSourceLaw", "G2CalendarDecoration", "G2ChronologicalDecoration", "G2ChronologicalPathReadout", "G2ClockBoundaryNull", "G2CompleteAncestralPath", "G2CompleteCalendarAttachment", "G2CompleteDecoration", "G2CutFutureSourceBinding", "G2DecorationMeasurability", "G2EpochHistoryReadout", "G2FaithfulPairAgeDecoration", "G2FiniteAncestralTrace", "G2HistoryResidualAttachment", "G2LiteralCutResidual", "G2LiteralEpochLaw", "G2LiteralMarkedClockTrace", "G2LiveLineageRouting", "G2MarkedTraceBudgetStability", "G2MarkedTraceCuts", "G2MarkedTraceRenewal", "G2PairBirthFold", "G2SameClockContinuation", "G2SameClockPastFutureLaw", "G2SourceGraftDecoration", "G2WholeMatrixAges", "G4AllRootPairClocks", "G4FourRootPositivity", "G4IndependentRoutingBridge", "G4PathResolvedMeasurement", "G4TwoRootSourceStopping", "G5ActualComponentSupport", "G5BridgeBarrier", "G5BridgeComponentEntries", "G5CalendarRoutes", "G5ComponentCalendarCoverage", "G5CoupledQuartetKernel", "G5CurrentPortTwoPositions", "G5ExponentialGermIdentification", "G5FairOriginalCoinLaw", "G5FairSelectorMoments", "G5MinimalGraphInterface", "G5NonbridgeRouteBound", "G5OriginalCoinPMF", "G5OriginalRouteHazard", "G5OriginalTipCurrentSupport", "G5PairOnlySureBlockChronology", "G5ParentChoiceCalendar", "G5ParentPositionPushforward", "G5ProtectiveBlock", "G5RootRouteCurrentSupport", "G5SafePastHybridDisjointness", "G5SafePastMeetingPermanence", "G5UnknownRateSupport", "G6BridgeCannotEnterHybrid", "GraphCuts", "GraphLeaves", "ResearchCommons.MSCI.JC69", "ResearchCommons.MSCI.JC69Tree", "ResearchCommons.MSCI.KilledClocks", "SourceForestKingmanPopulationProjection", "SourceForestKingmanProjection", "SourceLabelledForest", "SourceNetwork", "UnifiedLean.Source.FiniteGenealogyEncoding", "UnifiedLean.Source.FiniteSourceSnapshot", "UnifiedLean.Source.MatrixProjectionExponential", "UnifiedLean.Source.NativeIndependentPairMixture", "UnifiedLean.Source.NativePairClockLaw", "UnifiedLean.Source.NativeParentRouting", "UnifiedLean.Source.SourceActualHoldingClocks", "UnifiedLean.Source.SourceAncestralAbsorption", "UnifiedLean.Source.SourceAncestralCompletion", "UnifiedLean.Source.SourceAncestralDrift", "UnifiedLean.Source.SourceBoundaryKernels", "UnifiedLean.Source.SourceBoundaryLocations", "UnifiedLean.Source.SourceBoundaryProjection", "UnifiedLean.Source.SourceCalendarCompatibility", "UnifiedLean.Source.SourceCalendarCompiler", "UnifiedLean.Source.SourceCalendarPhysicalSupport", "UnifiedLean.Source.SourceCalendarTiming", "UnifiedLean.Source.SourceCompletedUnrankedTree", "UnifiedLean.Source.SourceCompletionHarmonic", "UnifiedLean.Source.SourceDestinationClockReset", "UnifiedLean.Source.SourceEmbeddedJumpLaw", "UnifiedLean.Source.SourceEpochRenewal", "UnifiedLean.Source.SourceEpochSemigroup", "UnifiedLean.Source.SourceEventualCompletionLimit", "UnifiedLean.Source.SourceExponentialRace", "UnifiedLean.Source.SourceExponentialRaceDensity", "UnifiedLean.Source.SourceExponentialResiduals", "UnifiedLean.Source.SourceFiniteJumpExpansion", "UnifiedLean.Source.SourceFiniteProjection", "UnifiedLean.Source.SourceFirstMarkDistribution", "UnifiedLean.Source.SourceFirstMergerMark", "UnifiedLean.Source.SourceForestCommonPulse", "UnifiedLean.Source.SourceForestGeneratorIntertwining", "UnifiedLean.Source.SourceForestIntrinsicGenerator", "UnifiedLean.Source.SourceForestPulseMeasure", "UnifiedLean.Source.SourceForestPulseTransport", "UnifiedLean.Source.SourceForestSilentPruning", "UnifiedLean.Source.SourceGeneratorExponential", "UnifiedLean.Source.SourceInitializedCalendar", "UnifiedLean.Source.SourceLiteralClockEndpoint", "UnifiedLean.Source.SourceMergerClockCatalogue", "UnifiedLean.Source.SourceNaturalInitialization", "UnifiedLean.Source.SourcePoissonExponential", "UnifiedLean.Source.SourcePoissonKernel", "UnifiedLean.Source.SourceProgramTransport", "UnifiedLean.Source.SourceRaceWinnerSelection", "UnifiedLean.Source.SourceStepGeneratorBinding", "UnifiedLean.Source.SourceWinningClockReset", "UnifiedLean.Source.UniformizedSourceStep", "UnifiedLean.Source.UnrankedGenealogyObservation", "ResearchCommons.MSCI.JC69CurrentPartition", "ResearchCommons.MSCI.JC69TraceOccupation", "ResearchCommons.MSCI.JC69Occupation", "ResearchCommons.MSCI.JC69BoundaryOccupation", "ResearchCommons.MSCI.JC69CalendarOccupation", "ResearchCommons.MSCI.JC69WeightedTrace", "ResearchCommons.MSCI.JC69EndpointWeight"]
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
  liftIO <| IO.FS.writeFile "OwnedAudit.json" result.pretty
  logInfo m!"Fresh closure: {declarations.size} declarations, {theorems} theorems, {ownedAxioms.size} owned axioms, {invalid.size} nonstandard rows, {missing.size} missing modules"
  unless ownedAxioms.isEmpty && invalid.isEmpty && missing.isEmpty do
    throwError "Fresh complete closure audit failed"
