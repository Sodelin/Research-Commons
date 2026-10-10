import G2AssembledBoundaryNull
import G2UniversalTransitionCriterion
import G2ActualSourceTransitionCriterion
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
open Lean Elab Command
set_option debug.skipKernelTC false
run_cmd do
  let env := (← getEnv).setExporting false
  let targets : Array Name := #[`SourceNetwork, `G2LiveLineageRouting, `SourceLabelledForest, `SourceForestKingmanProjection, `SourceForestKingmanPopulationProjection, `UnifiedLean.Source.SourceForestSilentPruning, `G2FaithfulPairAgeDecoration, `UnifiedLean.Source.FiniteGenealogyEncoding, `UnifiedLean.Source.FiniteSourceSnapshot, `GraphLeaves, `GraphCuts, `G5BridgeBarrier, `G5CalendarRoutes, `G5ProtectiveBlock, `G5MinimalGraphInterface, `G6BridgeCannotEnterHybrid, `G5BridgeComponentEntries, `G5NonbridgeRouteBound, `G5ComponentCalendarCoverage, `G5ActualComponentSupport, `G5RootRouteCurrentSupport, `G5CurrentPortTwoPositions, `G5OriginalTipCurrentSupport, `G5ParentChoiceCalendar, `G5CoupledQuartetKernel, `G5FairSelectorMoments, `G5FairOriginalCoinLaw, `G5OriginalCoinPMF, `G5ParentPositionPushforward, `G5SafePastHybridDisjointness, `G5PairOnlySureBlockChronology, `G5SafePastMeetingPermanence, `G5ExponentialGermIdentification, `G5UnknownRateSupport, `G5OriginalRouteHazard, `G4TwoRootSourceStopping, `G1SharedRegisterStress, `G4FourRootPositivity, `G4IndependentRoutingBridge, `G4AllRootPairClocks, `G4PathResolvedMeasurement, `UnifiedLean.Source.NativeParentRouting, `UnifiedLean.Source.NativePairClockLaw, `UnifiedLean.Source.UniformizedSourceStep, `G2SourceGraftDecoration, `UnifiedLean.Source.SourceForestGeneratorIntertwining, `UnifiedLean.Source.SourceForestIntrinsicGenerator, `UnifiedLean.Source.SourceStepGeneratorBinding, `UnifiedLean.Source.MatrixProjectionExponential, `UnifiedLean.Source.SourceFiniteProjection, `UnifiedLean.Source.SourcePoissonKernel, `UnifiedLean.Source.SourceGeneratorExponential, `UnifiedLean.Source.SourcePoissonExponential, `UnifiedLean.Source.SourceEpochSemigroup, `UnifiedLean.Source.SourceCalendarCompatibility, `UnifiedLean.Source.SourceForestPulseTransport, `UnifiedLean.Source.SourceForestPulseMeasure, `UnifiedLean.Source.SourceForestCommonPulse, `UnifiedLean.Source.SourceBoundaryKernels, `UnifiedLean.Source.SourceBoundaryProjection, `UnifiedLean.Source.SourceProgramTransport, `UnifiedLean.Source.SourceCalendarCompiler, `UnifiedLean.Source.SourceBoundaryLocations, `UnifiedLean.Source.SourceCalendarTiming, `UnifiedLean.Source.SourceCalendarPhysicalSupport, `UnifiedLean.Source.SourceInitializedCalendar, `UnifiedLean.Source.SourceActualHoldingClocks, `UnifiedLean.Source.SourceFirstMergerMark, `UnifiedLean.Source.SourceFirstMarkDistribution, `UnifiedLean.Source.SourceExponentialRace, `UnifiedLean.Source.SourceExponentialRaceDensity, `UnifiedLean.Source.SourceExponentialResiduals, `UnifiedLean.Source.SourceWinningClockReset, `UnifiedLean.Source.SourceMergerClockCatalogue, `UnifiedLean.Source.SourceDestinationClockReset, `UnifiedLean.Source.SourceEpochRenewal, `UnifiedLean.Source.SourceFiniteJumpExpansion, `UnifiedLean.Source.SourceRaceWinnerSelection, `UnifiedLean.Source.SourceLiteralClockEndpoint, `G2LiteralMarkedClockTrace, `G2ActualDecorationFold, `G2DecorationMeasurability, `G2MarkedTraceRenewal, `G2LiteralEpochLaw, `G2ActualCalendarTrace, `UnifiedLean.Source.SourceEmbeddedJumpLaw, `UnifiedLean.Source.NativeIndependentPairMixture, `UnifiedLean.Source.SourceNaturalInitialization, `UnifiedLean.Source.SourceAncestralCompletion, `G2FiniteAncestralTrace, `UnifiedLean.Source.UnrankedGenealogyObservation, `UnifiedLean.Source.SourceCompletedUnrankedTree, `UnifiedLean.Source.SourceAncestralDrift, `UnifiedLean.Source.SourceAncestralAbsorption, `UnifiedLean.Source.SourceCompletionHarmonic, `UnifiedLean.Source.SourceEventualCompletionLimit, `G2AncestralTraceSourceLaw, `G2CompleteCalendarAttachment, `G2LiteralCutResidual, `G2MarkedTraceCuts, `G2MarkedTraceBudgetStability, `G2SameClockContinuation, `G2HistoryResidualAttachment, `G2CutFutureSourceBinding, `G2SameClockPastFutureLaw, `G2EpochHistoryReadout, `G2CompleteAncestralPath, `G2ChronologicalPathReadout, `G2CalendarDecoration, `G2CompleteDecoration, `G2PairBirthFold, `G2ClockBoundaryNull, `G2WholeMatrixAges, `G2ChronologicalDecoration, `G2StrictClockDecoration, `G2OriginalProgramSafety, `G2TimedBoundMeasurability, `G2CutResidualSourceMixture, `UnifiedLean.Source.SourceNaturalCompletedLimit, `UnifiedLean.Source.SourceCopyCarrierTransport, `UnifiedLean.Source.SourceSmallCarrierGenerator, `UnifiedLean.Source.SourceCrossCarrierEpoch, `UnifiedLean.Source.SourceSmallCarrierPulse, `UnifiedLean.Source.SourceCrossCarrierBoundary, `UnifiedLean.Source.SourceCrossCarrierProgram, `G2SourceFiniteHistory, `G2ActualEpochHistoryLaw, `G2EpochPathProjection, `G2ActualSegmentPathLaw, `G2FiniteFibreTransport, `G2CalendarHistoryBinding, `G2CalendarPathProjection, `G2CompletedCalendarPathLaw, `G2ChronologicalGluing, `G2ActualChronologicalPathLaw, `G2EventualPathReadout, `G2ActualPairCoalescence, `G2CalendarPairSupport, `G2RationalAgeReadout, `G2PairBirthThreshold, `G2AncestralPairSupport, `G2AncestralAgeCertificate, `G2ChronologicalTraceCompatibility, `G2CalendarFirstAge, `UnifiedLean.Source.SourceCrossCarrierNatural, `UnifiedLean.Source.SourceUnrankedCopyProjectivity, `UnifiedLean.Source.SourceUnrankedAllPanels, `UnifiedLean.Source.OriginalFixedIDControls, `UnifiedLean.Source.ControlledUnrankedSourceProjectivity, `G2ControlledTraceAssembly, `G2RegisteredPathProjection, `G2OriginalAbsoluteAges, `G2JointTimedObservation, `G2CompleteTimedSupport, `G2TimedDecorationPruning, `G2ChronologicalPruning, `G2SourcePairMatrixReadout, `G2CompleteTerminalReadout, `G2FaithfulTimedOutput, `G2LiteralTimedObservationPruning, `G2ActualTimedAllPanelLaw, `G2TimedOutputForgetting, `G2RootedTimedOutputSupport, `G2AssembledBoundaryNull, `G2UniversalTransitionCriterion, `G2ActualSourceTransitionCriterion]
  let moduleNames := env.header.moduleNames
  let indices := moduleNames.map (fun n => targets.contains n)
  let mut rows : Array Json := #[]
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if indices[idx.toNat]! then
        let kind := match ci with
          | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
        let baseName : Option Name := match name with
          | .str base "_unsafe_rec" => some base
          | _ => none
        let baseInfo := baseName.bind (fun n => env.find? n)
        let axs ← collectAxioms name
        rows := rows.push <| Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleNames[idx.toNat]!.toString),
          ("kind", toJson kind), ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
          ("has_body", toJson (ci.value? true).isSome),
          ("type_references", toJson (ci.type.getUsedConstants.map Name.toString)),
          ("body_references", toJson (((ci.value? true).map Expr.getUsedConstants |>.getD #[]).map Name.toString)),
          ("axioms", toJson (axs.map Name.toString)),
          ("unsafe_rec_base", baseName.map (toJson ∘ Name.toString) |>.getD Json.null),
          ("base_exists", toJson baseInfo.isSome),
          ("base_unsafe", baseInfo.map (toJson ∘ ConstantInfo.isUnsafe) |>.getD Json.null),
          ("base_partial", baseInfo.map (toJson ∘ ConstantInfo.isPartial) |>.getD Json.null),
          ("same_base_type", baseInfo.map (fun b => toJson (b.type == ci.type)) |>.getD Json.null)]
  let out := Json.mkObj [("status", toJson "DIAGNOSTIC_COMPLETE_SAFETY_FLAG_ENUMERATION"),
    ("selected_modules", toJson (targets.map Name.toString)), ("declaration_count", toJson rows.size),
    ("declarations", Json.arr rows)]
  liftIO <| IO.FS.writeFile "G2-SAFETY-CENSUS.json" out.pretty
  logInfo m!"Complete current G2-context166 safety-flag census: {rows.size} declarations"
