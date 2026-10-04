import G1ActualCurrentPanelInitialization
import G1ActualJointBoundary
import G1ActualJointEpoch
import G1ActualJointGenerator
import G1ActualJointOpaqueContext
import G1ActualJointProgram
import G1ActualJointStageHistory
import G1ContextualForestReplacement
import G1ExteriorBoundarySilence
import G1InterleavedEpochCompression
import G1JointForestPreservation
import G1JointSeparatedSourceGeometry
import G1JointUnrankedForestAssembly
import G1NonrootBigonKernel
import G1OpaqueSourceGrafting
import G1OriginalCurrentRootReconstruction
import G1OriginalEpochRecomposition
import G1SameOriginalExteriorContinuation
import G1SharedRegisterStress
import G1TensorExponential
import G2LiveLineageRouting
import G4AllRootPairClocks
import G4FourRootPositivity
import G4IndependentRoutingBridge
import G4PathResolvedMeasurement
import G4TwoRootSourceStopping
import G5ActualComponentSupport
import G5BridgeBarrier
import G5BridgeComponentEntries
import G5CalendarRoutes
import G5ComponentCalendarCoverage
import G5CoupledQuartetKernel
import G5CurrentPortTwoPositions
import G5ExponentialGermIdentification
import G5FairOriginalCoinLaw
import G5FairSelectorMoments
import G5MinimalGraphInterface
import G5NonbridgeRouteBound
import G5OriginalCoinPMF
import G5OriginalRouteHazard
import G5OriginalTipCurrentSupport
import G5PairOnlySureBlockChronology
import G5ParentChoiceCalendar
import G5ParentPositionPushforward
import G5ProtectiveBlock
import G5RootRouteCurrentSupport
import G5SafePastHybridDisjointness
import G5SafePastMeetingPermanence
import G5UnknownRateSupport
import G6BridgeCannotEnterHybrid
import GraphCuts
import GraphLeaves
import SourceForestKingmanPopulationProjection
import SourceForestKingmanProjection
import SourceLabelledForest
import SourceNetwork
import UnifiedLean.Source.FiniteGenealogyEncoding
import UnifiedLean.Source.FiniteSourceSnapshot
import UnifiedLean.Source.MatrixProjectionExponential
import UnifiedLean.Source.NativeIndependentPairMixture
import UnifiedLean.Source.NativePairClockLaw
import UnifiedLean.Source.NativeParentRouting
import UnifiedLean.Source.SourceActualHoldingClocks
import UnifiedLean.Source.SourceAncestralAbsorption
import UnifiedLean.Source.SourceAncestralCompletion
import UnifiedLean.Source.SourceAncestralDrift
import UnifiedLean.Source.SourceBoundaryKernels
import UnifiedLean.Source.SourceBoundaryLocations
import UnifiedLean.Source.SourceBoundaryProjection
import UnifiedLean.Source.SourceCalendarCompatibility
import UnifiedLean.Source.SourceCalendarCompiler
import UnifiedLean.Source.SourceCalendarPhysicalSupport
import UnifiedLean.Source.SourceCalendarTiming
import UnifiedLean.Source.SourceCompletedUnrankedTree
import UnifiedLean.Source.SourceCompletionHarmonic
import UnifiedLean.Source.SourceCopyCarrierTransport
import UnifiedLean.Source.SourceCrossCarrierBoundary
import UnifiedLean.Source.SourceCrossCarrierEpoch
import UnifiedLean.Source.SourceCrossCarrierNatural
import UnifiedLean.Source.SourceCrossCarrierProgram
import UnifiedLean.Source.SourceDestinationClockReset
import UnifiedLean.Source.SourceEmbeddedJumpLaw
import UnifiedLean.Source.SourceEpochRenewal
import UnifiedLean.Source.SourceEpochSemigroup
import UnifiedLean.Source.SourceEventualCompletionLimit
import UnifiedLean.Source.SourceExponentialRace
import UnifiedLean.Source.SourceExponentialRaceDensity
import UnifiedLean.Source.SourceExponentialResiduals
import UnifiedLean.Source.SourceFiniteJumpExpansion
import UnifiedLean.Source.SourceFiniteProjection
import UnifiedLean.Source.SourceFirstMarkDistribution
import UnifiedLean.Source.SourceFirstMergerMark
import UnifiedLean.Source.SourceForestCommonPulse
import UnifiedLean.Source.SourceForestGeneratorIntertwining
import UnifiedLean.Source.SourceForestIntrinsicGenerator
import UnifiedLean.Source.SourceForestPulseMeasure
import UnifiedLean.Source.SourceForestPulseTransport
import UnifiedLean.Source.SourceForestSilentPruning
import UnifiedLean.Source.SourceGeneratorExponential
import UnifiedLean.Source.SourceInitializedCalendar
import UnifiedLean.Source.SourceMergerClockCatalogue
import UnifiedLean.Source.SourceNaturalCompletedLimit
import UnifiedLean.Source.SourceNaturalInitialization
import UnifiedLean.Source.SourcePoissonExponential
import UnifiedLean.Source.SourcePoissonKernel
import UnifiedLean.Source.SourceProgramTransport
import UnifiedLean.Source.SourceRaceWinnerSelection
import UnifiedLean.Source.SourceSmallCarrierGenerator
import UnifiedLean.Source.SourceSmallCarrierPulse
import UnifiedLean.Source.SourceStepGeneratorBinding
import UnifiedLean.Source.SourceUnrankedCopyProjectivity
import UnifiedLean.Source.SourceWinningClockReset
import UnifiedLean.Source.UniformizedSourceStep
import UnifiedLean.Source.UnrankedGenealogyObservation
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array String := #["G1ActualCurrentPanelInitialization","G1ActualJointBoundary","G1ActualJointEpoch","G1ActualJointGenerator","G1ActualJointOpaqueContext","G1ActualJointProgram","G1ActualJointStageHistory","G1ContextualForestReplacement","G1ExteriorBoundarySilence","G1InterleavedEpochCompression","G1JointForestPreservation","G1JointSeparatedSourceGeometry","G1JointUnrankedForestAssembly","G1NonrootBigonKernel","G1OpaqueSourceGrafting","G1OriginalCurrentRootReconstruction","G1OriginalEpochRecomposition","G1SameOriginalExteriorContinuation","G1SharedRegisterStress","G1TensorExponential","G2LiveLineageRouting","G4AllRootPairClocks","G4FourRootPositivity","G4IndependentRoutingBridge","G4PathResolvedMeasurement","G4TwoRootSourceStopping","G5ActualComponentSupport","G5BridgeBarrier","G5BridgeComponentEntries","G5CalendarRoutes","G5ComponentCalendarCoverage","G5CoupledQuartetKernel","G5CurrentPortTwoPositions","G5ExponentialGermIdentification","G5FairOriginalCoinLaw","G5FairSelectorMoments","G5MinimalGraphInterface","G5NonbridgeRouteBound","G5OriginalCoinPMF","G5OriginalRouteHazard","G5OriginalTipCurrentSupport","G5PairOnlySureBlockChronology","G5ParentChoiceCalendar","G5ParentPositionPushforward","G5ProtectiveBlock","G5RootRouteCurrentSupport","G5SafePastHybridDisjointness","G5SafePastMeetingPermanence","G5UnknownRateSupport","G6BridgeCannotEnterHybrid","GraphCuts","GraphLeaves","SourceForestKingmanPopulationProjection","SourceForestKingmanProjection","SourceLabelledForest","SourceNetwork","UnifiedLean.Source.FiniteGenealogyEncoding","UnifiedLean.Source.FiniteSourceSnapshot","UnifiedLean.Source.MatrixProjectionExponential","UnifiedLean.Source.NativeIndependentPairMixture","UnifiedLean.Source.NativePairClockLaw","UnifiedLean.Source.NativeParentRouting","UnifiedLean.Source.SourceActualHoldingClocks","UnifiedLean.Source.SourceAncestralAbsorption","UnifiedLean.Source.SourceAncestralCompletion","UnifiedLean.Source.SourceAncestralDrift","UnifiedLean.Source.SourceBoundaryKernels","UnifiedLean.Source.SourceBoundaryLocations","UnifiedLean.Source.SourceBoundaryProjection","UnifiedLean.Source.SourceCalendarCompatibility","UnifiedLean.Source.SourceCalendarCompiler","UnifiedLean.Source.SourceCalendarPhysicalSupport","UnifiedLean.Source.SourceCalendarTiming","UnifiedLean.Source.SourceCompletedUnrankedTree","UnifiedLean.Source.SourceCompletionHarmonic","UnifiedLean.Source.SourceCopyCarrierTransport","UnifiedLean.Source.SourceCrossCarrierBoundary","UnifiedLean.Source.SourceCrossCarrierEpoch","UnifiedLean.Source.SourceCrossCarrierNatural","UnifiedLean.Source.SourceCrossCarrierProgram","UnifiedLean.Source.SourceDestinationClockReset","UnifiedLean.Source.SourceEmbeddedJumpLaw","UnifiedLean.Source.SourceEpochRenewal","UnifiedLean.Source.SourceEpochSemigroup","UnifiedLean.Source.SourceEventualCompletionLimit","UnifiedLean.Source.SourceExponentialRace","UnifiedLean.Source.SourceExponentialRaceDensity","UnifiedLean.Source.SourceExponentialResiduals","UnifiedLean.Source.SourceFiniteJumpExpansion","UnifiedLean.Source.SourceFiniteProjection","UnifiedLean.Source.SourceFirstMarkDistribution","UnifiedLean.Source.SourceFirstMergerMark","UnifiedLean.Source.SourceForestCommonPulse","UnifiedLean.Source.SourceForestGeneratorIntertwining","UnifiedLean.Source.SourceForestIntrinsicGenerator","UnifiedLean.Source.SourceForestPulseMeasure","UnifiedLean.Source.SourceForestPulseTransport","UnifiedLean.Source.SourceForestSilentPruning","UnifiedLean.Source.SourceGeneratorExponential","UnifiedLean.Source.SourceInitializedCalendar","UnifiedLean.Source.SourceMergerClockCatalogue","UnifiedLean.Source.SourceNaturalCompletedLimit","UnifiedLean.Source.SourceNaturalInitialization","UnifiedLean.Source.SourcePoissonExponential","UnifiedLean.Source.SourcePoissonKernel","UnifiedLean.Source.SourceProgramTransport","UnifiedLean.Source.SourceRaceWinnerSelection","UnifiedLean.Source.SourceSmallCarrierGenerator","UnifiedLean.Source.SourceSmallCarrierPulse","UnifiedLean.Source.SourceStepGeneratorBinding","UnifiedLean.Source.SourceUnrankedCopyProjectivity","UnifiedLean.Source.SourceWinningClockReset","UnifiedLean.Source.UniformizedSourceStep","UnifiedLean.Source.UnrankedGenealogyObservation"]
  let reportFile : String := "declarations.json"
  let progressFile : String := "progress.txt"
  let moduleSelected := env.header.moduleNames.map (fun n => selected.contains n.toString)
  let owned := fun (n : Name) => match env.getModuleIdxFor? n with
    | some i => moduleSelected[i.toNat]!
    | none => false
  let mut rows : Array Json := #[]
  for (name, info) in env.constants do
    if owned name then
      let sourceModule := env.header.moduleNames[(env.getModuleIdxFor? name).get!.toNat]!.toString
      let typeRefs := info.type.getUsedConstants
      let bodyRefs := match info.value? (allowOpaque := true) with
        | some e => e.getUsedConstants
        | none => #[]
      let headRef := match info.value? (allowOpaque := true) with
        | some e => match e.getAppFn with
          | .const n _ => if owned n then some n.toString else none
          | _ => none
        | none => none
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .axiomInfo _ => "axiom"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .quotInfo _ => "quotient"
      rows := rows.push <| Json.mkObj [
        ("module", toJson sourceModule), ("name", toJson name.toString),
        ("kind", toJson kind), ("all_type_references", toJson (typeRefs.map Name.toString)),
        ("all_body_references", toJson (bodyRefs.map Name.toString)),
        ("direct_head_delegation_candidate", toJson headRef)]
  liftIO <| IO.FS.writeFile reportFile (Json.mkObj [
    ("selected_modules", toJson selected), ("declaration_count", toJson rows.size),
    ("direct_dependencies_not_claim_implications", toJson true),
    ("head_delegation_not_mathematical_equivalence", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo m!"Compiled declaration dependency rows: {rows.size}"
