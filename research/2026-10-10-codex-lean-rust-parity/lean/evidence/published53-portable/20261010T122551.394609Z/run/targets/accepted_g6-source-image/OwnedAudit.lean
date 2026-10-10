import G6AffineAudit
import AffineRegression
import NaturalCellAffineCompiler
import StrictAffineElimination
import OriginalCalendarSchema
import G6CalendarSchemaAudit
import OriginalCalendarPattern
import ActualKernelCoefficientBound
import G6EffectiveModulusAudit
import ActualPolynomialEpochModulus
import G6FiniteCutWordAudit
import GeneratedCompleteBinProxy
import FiniteCutSourceWord
import GeneratedNaturalChronology
import G6GeneratedChartAudit
import RationalNaturalGrid
import GeneratedRationalSourceWitness
import G6NaturalCutAudit
import ArbitraryCutSharedBankProxy
import NaturalAncestralCutExtension
import G6PopulationPanelAudit
import ActualPopulationPanelSplit
import RationalNaturalCellWitness
import G6RationalWitnessAudit
import OriginalInheritanceRetuning
import SharedBankNaturalProxy
import SharedBankCompleteProxy
import G6SharedBankAudit
import G6NaturalCellInverseRates
import UpperRateCompleteObservation
import UpperRateNaturalHistory
import G6ProxyAudit
import UpperRateProxySupport
import ActualCalendarCutContext
import ActualCalendarEndpointHistory
import ActualCutJointLaw
import ActualCutTagRefinement
import ActualFiniteCutJointLaw
import ActualObservationCorruption
import ActualObservationCutRefinement
import ActualTailBinRow
import CompleteCalendarBinReadout
import CompleteCalendarJointLaw
import FiniteTagDecoder
import G6BridgeCannotEnterHybrid
import HybridSizeCore
import LiteralSameBinTrace
import NaturalCalendarPastAdmission
import NaturalPastCompleteObservation
import PrivateSeedFactorization
import PrivateSeedHistoryFactorization
import UnifiedLean.G6.AncestralRateFree
import UnifiedLean.G6.BinClock
import UnifiedLean.G6.BinFold
import UnifiedLean.G6.BinHistory
import UnifiedLean.G6.CompleteObservationPrefix
import UnifiedLean.G6.Conditioning
import UnifiedLean.G6.FiniteCorruptionBoundary
import UnifiedLean.G6.FiniteProbability
import UnifiedLean.G6.HistoryPrefix
import UnifiedLean.G6.InheritanceBankCommon
import UnifiedLean.G6.MeanEnclosure
import UnifiedLean.G6.PrivateRegisterBoundary
import UnifiedLean.G6.PrivateRegisterCalendar
import UnifiedLean.G6.PrivateRegisterCalendarPrefix
import UnifiedLean.G6.PrivateRegisterErasure
import UnifiedLean.G6.PrivateRegisterHistory
import UnifiedLean.G6.PrivateRegisterProgram
import UnifiedLean.G6.PrivateRegisterSourceStep
import UnifiedLean.G6.ProgramPrefix
import UnifiedLean.G6.RateBankCommon
import UnifiedLean.G6.RationalCertificate
import UnifiedLean.G6.RationalResidualCertificate
import UnifiedLean.G6.ResidualPrefix
import UnifiedLean.G6.ResidualProgram
import UnifiedLean.G6.SourcePrefix
import UnifiedLean.G6.TaylorCertificate
import UnifiedLean.G6.UpperMeanCommon
import UnifiedLean.G6.UpperRateSourceCommon
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["StrictAffineElimination", "SourceNetwork", "GraphLeaves", "GraphCuts", "G5BridgeBarrier", "G5CalendarRoutes", "G5ProtectiveBlock", "G5MinimalGraphInterface", "G2LiveLineageRouting", "G6BridgeCannotEnterHybrid", "G5BridgeComponentEntries", "G5NonbridgeRouteBound", "G5ComponentCalendarCoverage", "G5ActualComponentSupport", "G5RootRouteCurrentSupport", "G5CurrentPortTwoPositions", "G5OriginalTipCurrentSupport", "G5ParentChoiceCalendar", "SourceLabelledForest", "G5CoupledQuartetKernel", "G5FairSelectorMoments", "G5FairOriginalCoinLaw", "G5OriginalCoinPMF", "G5ParentPositionPushforward", "G5SafePastHybridDisjointness", "G5PairOnlySureBlockChronology", "G5SafePastMeetingPermanence", "G5ExponentialGermIdentification", "G5UnknownRateSupport", "G5OriginalRouteHazard", "G4TwoRootSourceStopping", "G1SharedRegisterStress", "G4FourRootPositivity", "G4IndependentRoutingBridge", "G4AllRootPairClocks", "G4PathResolvedMeasurement", "UnifiedLean.Source.NativeParentRouting", "UnifiedLean.Source.NativePairClockLaw", "UnifiedLean.Source.NativeIndependentPairMixture", "G6NaturalCellInverseRates", "NaturalCellAffineCompiler", "AffineRegression", "G6AffineAudit", "SourceForestKingmanProjection", "SourceForestKingmanPopulationProjection", "UnifiedLean.Source.SourceForestSilentPruning", "UnifiedLean.Source.FiniteGenealogyEncoding", "UnifiedLean.Source.FiniteSourceSnapshot", "UnifiedLean.Source.UniformizedSourceStep", "UnifiedLean.Source.SourceForestGeneratorIntertwining", "UnifiedLean.Source.SourceForestIntrinsicGenerator", "UnifiedLean.Source.SourceStepGeneratorBinding", "UnifiedLean.Source.MatrixProjectionExponential", "UnifiedLean.Source.SourceFiniteProjection", "UnifiedLean.Source.SourcePoissonKernel", "UnifiedLean.Source.SourceCalendarCompatibility", "UnifiedLean.Source.SourceForestPulseTransport", "UnifiedLean.Source.SourceForestPulseMeasure", "UnifiedLean.Source.SourceForestCommonPulse", "UnifiedLean.Source.SourceBoundaryKernels", "UnifiedLean.Source.SourceBoundaryProjection", "UnifiedLean.Source.SourceProgramTransport", "UnifiedLean.Source.SourceCalendarCompiler", "UnifiedLean.Source.SourceBoundaryLocations", "UnifiedLean.Source.SourceCalendarTiming", "UnifiedLean.Source.SourceCalendarPhysicalSupport", "UnifiedLean.Source.SourceInitializedCalendar", "UnifiedLean.Source.SourceNaturalInitialization", "OriginalCalendarSchema", "GeneratedNaturalChronology", "OriginalCalendarPattern", "G6CalendarSchemaAudit", "UnifiedLean.Source.SourceGeneratorExponential", "UnifiedLean.Source.SourcePoissonExponential", "UnifiedLean.Source.SourceEpochSemigroup", "UnifiedLean.Source.SourceActualHoldingClocks", "UnifiedLean.Source.SourceFirstMergerMark", "UnifiedLean.Source.SourceFirstMarkDistribution", "UnifiedLean.Source.SourceExponentialRace", "UnifiedLean.Source.SourceExponentialRaceDensity", "UnifiedLean.Source.SourceExponentialResiduals", "UnifiedLean.Source.SourceWinningClockReset", "UnifiedLean.Source.SourceMergerClockCatalogue", "UnifiedLean.Source.SourceDestinationClockReset", "UnifiedLean.Source.SourceEpochRenewal", "UnifiedLean.Source.SourceFiniteJumpExpansion", "UnifiedLean.Source.SourceRaceWinnerSelection", "UnifiedLean.Source.SourceEmbeddedJumpLaw", "UnifiedLean.Source.SourceAncestralCompletion", "UnifiedLean.Source.UnrankedGenealogyObservation", "UnifiedLean.Source.SourceCompletedUnrankedTree", "UnifiedLean.Source.SourceAncestralDrift", "UnifiedLean.Source.SourceAncestralAbsorption", "UnifiedLean.Source.SourceCompletionHarmonic", "UnifiedLean.G6.AncestralRateFree", "G7SinglePopulationPolynomialKernel", "ActualKernelCoefficientBound", "UnifiedLean.G6.FiniteProbability", "ActualPolynomialEpochModulus", "G6EffectiveModulusAudit", "G2FaithfulPairAgeDecoration", "G2SourceGraftDecoration", "UnifiedLean.Source.SourceLiteralClockEndpoint", "G2LiteralMarkedClockTrace", "G2ActualDecorationFold", "G2DecorationMeasurability", "G2MarkedTraceRenewal", "G2LiteralEpochLaw", "G2ActualCalendarTrace", "G2FiniteAncestralTrace", "UnifiedLean.Source.SourceEventualCompletionLimit", "G2AncestralTraceSourceLaw", "G2CompleteCalendarAttachment", "G2LiteralCutResidual", "G2MarkedTraceCuts", "G2MarkedTraceBudgetStability", "G2SameClockContinuation", "G2HistoryResidualAttachment", "G2CutFutureSourceBinding", "G2SameClockPastFutureLaw", "G2EpochHistoryReadout", "G2CompleteAncestralPath", "G2ChronologicalPathReadout", "G2CalendarDecoration", "G2CompleteDecoration", "G2CutResidualSourceMixture", "UnifiedLean.Source.SourceNaturalCompletedLimit", "UnifiedLean.Source.SourceCopyCarrierTransport", "UnifiedLean.Source.SourceSmallCarrierGenerator", "UnifiedLean.Source.SourceCrossCarrierEpoch", "UnifiedLean.Source.SourceSmallCarrierPulse", "UnifiedLean.Source.SourceCrossCarrierBoundary", "UnifiedLean.Source.SourceCrossCarrierProgram", "G2SourceFiniteHistory", "G2ActualEpochHistoryLaw", "G2EpochPathProjection", "G2ActualSegmentPathLaw", "G2FiniteFibreTransport", "G2CalendarHistoryBinding", "G2CalendarPathProjection", "G2CompletedCalendarPathLaw", "G2ChronologicalGluing", "G2ActualChronologicalPathLaw", "G2EventualPathReadout", "G2ActualPairCoalescence", "UnifiedLean.G6.BinHistory", "UnifiedLean.G6.BinFold", "ActualCutTagRefinement", "G2PairBirthFold", "G2ClockBoundaryNull", "G2WholeMatrixAges", "UnifiedLean.G6.BinClock", "LiteralSameBinTrace", "ActualTailBinRow", "ActualCutJointLaw", "FiniteTagDecoder", "CompleteCalendarBinReadout", "CompleteCalendarJointLaw", "ActualCalendarCutContext", "ActualFiniteCutJointLaw", "UnifiedLean.G6.Conditioning", "UnifiedLean.G6.SourcePrefix", "UnifiedLean.G6.ProgramPrefix", "UnifiedLean.G6.HistoryPrefix", "ActualCalendarEndpointHistory", "ActualObservationCutRefinement", "FiniteCutSourceWord", "UnifiedLean.G6.TaylorCertificate", "UnifiedLean.G6.ResidualPrefix", "UnifiedLean.G6.MeanEnclosure", "UnifiedLean.G6.UpperMeanCommon", "UnifiedLean.G6.ResidualProgram", "UnifiedLean.G6.RateBankCommon", "UnifiedLean.G6.UpperRateSourceCommon", "UnifiedLean.G6.PrivateRegisterErasure", "UnifiedLean.G6.PrivateRegisterSourceStep", "UnifiedLean.G6.PrivateRegisterBoundary", "UnifiedLean.G6.PrivateRegisterProgram", "PrivateSeedFactorization", "UnifiedLean.G6.PrivateRegisterHistory", "PrivateSeedHistoryFactorization", "UnifiedLean.G6.PrivateRegisterCalendar", "UnifiedLean.G6.PrivateRegisterCalendarPrefix", "NaturalCalendarPastAdmission", "UpperRateNaturalHistory", "UnifiedLean.G6.CompleteObservationPrefix", "NaturalPastCompleteObservation", "UpperRateCompleteObservation", "UpperRateProxySupport", "UnifiedLean.G6.InheritanceBankCommon", "OriginalInheritanceRetuning", "SharedBankNaturalProxy", "SharedBankCompleteProxy", "NaturalAncestralCutExtension", "ArbitraryCutSharedBankProxy", "GeneratedCompleteBinProxy", "G6FiniteCutWordAudit", "RationalNaturalGrid", "UnifiedLean.G6.RationalCertificate", "UnifiedLean.G6.RationalResidualCertificate", "RationalNaturalCellWitness", "GeneratedRationalSourceWitness", "G6GeneratedChartAudit", "G6NaturalCutAudit", "G1OpaqueSourceGrafting", "G1ContextualForestReplacement", "UnifiedLean.Source.SourceCrossCarrierNatural", "UnifiedLean.Source.SourceUnrankedCopyProjectivity", "G1OriginalCurrentRootReconstruction", "G1NonrootBigonKernel", "G1JointSeparatedSourceGeometry", "G1ActualJointGenerator", "G1TensorExponential", "G1ActualJointEpoch", "G1ActualJointBoundary", "G1ActualJointProgram", "ActualPopulationPanelSplit", "G6PopulationPanelAudit", "G6RationalWitnessAudit", "G6SharedBankAudit", "G6ProxyAudit", "UnifiedLean.G6.FiniteCorruptionBoundary", "ActualObservationCorruption", "HybridSizeCore"]
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
