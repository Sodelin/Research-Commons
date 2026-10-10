import AncestryExamples
import AncestryMixing
import AncestryObservation
import BlowUpRankInvariance
import ControlledMemory
import DeterministicEpigenetic
import DirectedIAP
import ExactAbstraction
import FeedbackDynamics
import FiniteEpigenetic
import FiniteFixation
import FiniteGenomeIdentifiability
import FogartyAffinity
import FogartyAffinityFixation
import FounderMaximal
import FounderWindow
import GenericCertificate
import GenericMortalRank
import GenericOrdinalCertificate
import GenericPruning
import GenericUniversalAvoiders
import HistoryConverse
import HistoryObservation
import HistoryPruning
import HistoryWellFounded
import MergeHistoryProjection
import NanuqPositiveCombination
import OrdinalCertificates
import OrdinalHistoryRank
import PortEncoding
import PredictiveState
import RankingReversal
import ReachableRankNecessity
import RealFounderWindow
import RealSpeciesTheorem
import SeedIntersections
import SpeciesReindex
import SpeciesSeed
import StatefulCAReal
import StochasticAbstraction
import StochasticExamples
import TerminalCloneAvoiders
import ThreeTaxonFiniteEvidence
import ThreeTaxonIdentifiability
import WongAdaptiveSelection
import WongBigARGAbsorption
import WongBigARGDrift
import WongBreakpointCells
import WongCountChain
import WongDatedSupport
import WongDiamond
import WongEventDecoding
import WongEventEncoding
import WongExamples
import WongIntervalCanonicalization
import WongIntervalNormalization
import WongLocalArity
import WongLocalSimplification
import WongMRCATruncation
import WongMarkedDated
import WongMarkedLaw
import WongMarkedMeasurable
import WongMarkedProcess
import WongMarkedRecorder
import WongMarkedSupport
import WongMemoizedTracing
import WongPedigreeBridge
import WongPedigreeRobust
import WongPredictiveBridge
import WongRecordTracing
import WongSampleTracing
import WongSimplification
import WongSimplificationNormalForm
import WongTimedHistory
import WongWaitingTimes
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["SamuelAlexanderResearch.SpeciesBridge", "SamuelAlexanderResearch.SpeciesGlobalIAP", "AncestryMixing", "AncestryExamples", "ExactAbstraction", "PredictiveState", "SamuelAlexanderResearch.AncestryViews", "SamuelAlexanderResearch.AncestralRestriction", "AncestryObservation", "GenericCertificate", "SamuelAlexanderResearch.BirthOrder", "SamuelAlexanderResearch.BinaryAvoidance", "SamuelAlexanderResearch.BinaryPopulation", "SamuelAlexanderResearch.PositiveUnavoidability", "SamuelAlexanderResearch.ThueMorseBound", "SamuelAlexanderResearch.ThueMorseBits", "SamuelAlexanderResearch.SharpThueMorse", "SamuelAlexanderResearch.SharpCorollaries", "SamuelAlexanderResearch.QuantitativeAvoidance", "SamuelAlexanderResearch.FiniteEditStability", "SamuelAlexanderResearch.PhaseShift", "SamuelAlexanderResearch.PopulationCounting", "SamuelAlexanderResearch.InfiniteConservation", "SamuelAlexanderResearch.SpeciesCones", "SamuelAlexanderResearch.SpeciesRootCriterion", "SamuelAlexanderResearch.GeneralRootObstruction", "SamuelAlexanderResearch.PopulationReindex", "RealBridges", "GenericUniversalAvoiders", "BlowUpRankInvariance", "ControlledMemory", "DeterministicEpigenetic", "FounderWindow", "SamuelAlexanderResearch.FixedGenderLift", "SamuelAlexanderResearch.FixedGenderReindex", "SamuelAlexanderResearch.ProductiveCore", "DirectedIAP", "FeedbackDynamics", "FiniteFixation", "FiniteEpigenetic", "SamuelAlexanderResearch.SpeciesAdapter", "SamuelAlexanderResearch.HistoryProjection", "WongGARG", "SamuelAlexanderResearch.AncestryContraction", "SamuelAlexanderResearch.FiniteHistoryCompletion", "WongAlexander", "FiniteGenomeIdentifiability", "FogartyAffinity", "FogartyAffinityFixation", "RealFounderWindow", "FounderMaximal", "GenericPruning", "GenericMortalRank", "GenericOrdinalCertificate", "SamuelAlexanderResearch.LayeredUnavoidability", "ReachableRankNecessity", "HistoryWellFounded", "HistoryConverse", "HistoryObservation", "HistoryPruning", "MergeHistoryProjection", "NanuqPositiveCombination", "OrdinalCertificates", "OrdinalHistoryRank", "SamuelAlexanderResearch.FinitePhasePaths", "SamuelAlexanderResearch.PortDynamics", "PortEncoding", "RankingReversal", "SpeciesReindex", "SeedIntersections", "SpeciesSeed", "RealSpeciesTheorem", "SamuelAlexanderResearch.StatefulCA", "StatefulCAReal", "StochasticAbstraction", "StochasticExamples", "TerminalCloneAvoiders", "ThreeTaxonFiniteEvidence", "ThreeTaxonIdentifiability", "WongCountChain", "WongBigARGDrift", "WongBigARGAbsorption", "WongWaitingTimes", "WongMarkedLaw", "WongEventEncoding", "WongEventDecoding", "WongMarkedRecorder", "WongMarkedProcess", "WongMarkedMeasurable", "WongAdaptiveSelection", "WongBreakpointCells", "WongMarkedSupport", "WongMarkedDated", "WongDatedSupport", "WongDiamond", "WongExamples", "WongIntervalNormalization", "WongSimplification", "WongIntervalCanonicalization", "WongLocalArity", "WongLocalSimplification", "WongMRCATruncation", "WongSampleTracing", "WongRecordTracing", "WongMemoizedTracing", "SamuelAlexanderResearch.ObservationPrediction", "WongPedigreeBridge", "WongPedigreeRobust", "WongPredictiveBridge", "WongSimplificationNormalForm", "WongTimedHistory"]
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
