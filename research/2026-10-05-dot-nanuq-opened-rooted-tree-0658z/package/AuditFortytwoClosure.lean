import AnchorComposition
import AnchorPortCounts
import AnchorPortFibers
import AnchorPortPatterns
import G2LiveLineageRouting
import G5MinimalGraphInterface
import G6BridgeCannotEnterHybrid
import GraphBlobLeaves
import GraphBlobMedian
import GraphBlobOrientation
import GraphBlobPorts
import GraphBlobs
import GraphBridgeSplits
import GraphCuts
import GraphGalls
import GraphLeaves
import GraphMedianUnique
import GraphPortConsequences
import GraphPortFibers
import GraphPortTransport
import GraphPorts
import GraphQuartetBridge
import GraphQuartetExistence
import GraphSwitching
import GraphSwitchingCuts
import GraphSwitchingDegree
import GraphSwitchingExistence
import GraphSwitchingFinite
import GraphTreePorts
import QuartetComposition
import QuartetCompositionDependent
import QuartetSemantics
import RawSourceAnchorLocalization
import SourceCompositionBridge
import SourceNetwork
import SourceQuartetRelation
import SourceResolve
import WeightedAnchor
import WeightedCoefficients
import WeightedOrderedPairs
import WeightedSource
import NanuqActualBridgeQuartetResolution
import NanuqActualQuartetPortBranching
import NanuqCutWalkLocality
import NanuqActualPortCutFibre
import NanuqActualQuartetCutLocality
import NanuqActualQuartetCutLocalization
import NanuqActualFourPortInvariance
import NanuqActualBlobInternalPaths
import NanuqActualSelectedBlobGraph
import NanuqActualBlobSwitchingRestriction
import NanuqActualPortLeafCap
import NanuqActualCappedBlobCutReadout
import NanuqActualCappedQuartetReadout
import NanuqEdgeOccurrenceReadoutEquiv
import NanuqActualLocalChoiceCapGraph
import NanuqActualLocalChoiceQuartetMean
import NanuqActualRootedCapBoundary
import NanuqActualRootedCapIncidence
import NanuqActualRootedCapDegrees
import NanuqActualRootedCapPaths
import NanuqActualRootedCapAdmission
import NanuqActualPortCardinality
import NanuqActualRootedCapSwitching
import NanuqActualRootedCapReadout
import NanuqActualPortPairQuartet
import NanuqActualAnchorPatterns
import NanuqActualDistinctAnchor
import NanuqActualFullAnchor
import NanuqActualWeightedAnchorComposition
import NanuqActualQuartetWitnessSymmetry
import NanuqActualNanuqAnchorBridge
import NanuqActualGalledHybridBoundary
import NanuqLeafEdgeWalkErase
import NanuqActualGalledChildBridge
import NanuqActualCappedHybridTips
import NanuqActualRootSkeleton
import NanuqActualOpenedHybridTree
import NanuqActualOpenedIncidence
import NanuqActualHybridChildTaxa
import NanuqActualOpenedTipMultiplicity
import NanuqActualOpenedBinaryDegrees
import NanuqActualOpenedRootedAdmission
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["AnchorComposition", "AnchorPortCounts", "AnchorPortFibers", "AnchorPortPatterns", "G2LiveLineageRouting", "G5MinimalGraphInterface", "G6BridgeCannotEnterHybrid", "GraphBlobLeaves", "GraphBlobMedian", "GraphBlobOrientation", "GraphBlobPorts", "GraphBlobs", "GraphBridgeSplits", "GraphCuts", "GraphGalls", "GraphLeaves", "GraphMedianUnique", "GraphPortConsequences", "GraphPortFibers", "GraphPortTransport", "GraphPorts", "GraphQuartetBridge", "GraphQuartetExistence", "GraphSwitching", "GraphSwitchingCuts", "GraphSwitchingDegree", "GraphSwitchingExistence", "GraphSwitchingFinite", "GraphTreePorts", "QuartetComposition", "QuartetCompositionDependent", "QuartetSemantics", "RawSourceAnchorLocalization", "SourceCompositionBridge", "SourceNetwork", "SourceQuartetRelation", "SourceResolve", "WeightedAnchor", "WeightedCoefficients", "WeightedOrderedPairs", "WeightedSource", "NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching", "NanuqCutWalkLocality", "NanuqActualPortCutFibre", "NanuqActualQuartetCutLocality", "NanuqActualQuartetCutLocalization", "NanuqActualFourPortInvariance", "NanuqActualBlobInternalPaths", "NanuqActualSelectedBlobGraph", "NanuqActualBlobSwitchingRestriction", "NanuqActualPortLeafCap", "NanuqActualCappedBlobCutReadout", "NanuqActualCappedQuartetReadout", "NanuqEdgeOccurrenceReadoutEquiv", "NanuqActualLocalChoiceCapGraph", "NanuqActualLocalChoiceQuartetMean", "NanuqActualRootedCapBoundary", "NanuqActualRootedCapIncidence", "NanuqActualRootedCapDegrees", "NanuqActualRootedCapPaths", "NanuqActualRootedCapAdmission", "NanuqActualPortCardinality", "NanuqActualRootedCapSwitching", "NanuqActualRootedCapReadout", "NanuqActualPortPairQuartet", "NanuqActualAnchorPatterns", "NanuqActualDistinctAnchor", "NanuqActualFullAnchor", "NanuqActualWeightedAnchorComposition", "NanuqActualQuartetWitnessSymmetry", "NanuqActualNanuqAnchorBridge", "NanuqActualGalledHybridBoundary", "NanuqLeafEdgeWalkErase", "NanuqActualGalledChildBridge", "NanuqActualCappedHybridTips", "NanuqActualRootSkeleton", "NanuqActualOpenedHybridTree", "NanuqActualOpenedIncidence", "NanuqActualHybridChildTaxa", "NanuqActualOpenedTipMultiplicity", "NanuqActualOpenedBinaryDegrees", "NanuqActualOpenedRootedAdmission"]
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
  liftIO <| IO.FS.writeFile "certification-fortytwo/AUDIT-CLOSURE.json" result.pretty
  logInfo m!"Fresh closure: {declarations.size} declarations, {theorems} theorems, {ownedAxioms.size} owned axioms, {invalid.size} nonstandard rows, {missing.size} missing modules"
  unless ownedAxioms.isEmpty && invalid.isEmpty && missing.isEmpty do
    throwError "Fresh complete closure audit failed"
