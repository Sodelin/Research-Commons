import NanuqActualAnchorPatterns
import NanuqActualBlobInternalPaths
import NanuqActualBlobSwitchingRestriction
import NanuqActualBridgeQuartetResolution
import NanuqActualCappedBlobCutReadout
import NanuqActualCappedHybridTips
import NanuqActualCappedQuartetReadout
import NanuqActualCurveCycle
import NanuqActualCurveOpening
import NanuqActualCurveWalk
import NanuqActualDistinctAnchor
import NanuqActualFourPortInvariance
import NanuqActualFullAnchor
import NanuqActualGalledChildBridge
import NanuqActualGalledHybridBoundary
import NanuqActualHybridChildTaxa
import NanuqActualIndependentParentChoices
import NanuqActualLocalChoiceCapGraph
import NanuqActualLocalChoiceQuartetMean
import NanuqActualNanuqAnchorBridge
import NanuqActualOpenedBinaryDegrees
import NanuqActualOpenedChoiceFamily
import NanuqActualOpenedCutProjection
import NanuqActualOpenedHybridTree
import NanuqActualOpenedIncidence
import NanuqActualOpenedQuartetReadout
import NanuqActualOpenedRootedAdmission
import NanuqActualOpenedSelection
import NanuqActualOpenedTipMultiplicity
import NanuqActualOriginalCurveAdapter
import NanuqActualPortCardinality
import NanuqActualPortCutFibre
import NanuqActualPortLeafCap
import NanuqActualPortPairQuartet
import NanuqActualQuartetCutLocality
import NanuqActualQuartetCutLocalization
import NanuqActualQuartetPortBranching
import NanuqActualQuartetWitnessSymmetry
import NanuqActualRootSkeleton
import NanuqActualRootedCapAdmission
import NanuqActualRootedCapBoundary
import NanuqActualRootedCapDegrees
import NanuqActualRootedCapIncidence
import NanuqActualRootedCapPaths
import NanuqActualRootedCapReadout
import NanuqActualRootedCapSwitching
import NanuqActualSelectedBlobGraph
import NanuqActualSourceCycleCurve
import NanuqActualWeightedAnchorComposition
import NanuqCutWalkLocality
import NanuqEdgeOccurrenceReadoutEquiv
import NanuqLeafEdgeWalkErase
import NanuqOriginalPlanarCurvesInterface
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["SourceNetwork", "GraphLeaves", "GraphCuts", "GraphBlobs", "GraphSwitching", "NanuqCutWalkLocality", "G5MinimalGraphInterface", "G2LiveLineageRouting", "G6BridgeCannotEnterHybrid", "RawSourceAnchorLocalization", "GraphBridgeSplits", "GraphBlobOrientation", "GraphBlobLeaves", "GraphSwitchingDegree", "GraphQuartetExistence", "GraphTreePorts", "GraphPorts", "GraphBlobPorts", "GraphPortTransport", "GraphPortFibers", "NanuqActualPortCutFibre", "NanuqActualQuartetCutLocality", "NanuqActualQuartetCutLocalization", "QuartetSemantics", "SourceQuartetRelation", "GraphSwitchingExistence", "GraphSwitchingFinite", "GraphGalls", "GraphSwitchingCuts", "SourceResolve", "NanuqActualFourPortInvariance", "NanuqActualBlobInternalPaths", "NanuqActualSelectedBlobGraph", "NanuqActualBlobSwitchingRestriction", "NanuqActualPortLeafCap", "NanuqActualCappedBlobCutReadout", "NanuqActualCappedQuartetReadout", "NanuqEdgeOccurrenceReadoutEquiv", "NanuqActualLocalChoiceCapGraph", "NanuqActualLocalChoiceQuartetMean", "NanuqActualRootedCapBoundary", "NanuqActualRootedCapIncidence", "NanuqActualRootedCapDegrees", "NanuqActualRootedCapPaths", "NanuqActualRootedCapAdmission", "NanuqActualPortCardinality", "NanuqActualRootedCapSwitching", "NanuqActualRootedCapReadout", "QuartetComposition", "QuartetCompositionDependent", "WeightedAnchor", "WeightedCoefficients", "WeightedOrderedPairs", "WeightedSource", "SourceCompositionBridge", "AnchorComposition", "AnchorPortPatterns", "AnchorPortFibers", "GraphQuartetBridge", "NanuqActualBridgeQuartetResolution", "NanuqActualPortPairQuartet", "NanuqActualAnchorPatterns", "GraphPortConsequences", "GraphBlobMedian", "GraphMedianUnique", "AnchorPortCounts", "NanuqActualQuartetPortBranching", "NanuqActualDistinctAnchor", "NanuqActualFullAnchor", "NanuqActualWeightedAnchorComposition", "NanuqActualQuartetWitnessSymmetry", "NanuqActualNanuqAnchorBridge", "NanuqActualGalledHybridBoundary", "NanuqLeafEdgeWalkErase", "NanuqActualGalledChildBridge", "NanuqActualCappedHybridTips", "NanuqActualRootSkeleton", "NanuqActualOpenedHybridTree", "NanuqActualOpenedIncidence", "NanuqActualHybridChildTaxa", "NanuqActualOpenedTipMultiplicity", "NanuqActualOpenedBinaryDegrees", "NanuqActualOpenedRootedAdmission", "NanuqActualOpenedSelection", "NanuqActualOpenedCutProjection", "NanuqActualOpenedQuartetReadout", "NanuqActualIndependentParentChoices", "NanuqActualOpenedChoiceFamily", "NanuqActualCurveOpening", "NanuqActualCurveCycle", "NanuqActualCurveWalk", "NanuqOriginalPlanarCurvesInterface", "NanuqActualOriginalCurveAdapter", "NanuqActualSourceCycleCurve"]
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
