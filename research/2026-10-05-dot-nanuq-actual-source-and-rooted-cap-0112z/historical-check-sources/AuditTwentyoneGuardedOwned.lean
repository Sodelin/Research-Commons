import guards.NanuqActualBridgeQuartetResolution
import guards.NanuqActualQuartetPortBranching
import guards.NanuqCutWalkLocality
import guards.NanuqActualPortCutFibre
import guards.NanuqActualQuartetCutLocality
import guards.NanuqActualQuartetCutLocalization
import guards.NanuqActualFourPortInvariance
import guards.NanuqActualBlobInternalPaths
import guards.NanuqActualSelectedBlobGraph
import guards.NanuqActualBlobSwitchingRestriction
import guards.NanuqActualPortLeafCap
import guards.NanuqActualCappedBlobCutReadout
import guards.NanuqActualCappedQuartetReadout
import guards.NanuqEdgeOccurrenceReadoutEquiv
import guards.NanuqActualLocalChoiceCapGraph
import guards.NanuqActualLocalChoiceQuartetMean
import guards.NanuqActualRootedCapBoundary
import guards.NanuqActualRootedCapIncidence
import guards.NanuqActualRootedCapDegrees
import guards.NanuqActualRootedCapPaths
import guards.NanuqActualRootedCapAdmission
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["guards.NanuqActualBridgeQuartetResolution", "guards.NanuqActualQuartetPortBranching", "guards.NanuqCutWalkLocality", "guards.NanuqActualPortCutFibre", "guards.NanuqActualQuartetCutLocality", "guards.NanuqActualQuartetCutLocalization", "guards.NanuqActualFourPortInvariance", "guards.NanuqActualBlobInternalPaths", "guards.NanuqActualSelectedBlobGraph", "guards.NanuqActualBlobSwitchingRestriction", "guards.NanuqActualPortLeafCap", "guards.NanuqActualCappedBlobCutReadout", "guards.NanuqActualCappedQuartetReadout", "guards.NanuqEdgeOccurrenceReadoutEquiv", "guards.NanuqActualLocalChoiceCapGraph", "guards.NanuqActualLocalChoiceQuartetMean", "guards.NanuqActualRootedCapBoundary", "guards.NanuqActualRootedCapIncidence", "guards.NanuqActualRootedCapDegrees", "guards.NanuqActualRootedCapPaths", "guards.NanuqActualRootedCapAdmission"]
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
  liftIO <| IO.FS.writeFile "certification-twentyone/AUDIT-GUARDEDOWNED.json" result.pretty
  logInfo m!"Fresh closure: {declarations.size} declarations, {theorems} theorems, {ownedAxioms.size} owned axioms, {invalid.size} nonstandard rows, {missing.size} missing modules"
  unless ownedAxioms.isEmpty && invalid.isEmpty && missing.isEmpty do
    throwError "Fresh complete closure audit failed"
