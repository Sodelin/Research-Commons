import G3ActualFixedResidueCriticalFiniteness
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let environment ← getEnv
  let names : Array String := #["G3BernoulliDerivatives", "G3BernoulliCriticalNumerators", "G3AllResiduePositivity", "G3AllResidueNormalIdentities", "G3BernoulliVerticalExclusion", "G3FixedDegreeResultants", "G3CriticalProjectionPolynomials", "G3CriticalCoefficientLists", "G3CriticalBivariateLists", "G3CriticalSourceArrayBinding", "G3CriticalFinSixExpansion", "G3CriticalSourceFactors3", "G3CriticalSliceSourceBinding3", "G3CriticalSourceFactors5", "G3CriticalSliceSourceBinding5", "G3CriticalSourceBlock3_0", "G3CriticalSourceBlock3_1", "G3CriticalSourceBlock3_2", "G3CriticalSourceBlock3_3", "G3CriticalSourceBlock3_4", "G3CriticalSourceBlock3_5", "G3CriticalSourceBlock3_6", "G3CriticalSourceBlock3_7", "G3CriticalSourceBlock3_8", "G3CriticalSourceBlock3_9", "G3CriticalSourceBlock3_10", "G3CriticalSourceBlock3_11", "G3CriticalSourceBlock3_12", "G3CriticalSourceBlock3_13", "G3CriticalSourceBlock3_14", "G3CriticalSourceBlock3_15", "G3CriticalSourceBlock3_16", "G3CriticalSourceBlock3_17", "G3CriticalSourceBlock3_18", "G3CriticalSourceBlock3_19", "G3CriticalSourceBlock3_20", "G3CriticalSourceBlock3_21", "G3CriticalSourceBlock3_22", "G3CriticalBlockReconstruction", "G3CriticalSliceCoefficientData", "G3CriticalSourceBlockAssembly3", "G3CriticalSourceBlock5_0", "G3CriticalSourceBlock5_1", "G3CriticalSourceBlock5_2", "G3CriticalSourceBlock5_3", "G3CriticalSourceBlock5_4", "G3CriticalSourceBlock5_5", "G3CriticalSourceBlock5_6", "G3CriticalSourceBlock5_7", "G3CriticalSourceBlock5_8", "G3CriticalSourceBlock5_9", "G3CriticalSourceBlock5_10", "G3CriticalSourceBlock5_11", "G3CriticalSourceBlock5_12", "G3CriticalSourceBlock5_13", "G3CriticalSourceBlock5_14", "G3CriticalSourceBlock5_15", "G3CriticalSourceBlock5_16", "G3CriticalSourceBlock5_17", "G3CriticalSourceBlock5_18", "G3CriticalSourceBlock5_19", "G3CriticalSourceBlock5_20", "G3CriticalSourceBlock5_21", "G3CriticalSourceBlock5_22", "G3CriticalSourceBlockAssembly5", "G3CriticalModularLifting", "G3CriticalPositiveProduct", "G3CriticalExportedNoCommon", "G3CriticalSourceSliceCoprime", "G3ActualFixedResidueCriticalFiniteness"]
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
