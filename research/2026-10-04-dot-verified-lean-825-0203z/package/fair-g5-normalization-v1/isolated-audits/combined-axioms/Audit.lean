import G5AllAgeSafeQuartetTransfer
import G5AncestralObservedPairGerm
import G5ArbitraryCoupledGroupCountTransfer
import G5AttainedOriginalTipChronology
import G5BinaryRootSuppressedCutEncoding
import G5ChronologicalQuartetWitnessTransfer
import G5CommonSwitchingPersistence
import G5CommonSwitchingQuartetWitness
import G5FairNormalizedCutQuartetIdentification
import G5FairRawDisplayedQuartetIdentification
import G5FairRawQuartetIdentificationFiniteLabels
import G5FiniteAttainedDeletionTrace
import G5NativeOriginalRouteCoverage
import G5NormalizedSwitchingQuartetCompatibility
import G5ObservableSafePairSupport
import G5OriginalGroupPathChronology
import G5OriginalPruningClusterPreservation
import G5OriginalSwitchingPruning
import G5OriginalTipRepresentativeDeletion
import G5SafeCommonGroupQuartetTransfer
import G5SafeCommonGroupSelector
import G5SharedObservableDeletionTrace
import G5SynchronizedObservableChronology
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array String := #["G5AllAgeSafeQuartetTransfer","G5AncestralObservedPairGerm","G5ArbitraryCoupledGroupCountTransfer","G5AttainedOriginalTipChronology","G5BinaryRootSuppressedCutEncoding","G5ChronologicalQuartetWitnessTransfer","G5CommonSwitchingPersistence","G5CommonSwitchingQuartetWitness","G5FairNormalizedCutQuartetIdentification","G5FairRawDisplayedQuartetIdentification","G5FairRawQuartetIdentificationFiniteLabels","G5FiniteAttainedDeletionTrace","G5NativeOriginalRouteCoverage","G5NormalizedSwitchingQuartetCompatibility","G5ObservableSafePairSupport","G5OriginalGroupPathChronology","G5OriginalPruningClusterPreservation","G5OriginalSwitchingPruning","G5OriginalTipRepresentativeDeletion","G5SafeCommonGroupQuartetTransfer","G5SafeCommonGroupSelector","G5SharedObservableDeletionTrace","G5SynchronizedObservableChronology"]
  let reportFile : String := "declarations.json"
  let progressFile : String := "progress.txt"
  let moduleSelected := env.header.moduleNames.map (fun n => selected.contains n.toString)
  let mut rows : Array Json := #[]
  let mut bad : Array Json := #[]
  let mut theoremCount : Nat := 0
  for (name, info) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if moduleSelected[index.toNat]! then
        let sourceModule := env.header.moduleNames[index.toNat]!.toString
        if rows.size % 500 == 0 then
          liftIO <| IO.FS.writeFile progressFile s!"BEFORE_AXIOMS {rows.size} {sourceModule} {name}"
        let axes ← collectAxioms name
        let kind := match info with
          | .thmInfo _ => "theorem"
          | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque"
          | .defnInfo _ => "definition"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .quotInfo _ => "quotient"
        if kind == "theorem" then theoremCount := theoremCount + 1
        let row := Json.mkObj [
          ("module", toJson sourceModule), ("name", toJson name.toString),
          ("kind", toJson kind), ("axioms", toJson (axes.map Name.toString))]
        rows := rows.push row
        if axes.any (fun a => ! #[``propext, ``Classical.choice, ``Quot.sound].contains a) then
          bad := bad.push row
  let imported := env.header.moduleNames.map Name.toString
  let missing := selected.filter (fun m => ! imported.contains m)
  let result := Json.mkObj [
    ("selected_modules", toJson selected), ("declaration_count", toJson rows.size),
    ("theorem_declaration_count", toJson theoremCount), ("missing_modules", toJson missing),
    ("nonstandard_axiom_rows", toJson bad), ("declarations", toJson rows)]
  liftIO <| IO.FS.writeFile reportFile result.pretty
  logInfo m!"All selected declarations: {rows.size}; theorem declarations: {theoremCount}; bad axioms: {bad.size}; missing modules: {missing.size}"
  unless bad.isEmpty && missing.isEmpty do
    throwError "Selected declaration axiom audit failed"
