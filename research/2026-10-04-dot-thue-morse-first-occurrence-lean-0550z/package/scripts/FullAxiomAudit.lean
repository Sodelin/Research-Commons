import ThueMorseMAP.Headline
import Lean
open Lean Elab Command
run_cmd do
  let selected : Array String := #[
    "SamuelAlexanderResearch.ThueMorseBits", "ThueMorseMAP.Basic",
    "ThueMorseMAP.Blocks", "ThueMorseMAP.OddMinus", "ThueMorseMAP.EvenMinus",
    "ThueMorseMAP.Plus", "ThueMorseMAP.Headline"]
  let env ← getEnv
  let moduleSelected := env.header.moduleNames.map (fun n => selected.contains n.toString)
  let mut rows : Array Json := #[]
  let mut bad : Array Json := #[]
  for (name, info) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if moduleSelected[index.toNat]! then
        let sourceModule := env.header.moduleNames[index.toNat]!.toString
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
    ("missing_modules", toJson missing), ("nonstandard_axiom_rows", toJson bad),
    ("declarations", toJson rows)]
  let destination ← liftIO <| IO.getEnv "TM_AUDIT_REPORT"
  let path := destination.getD "verification/FULL-OWNED-AXIOMS.json"
  liftIO <| IO.FS.writeFile path result.pretty
  logInfo m!"All selected declarations including generated/private: {rows.size}; bad axioms: {bad.size}; missing modules: {missing.size}"
  unless bad.isEmpty && missing.isEmpty do
    throwError "Complete source-module axiom audit failed"
