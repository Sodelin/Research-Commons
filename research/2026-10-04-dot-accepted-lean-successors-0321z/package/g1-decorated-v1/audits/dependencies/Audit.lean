import G1DecoratedOriginalProvenance
import G1DecoratedRootBlobRetention
import G1DecoratedSpliceConstruction
import G1FiniteOriginalDecoratedCore
import G1LiftedOriginalBigon
import G1OriginalDecoratedSpan
import Lean.Util.CollectAxioms
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let selected : Array String := #["G1DecoratedOriginalProvenance","G1DecoratedRootBlobRetention","G1DecoratedSpliceConstruction","G1FiniteOriginalDecoratedCore","G1LiftedOriginalBigon","G1OriginalDecoratedSpan"]
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
