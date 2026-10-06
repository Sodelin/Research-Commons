import G2LiteralMarkedClockTrace
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-!
Complete newly authored module declaration audit. This audit itself does not
replace kernel checking or independent mathematical review. Every declaration
owned by the imported target module is selected by its environment module index,
including generated and private declarations, without a hand-picked name list.
-/
open Lean Elab Command
set_option debug.skipKernelTC false

run_cmd do
  let target := `G2LiteralMarkedClockTrace
  let env := (← getEnv).setExporting false
  let own := env.constants.toList.filter fun (name, _) =>
    match env.getModuleIdxFor? name with
    | none => false
    | some idx => env.header.moduleNames[idx.toNat]! == target
  let own := own.mergeSort (fun a b => Name.quickLt a.1 b.1)
  if own.isEmpty then throwError "No target module declarations found"
  let mut records : Array Json := #[]
  for (name, ci) in own do
    let typeRefs := ci.type.getUsedConstants.qsort Name.quickLt
    let value := ci.value? true
    let requiresBody := match ci with
      | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
      | _ => false
    if requiresBody && value.isNone then throwError "Missing declaration body in {name}"
    let bodyRefs := (value.map Expr.getUsedConstants |>.getD #[]).qsort Name.quickLt
    let axioms := (← collectAxioms name).qsort Name.quickLt
    let missing := (typeRefs ++ bodyRefs).filter fun n => (env.find? n).isNone
    if !missing.isEmpty then throwError "Unresolved referenced constants in {name}"
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial target declaration {name}"
    if axioms.any (fun a => a != `propext && a != `Classical.choice && a != `Quot.sound) then
      throwError "Unapproved transitive axioms in {name}: {axioms}"
    let kind := match ci with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    records := records.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("kind", toJson kind),
      ("level_parameters", toJson (ci.levelParams.map Name.toString)),
      ("type_expression", toJson (reprStr ci.type)),
      ("type_references", toJson (typeRefs.map Name.toString)),
      ("body_expression", value.map (fun e => toJson (reprStr e)) |>.getD Json.null),
      ("body_references", toJson (bodyRefs.map Name.toString)),
      ("axioms", toJson (axioms.map Name.toString)),
      ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial)]
  let result := Json.mkObj [("schema", toJson "complete-module-audit-v1"),
    ("module", toJson target.toString), ("declaration_count", toJson records.size),
    ("declarations", Json.arr records)]
  liftIO <| IO.println result.compress
