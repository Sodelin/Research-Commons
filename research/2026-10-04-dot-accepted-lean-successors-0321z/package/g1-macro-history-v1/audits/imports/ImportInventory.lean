import G1ActualHistoryEnrichedKMacro
import G1OriginalExteriorHistoryProduct
import G1OriginalHistoryQuotient
import G1OriginalOpaqueExteriorView
import G1RepeatedExteriorHistoryActualCompletion
import G1RepeatedOriginalExteriorHistoryMacros
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
