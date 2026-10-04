import G1OriginalMultiSpanCalendarRow
import G1OriginalSpanAtomAdmission
import G1OriginalSpanCalendarDecomposition
import G1OriginatedBridgeCalendarAdmission
import G1OriginatedSpanRegistryAdmission
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
