import G1OriginalClosingCalendarBinding
import G1OriginalExteriorCohort
import G1OriginalSpanBridgeBookends
import G1OriginalSpanClosingPhase
import G1OriginalSpanClosingSourceRow
import G1OriginatedBridgeBookends
import G1OriginatedClosingSourceAdmission
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
