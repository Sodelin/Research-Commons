import G1ActualCrossingWholeExteriorHistory
import G1ActualSelectedHistoryEndpoints
import G1ActualThreePanelSourceHistoryTensor
import G1CrossingHistorySameActualCompletion
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
