import G5ActualSingletonCalendarObservation
import G5FairM2Sharpness
import G5FairSharpnessSources
import G5FairSharpnessTargets
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
