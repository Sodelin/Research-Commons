import G1ActualDisplayedTreeFamily
import G1ActualWholeUnrootedCutTreeFamily
import G1FiniteCoreWholeDisplayedTreeFamilies
import G1UnrankedTreeClusterUniqueness
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
