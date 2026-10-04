import G1ActualDisplayedClusterSplitTransport
import G1ActualDisplayedQuartetTransport
import G1ActualSelectedClusterTransport
import G1FiniteNormalizationDisplayedTargets
import G1SplicedOriginalSwitching
import G1SwitchingDescendantTransport
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
