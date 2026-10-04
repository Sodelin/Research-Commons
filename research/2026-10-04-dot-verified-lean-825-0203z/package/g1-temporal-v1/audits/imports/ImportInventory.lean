import G1ExteriorBoundarySilence
import G1InterleavedEpochCompression
import G1OriginalEpochRecomposition
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
