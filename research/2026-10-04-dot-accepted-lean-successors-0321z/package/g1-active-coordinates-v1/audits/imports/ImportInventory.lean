import G1ActualFiniteOriginalQuotientTensor
import G1FiniteOriginalCausalCoordinates
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
