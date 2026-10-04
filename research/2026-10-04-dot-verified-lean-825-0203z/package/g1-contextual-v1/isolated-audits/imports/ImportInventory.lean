import G1ContextualForestReplacement
import G1FiniteTwoPortChain
import G1NonrootBigonKernel
import G1OpaqueSourceGrafting
import G1OriginalCurrentRootReconstruction
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
