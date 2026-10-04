import G1ActualSourceKMacroTransition
import G1OriginalWholeCausalView
import G1SourceMacroActualCompletion
import G1SourceMacroComposition
import G1SourceMacroInterfaceHistory
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
