import G5BinaryRootSuppressedCutEncoding
import G5FairNormalizedCutQuartetIdentification
import G5NormalizedSwitchingQuartetCompatibility
import G5OriginalPruningClusterPreservation
import G5OriginalSwitchingPruning
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
