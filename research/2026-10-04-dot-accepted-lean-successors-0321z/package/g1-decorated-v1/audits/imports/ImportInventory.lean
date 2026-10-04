import G1DecoratedOriginalProvenance
import G1DecoratedRootBlobRetention
import G1DecoratedSpliceConstruction
import G1FiniteOriginalDecoratedCore
import G1LiftedOriginalBigon
import G1OriginalDecoratedSpan
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
