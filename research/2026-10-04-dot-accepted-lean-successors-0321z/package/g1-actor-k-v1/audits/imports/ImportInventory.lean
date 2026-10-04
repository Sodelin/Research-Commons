import G1CanonicalKActorCompletedHistory
import G1CanonicalKActorExteriorHistory
import G1CanonicalOriginalKOnlyActorRow
import G1KOnlyActorSameCompletedFuture
import G1KOnlyActorWholeExteriorHistory
import G1KOnlyCurrentRootExitView
import G1OriginalKActorWholeViewAssembly
import G1OriginalOpaqueKActorOutput
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
