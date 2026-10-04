import G1ActualCompletedKInsertion
import G1ActualUnrankedAncestralCompletion
import G1ActualUnrankedCompletedFuture
import G1CanonicalCompletedFutureRootAdmission
import G1CanonicalOriginalCompletedKLaw
import G1CompletedExteriorHistoryKInsertion
import G1OriginalCompletedForestReconstruction
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
