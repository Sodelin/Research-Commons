import G1ActualKProductInsertion
import G1ActualUnrankedKMacro
import G1OriginalForestKOnlyInsertion
import G1UnrankedActualBoundary
import G1UnrankedActualEpoch
import G1UnrankedActualFuture
import G1UnrankedActualGenerator
import G1UnrankedExteriorHistoryKInsertion
import G1UnrankedNaturalPulse
import G1UnrankedSingleExitLabel
import G1UnrankedSourceView
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
