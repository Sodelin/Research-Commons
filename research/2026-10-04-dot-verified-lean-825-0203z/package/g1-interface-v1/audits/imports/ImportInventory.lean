import G1ActualComponentAgenda
import G1ActualCutDescendants
import G1ActualEnteringFrontier
import G1CanonicalComponentSegment
import G1InitializedFrontierPrefix
import G1InitializedJointComponentReplacement
import G1NaturalCalendarNodes
import G1OriginalRegistryBigon
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
