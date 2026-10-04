import G1AllNActualOuterSourceSharpness
import G1ConvexOriginalEdgeDrawing
import G1SharpCoreCombAdmission
import G1SharpCoreCombCutChild
import G1SharpCoreCombDefinition
import G1SharpCoreCombDegrees
import G1SharpCoreCombLSA
import G1SharpCoreCombOuterEmbedding
import G1SharpCoreCombOuterOrder
import G1SharpCoreCombReduced
import G1SharpCoreCombRootedness
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
