import G1ActualCurrentPanelInitialization
import G1ActualJointBoundary
import G1ActualJointEpoch
import G1ActualJointGenerator
import G1ActualJointOpaqueContext
import G1ActualJointProgram
import G1ActualJointStageHistory
import G1JointForestPreservation
import G1JointSeparatedSourceGeometry
import G1JointUnrankedForestAssembly
import G1SameOriginalExteriorContinuation
import G1TensorExponential
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
