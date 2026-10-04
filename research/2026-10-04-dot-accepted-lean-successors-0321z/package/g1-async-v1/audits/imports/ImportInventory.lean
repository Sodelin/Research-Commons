import G1ActualCrossingSourcePendingFusion
import G1ActualPurePanelJoin
import G1ActualThreePanelSourceTensor
import G1ConcurrentOriginalSourceWindow
import G1ConcurrentSpanPhysicalSeparation
import G1ConstructedPopulationPartition
import G1CrossingActorKernelFusion
import G1FiniteActorScheduleCommutation
import G1FinitePendingActorPromotion
import G1NestedOriginalSourceProjection
import G1OriginalRecipePopulationOwnership
import G1PendingActorInterfaceCommutation
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
