import G1ActiveCoreBridgeCohorts
import G1ActualFinitePanelProgramTensor
import G1CanonicalCrossingCohortPartition
import G1CanonicalCrossingCompletedSourceLaw
import G1CanonicalCrossingPhysicalAdmission
import G1CanonicalCrossingRootAndKAdmission
import G1OriginalCrossingCalendar
import G1OriginalDescendantCohortAgenda
import G1SeparatedAgendaSupportCuts
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
