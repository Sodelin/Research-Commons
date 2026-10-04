import G1ActualGraphNormalization
import G1BinaryCoreBudgets
import G1ComponentDescendantClosure
import G1ReducedCoreCounts
import G1ReducedQuotientGeometry
import Lean.Elab.Command
open Lean Elab Command
run_cmd do
  let env ← getEnv
  liftIO <| IO.FS.writeFile "modules.json" (toJson (env.header.moduleNames.map Name.toString)).pretty
