import Lake
open Lake DSL

package astraUnifiedIntegration

def runPython (pkg : Package) (args : Array String) : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "python3", args := #["-B"] ++ args, cwd := some pkg.dir,
    stdout := .inherit, stderr := .inherit }
  let code ← child.wait
  unless code == 0 do throw <| IO.userError s!"integration check failed (exit {code})"

/-- Fresh arithmetic/support kernel, pinned external cache reuse. Supply
ASTRA_LEAN_BIN, ASTRA_MATHLIB_ROOT, ASTRA_MATHLIB_STATE, and a fresh
ASTRA_LEAN_OUTPUT. -/
@[default_target]
target kernel pkg : Unit := do
  Job.async do runPython pkg #["build_lean.py"]

/-- Complete byte-exact original selection; performs no Lean compilation.
Supply a fresh ASTRA_SOURCE_OUTPUT directory. -/
target materialize pkg : Unit := do
  Job.async do
    let some out ← IO.getEnv "ASTRA_SOURCE_OUTPUT"
      | throw <| IO.userError "ASTRA_SOURCE_OUTPUT must name a fresh directory"
    runPython pkg #["materialize.py", "--out", out]

/-- Reauthenticate the full public packet and historic execution evidence.
This does not assert a fresh rebuild of original components. -/
target accepted_baseline pkg : Unit := do
  Job.async do
    runPython pkg #["../2026-10-12-dot-accepted-connected-union1613-1737z/verify_public_packet.py"]

/-- Original guarded replay adapter. It retains the original requirement for
the compatible accepted component/native closure and blocks if absent. -/
target full_replay pkg : Unit := do
  Job.async do
    runPython pkg #["../2026-10-12-dot-accepted-connected-union1613-1737z/scripts/run_current.py", "current/connected"]
