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

/-- Run the same audited compilation with explicit generated certificate
sources, e.g. `lake test -- --extra-source /path/Certificate.lean`. -/
@[test_driver]
script verify (args) do
  let workspace ← getWorkspace
  let child ← IO.Process.spawn {
    cmd := "python3", args := #["-B", "build_lean.py"] ++ args.toArray,
    cwd := some workspace.dir, stdout := .inherit, stderr := .inherit }
  child.wait

/-- Complete byte-exact original selection; performs no Lean compilation.
Supply a fresh ASTRA_SOURCE_OUTPUT directory. -/
target materialize pkg : Unit := do
  Job.async do
    let some out ← IO.getEnv "ASTRA_SOURCE_OUTPUT"
      | error "ASTRA_SOURCE_OUTPUT must name a fresh directory"
    runPython pkg #["materialize.py", "--out", out]

/-- Reauthenticate the full public packet and historic execution evidence.
This does not assert a fresh rebuild of original components. -/
target accepted_baseline pkg : Unit := do
  Job.async do
    runPython pkg #["../2026-10-12-dot-accepted-connected-union1613-1737z/verify_public_packet.py"]

/-- Full replay is deliberately closed until its exact component/native
closure and historical resource prerequisites are authenticated. The original
adapter is preserved in the accepted packet; it is not run against that evidence
in place. Source materialization and historical verification remain available. -/
target full_replay _pkg : Unit := do
  Job.async do
    error "Full1613 replay blocked: compatible accepted component/native object closure is not supplied. The original adapter also retains historical 6 GiB compiler allowances, beyond this run's 4 GiB conservative policy, and writes replay evidence into its packet. Preserve the original packet; prepare an isolated authenticated replay before running it. See LEAN-INTEGRATION.md."
