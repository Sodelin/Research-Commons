import Lake
open Lake DSL
package connectedResearch

/-- Additive current1568 replay under the inherited strict compiler and storage supervisor. -/
@[default_target]
target connected pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/run_current.py"], cwd := some pkg.dir, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do error s!"Current union retained failed/blocked checks (exit {code})."

@[test_driver]
script verify (args) do
  let workspace ← getWorkspace
  let result ← IO.Process.output { cmd := "python3", args := #["scripts/run_current.py"] ++ args.toArray, cwd := some workspace.dir }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
