import Lake
open Lake DSL
package connectedResearch

/-- Modular named groups first, then a separately bounded compatible check. -/
@[default_target]
target connected pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/build_connected.py", "accepted"], cwd := some pkg.dir, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do error s!"Connected build has preserved failed/blocked targets (exit {code})."

/-- Independently source-reviewed historical candidates, explicitly not prior passes. -/
target candidates pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/build_connected.py", "provisional"], cwd := some pkg.dir, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do error s!"Candidate checks have preserved failed/blocked targets (exit {code})."

@[test_driver]
script verify (args) do
  let result ← IO.Process.output { cmd := "python3", args := #["scripts/build_connected.py"] ++ args.toArray }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode

/-- Scheduling-only continuation: reauthenticate four prior passes, check the remaining 49. -/
target remaining49 pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/resume_remaining49.py"], cwd := some pkg.dir, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do error s!"Remaining-target replay retained failed/blocked targets (exit {code})."

/-- Portable full replay with exact, resource-qualified aggregate/audit exceptions. -/
target connectedQualified pkg : Unit := do
  Job.async do
    let child ← IO.Process.spawn { cmd := "python3", args := #["scripts/build_resource_qualified.py"], cwd := some pkg.dir, stdout := .inherit, stderr := .inherit }
    let code ← child.wait
    unless code == 0 do error s!"Qualified connected replay retained failed/blocked targets (exit {code})."
