# G6 pinned selected-source verification

Owner: internal Dot-style Lean verification worker under `CLOUD-G6-SOL-ULTRA-20261007`, authorized by Nolan's subsequent six-role delegation. Single serial compiler ownership; historical providers remain read-only.

This route copies the baseline Lake package without replacing its library registrations, overlays additive G6 sources, reconstructs their custom import closure, obtains the exact Mathlib imported-object cache, and elaborates each custom source serially with `--trust=0 -j1 -M4096`. Each command has a 180-second limit; the remote job has a 15-minute cap and shares `g567-pinned-lean` concurrency with G5. No aggregate library or complete corpus PASS is implied by selected targets.

Pinned Lean is 4.33.1 / commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; official Linux archive SHA256 is `890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`. Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. Exact dependency manifest and baseline Lake registration hashes are retained for new runs.

The new four-target frozen inventory at `89dffaa83c107c21922305474f272b4469d828c7` comprises 61 custom source modules and 42 external Mathlib roots. Its per-declaration audit enumerates all 51 declarations in the four selected G6 modules and asks Lean for their transitive axiom sets. The allowed foundational axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; missing reports and other axioms fail the route. Imported cache objects are reuse, not a fresh complete Mathlib dependency rebuild.

The scientific scope is unranked endpoint genealogy/population/register state and deterministic joint endpoint readouts of that carrier. Physical finite-calendar observation lifting, original event/bin history, effective rational coefficient/tail algorithms, positive biological replacement, RAW NONPLANAR source admission, and the remaining master obligations are separate. A conditional PMF constructor does not itself solve them.

| Exact run | Frozen input | Actual result |
|---|---|---|
| [37649710743](https://github.com/Sodelin/Research-Commons/actions/runs/37649710743) | `967919f7499743f7ccc19b0aa633bb77698ffa9e` | FAILURE in FiniteProbability `pmf_sum_real`; original failed log remains in parent packet. |
| [37650180952](https://github.com/Sodelin/Research-Commons/actions/runs/37650180952) | `63daba9b4fcdde8fb2eb8d52645c870f0f3b5a1f` | FiniteProbability PASS, then Conditioning FAILURE; [full evidence](evidence/g6-run-37650180952-FAILED/README.md). |
| [37651501035](https://github.com/Sodelin/Research-Commons/actions/runs/37651501035) | `89dffaa83c107c21922305474f272b4469d828c7` | First three G6 modules/source bridge PASS; ProgramPrefix FAILURE; [full evidence](evidence/g6-run-37651501035-FAILED/README.md). |
| [G5 37650073193](https://github.com/Sodelin/Research-Commons/actions/runs/37650073193) | `a5a80af1dedc53ff060f8d521b50596851261cd4` | CANCELLED; runtime passed, new analytic/G2 consumer suite has no PASS; [observed evidence](evidence/g5-run-37650073193-CANCELLED/README.md). |

Actual Commands, full stdout/stderr, exit status, timestamps, exact input hashes, tool identities and transitive reports are emitted into workflow logs and uploaded as artifacts on both success and failure. Local Azure cache/artifact downloads encountered HTTP 403; workflow logs are recoverable through the GitHub API. Signed URLs are not retained.

All four reused actual provider blobs match the assignment: UniformizedSourceStep `db19b3ea720bd26b0ccad5deffadf7ca9f3c7fdb`; SourcePoissonKernel `a0039a3a8b99897151971a843714ada7812aa581`; SourcePoissonExponential `3d6756f3f6f672bf9c221f5996b9c4937c5f6fe2`; SourceProgramTransport `1dcf63e697aa449eaa90d9a739e1b8ebf6173b79`.

Next action: recover the current terminal receipt, correct any genuine elaboration failures, then rerun the exact changed source serially. Continue mathematical source-to-master obligations after component PASS. Master status remains IN PROGRESS.
