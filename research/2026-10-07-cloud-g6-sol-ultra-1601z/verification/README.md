# G6 pinned selected-source verification

Owner: internal Dot-style Lean verification worker under `CLOUD-G6-SOL-ULTRA-20261007`, authorized by Nolan's subsequent six-role delegation. Single serial compiler ownership; historical providers remain read-only.

This route copies the baseline Lake package without replacing its library registrations, overlays additive G6 sources, reconstructs their custom import closure, obtains the exact Mathlib imported-object cache, and elaborates each custom source serially with `--trust=0 -j1 -M4096`. Each command has a 180-second limit; the remote job has a 15-minute cap and shares `g567-pinned-lean` concurrency with G5. No aggregate library or complete corpus PASS is implied by selected targets.

Pinned Lean is 4.33.1 / commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The executable SHA256 is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; official Linux archive SHA256 is `890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235`. Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. Exact dependency manifest and baseline Lake registration hashes are retained for new runs.

The new four-target frozen inventory at `89dffaa83c107c21922305474f272b4469d828c7` comprises 61 custom source modules and 42 external Mathlib roots. Its per-declaration audit enumerates all 51 declarations in the four selected G6 modules and asks Lean for their transitive axiom sets. The allowed foundational axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; missing reports and other axioms fail the route. Imported cache objects are reuse, not a fresh complete Mathlib dependency rebuild.

The expanded frozen inventory at `1eb4b9a7f39f50aa6bc59f2791e82d380764fdf5` has an actual successful receipt from run 37655542723 attempt 2: 65 freshly elaborated custom modules, 46 external Mathlib roots, 67 zero-exit commands and 80 complete standard-only declaration reports. These comprise 64 G6 declarations in five modules, one separately scoped G3 scalar declaration and 15 G5 frozen analytic support declarations. The complete G6 audit now includes serial product-deficit error allocation and the Taylor/actual-source joint TV certificate.

The scientific scope is unranked endpoint genealogy/population/register state and deterministic joint endpoint readouts of that carrier. Physical finite-calendar observation lifting, original event/bin history, effective rational coefficient/tail algorithms, positive biological replacement, RAW NONPLANAR source admission, and the remaining master obligations are separate. A conditional PMF constructor does not itself solve them.

| Exact run | Frozen input | Actual result |
|---|---|---|
| [37649710743](https://github.com/Sodelin/Research-Commons/actions/runs/37649710743) | `967919f7499743f7ccc19b0aa633bb77698ffa9e` | FAILURE in FiniteProbability `pmf_sum_real`; original failed log remains in parent packet. |
| [37650180952](https://github.com/Sodelin/Research-Commons/actions/runs/37650180952) | `63daba9b4fcdde8fb2eb8d52645c870f0f3b5a1f` | FiniteProbability PASS, then Conditioning FAILURE; [full evidence](evidence/g6-run-37650180952-FAILED/README.md). |
| [37651501035](https://github.com/Sodelin/Research-Commons/actions/runs/37651501035) | `89dffaa83c107c21922305474f272b4469d828c7` | First three G6 modules/source bridge PASS; ProgramPrefix FAILURE; [full evidence](evidence/g6-run-37651501035-FAILED/README.md). |
| [37652484086](https://github.com/Sodelin/Research-Commons/actions/runs/37652484086) | `3a45c8287a0b8e2b78281dd172861cfcc2cec532` | All four G6 modules and 51-declaration audit PASS; [full evidence](evidence/g6-run-37652484086-PASS/README.md). |
| [37654465801](https://github.com/Sodelin/Research-Commons/actions/runs/37654465801) | `eac8195827c1f8075f6946fc160634ec440b0d02` | Program error-budget PASS, Taylor HasSum FAILURE, G3 not reached; exact original G5 diagnostic recovered; [evidence](evidence/g6-run-37654465801-FAILED/README.md). |
| [37655542723 attempt 2](https://github.com/Sodelin/Research-Commons/actions/runs/37655542723/attempts/2) | `1eb4b9a7f39f50aa6bc59f2791e82d380764fdf5` | All seven selected targets and all 80 declaration reports PASS (64 G6, 1 G3 scalar, 15 G5 analytic); [full evidence](evidence/g6-run-37655542723-attempt2-PASS/README.md). Attempt 1 startup failure remains separately preserved. |
| [G5 37650073193](https://github.com/Sodelin/Research-Commons/actions/runs/37650073193) | `a5a80af1dedc53ff060f8d521b50596851261cd4` | CANCELLED; runtime passed, new analytic/G2 consumer suite has no PASS; [observed evidence](evidence/g5-run-37650073193-CANCELLED/README.md). |

Actual Commands, full stdout/stderr, exit status, timestamps, exact input hashes, tool identities and transitive reports are emitted into workflow logs and uploaded as artifacts on both success and failure. Local Azure cache/artifact downloads encountered HTTP 403; workflow logs are recoverable through the GitHub API. The runner successfully retrieved the original stopped-G5 artifact and enforced its failed-output hash before printing it. Signed URLs are not retained.

All four reused actual provider blobs match the assignment: UniformizedSourceStep `db19b3ea720bd26b0ccad5deffadf7ca9f3c7fdb`; SourcePoissonKernel `a0039a3a8b99897151971a843714ada7812aa581`; SourcePoissonExponential `3d6756f3f6f672bf9c221f5996b9c4937c5f6fe2`; SourceProgramTransport `1dcf63e697aa449eaa90d9a739e1b8ebf6173b79`.

Next action: continue mathematical source-to-master obligations and inspect the inherited full G5 timed-consumer context under the root takeover, with one agreed frozen serial compiler slot. The actual selected-source program budgets, Taylor/source certificate, G3 scalar and repaired G5 analytic branch now have receipts. Master status remains IN PROGRESS.

The expanded route includes a separately scoped G3 scalar declaration and narrow G5 frozen analytic branch. Per-module declaration inventories and target PASS markers separate these from G6. After a source failure, the already successful selected targets receive their full declaration audit; the overall workflow retains FAILURE. No failed module is imported into the audit.
