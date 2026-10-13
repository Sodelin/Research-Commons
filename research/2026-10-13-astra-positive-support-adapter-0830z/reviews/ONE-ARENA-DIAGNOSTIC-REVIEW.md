# One-arena diagnostic: narrow execution review

Reviewer: Astra Rust integration lane, 2026-10-13. No build or allocator/cache
operation was run by this reviewer.

**The recorded single-module diagnostic succeeded with unchanged source and
the original 4 GiB limits.** The actual result, compiler outputs and separate
guard outputs have matching hashes. Current module artifacts also match the
five hashes recorded by the diagnostic. This supports using the specific
successful invocation as a source-compilation receipt after the explicit state
repair, while retaining all earlier failed invocations.

The selected module is index 1895,
`Mathlib.Analysis.Normed.Operator.LinearIsometry`. Both the current selected
source and the preserved source copy have SHA256
`6566005d3ebe700a953b7bb6bc3f453e735aaf5dc9ca450eaf0c4a6cd65bd052`.
The compiler remains the pinned Lean 4.33.1 binary; the command retains
`-DElab.async=false`, `-j 1` and the same module root/output. The runner sets
`MALLOC_ARENA_MAX=1` only in the child environment. `MIMALLOC_VERBOSE=1` records
allocator diagnostics in the compiler stderr. Neither changes a source body,
theorem hypothesis, axiom allowance, system allocator setting, or guard cap.

The observed configuration combines the one-arena environment with the earlier
readonly input-cache advice. Its success is evidence for that combination;
the run does not independently establish which allocation caused the previous
failure or prove that an isolated setting suffices in other executions.

The compiler exited 0 after 21.297 seconds; the guard exited 0 with `stop=null`.
Guard limits remain 4,294,967,296 bytes each for address space and physical
cgroup stop, with 120-second wall and 90-second CPU ceilings. Recorded sampled
peaks are VmPeak 4,075,548,672 bytes, RSS 1,413,025,792 bytes and
cgroup 3,235,033,088 bytes, with six threads. Cgroup OOM counters stayed zero.
These are sampled observations, not guarantees for later modules.

The input inventory hash is unchanged from the independently checked earlier
probe: `fbbd67453592aeabf9354e304d8546fc08e5387450895f8fc66c674f3ee8184d`.
It excludes the active output family. The recording fix is present in both
source and actual samples: an `INPUT_CACHE_ADVICE_BEGIN` marker is flushed
before the sweep, followed by its completion data. The recorded sweep lasted
1.845 seconds and reduced observed cgroup memory from 3,235,033,088 to
2,898,489,344 bytes. Sampling still pauses during the sweep, while the separate
guard continues its own checks.

| Reviewed source or receipt | SHA256 |
| --- | --- |
| `diagnose_module.py` | `3627516934fff41a8f3e431dac8a0ac09a8aeff2c4f42ba82609e487d213e6e2` |
| `evidence/linear-isometry-one-arena-samples-4g/INVOCATION.json` | `2e92c7e0fd869810460ceba05839dc3033ee128e550b8aaa0c582679bcea5ad4` |
| `evidence/linear-isometry-one-arena-samples-4g/RESULT.json` | `a662d78029ae1456ae92231d4be03725d5250bec3c6af05d1f77d9f516d6ef07` |
| `evidence/linear-isometry-one-arena-4g/RECEIPT.json` | `3184f95455b56785413126ca971243cb0664f6a25f5e46c6de237af96c90461c` |

This review establishes neither full external-closure completion nor the
accepted-provider/adapter build. It does not review a future shared subprocess
helper: that runner's selection, reuse, output exclusion and evidence contract
must be checked separately when its exact source is available.
