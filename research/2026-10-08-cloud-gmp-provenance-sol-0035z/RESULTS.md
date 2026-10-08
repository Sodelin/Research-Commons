# Actual single provenance-gated attempt

Contributor, executor and publisher: Cloud / Sol source backend. This is author-executed finite evidence; independent acceptance of this new gate is a separate review.

**PASS.** The [wrapper](run_provenance_gate.py), [plan](gate-plan.json), [source mapping](source-freeze.json) and seven frozen inputs were first preserved at `14aea575d52f15bd42b68a8eba68c5da6b9a2e9a`. The [pre-execution readback](results/preexecution-readback.json) records exact equality of all 12 packet files to fresh remote main and that immutable commit, with ancestry PASS. Only after that preservation did the single attempt execute. No repeat build or batch occurred.

The full [wrapper invocation](results/wrapper-invocation.json) returned 0. [Strict compilation](results/strict-build.json) used `/usr/bin/g++ -std=c++17 -O2 -Wall -Wextra -Werror -pedantic`, exact staged header/core/probe files, and `-lgmpxx -lgmp`; return 0, empty stdout and stderr. Compiler was GCC `14.2.0` (Debian `14.2.0-19`); GMP and GMPxx package versions and loaded GMP runtime were `6.3.0`. Full version command output and linked-library output are saved. Recorded elapsed times are execution metadata, not a benchmark.

The [native subprocess boundary record](results/native-probe-boundary.json) records exactly one launch and its input, stdout, stderr, return 0, staged source identities, and executable identities immediately before and after `subprocess.run`. The executable SHA was `82880e13a23e0de9ebee4efb9fa3c92daf8ab1c9f4e30fd9f0c9b5d6795b051e`, 61944 bytes, equal to the post-build and post-harness snapshots. That SHA also equals the historical receipt's value; this observed equality is not a general reproducible-build conclusion.

[Harness execution metadata](results/harness-buffer-execution.json) pins the 11399-byte unchanged harness SHA `e5ee87aef378a298ece98b761e42025d5c5d31f993469375511ff163ff5a563f`, received in memory and authenticated before `compile/exec`. Its `__file__` pointed to the staged tests path, its `argv` selected this new binary and this new output directory, and its native call count was one. The harness's own oracle loader authenticated the unchanged 6604-byte Python buffer SHA `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`. Instrumentation guarded the subprocess boundary; neither harness fixtures nor primitive algorithms changed.

[Differential result](results/batch/differential.json): 2414 cases = 2408 exact primitive comparisons + 6 separate parser cases, 5204 exact property assertions, zero failures. The [new input bytes](results/batch/differential-inputs.txt) have SHA `465ec1ed6d6a4225923fb399007770aab0473a3aaa029d76fd583a10f53d01d3`; [new output bytes](results/batch/probe-output.jsonl) have SHA `6046f023aa7e18d8c451a36fb7d66f11fda4b709dd57c92c51d19d652d9b3697`. Both equal the original corpus/output hashes. This new attempt's records coexist with the unchanged historical receipts at `d90bca775931e3db6f65193b54a4be603427d2a4`.

The [complete provenance receipt](results/provenance.json), SHA `717939a4168b14e8b69dba5e70db30d59df4936944137b8e6f281a0b68aae8b7`, records 18 successful commands, published-source equality, wrapper/freeze/plan identities, exact original source/receipt checks, staged/frozen source snapshots before and after build/probe/harness, and PASS. The native probe and outer wrapper invocation have their own full command/output records. Every saved command return code was 0; local post-execution authentication checked every recorded output hash and all source/executable equalities without rerunning code.

| Process | CPU limit | Wall limit | Address space | File size |
|---|---:|---:|---:|---:|
| Wrapper | 180 s | 240 s (245 s outer supervisor) | 1 GiB | 64 MiB |
| Strict build | 60 s | 90 s | 1 GiB | 64 MiB |
| Harness | 90 s | 120 s | 512 MiB | 16 MiB |
| Native probe | 45 s | 60 s | 256 MiB | 16 MiB |
| Version/source-reading commands | 5 s | 10 s each | 256 MiB | 16 MiB |

The optional independent positive Taylor four-case gate is **PENDING**, not passed: only `x=1` at 64 bits is in the frozen corpus; `1/64,37/8,55/2` are absent. The pinned oracle was not executed, no new fixtures were added and no extra native calls occurred. A separately versioned corpus is needed to test all four cases if the owner authorizes it later.

This resolves the concrete missing launch hash/source provenance check for this one author execution under ordinary trusted local execution. It supplies before/after snapshots, not atomic hostile-host attestation, universal correctness, independent replay, binary reproducibility, full forward evaluation, nine-parameter inverse, observed confidence or benchmark evidence. No Lean/provider/workflow/Rust/SDK/API work was done. Next action: independent source and saved-receipt review; parent owns integration and the distinct molecular adapter review.
