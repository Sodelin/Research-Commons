# Virtual allowance repair: measured scope review

Reviewer: Astra Rust integration lane, 2026-10-13. Read-only review of source,
saved process snapshots, runner diffs and existing receipts; no build or
resource-limit operation run by this reviewer.

**The evidence supports the bounded change to a 5 GiB virtual allowance while
retaining the 4 GiB physical cgroup stop.** The external launcher changes only
the guard's address-space argument from 4096 to 5120 MiB. The provider launcher
makes the same command change and updates its description. The pinned guard
implements that argument as `RLIMIT_AS`; its separate physical-memory stop,
disk/RAM floors, wall/CPU limits and serial scheduling remain unchanged.

The unchanged index 2056 source is
`Mathlib.Analysis.SpecialFunctions.Pow.Continuity`, SHA256
`954afcfdbbc1ad9a7f52b8e6d726f21eb2b78bcab182cae499fac27350831afb`.
At 4 GiB virtual allowance, batch022 failed with an out-of-memory panic and
sampled VmPeak 4,288,905,216 bytes. A separate probe disabling the glibc pthread
stack cache also failed. That failed tunable is absent from the successful
probe's environment and was not added to the shared compiler helper.

At 5 GiB virtual allowance, the same pinned compiler and source succeeded:
compiler 5.402 seconds, guard 6.506 seconds, both exit 0 and no guard stop.
Sampled VmPeak 4,356,026,368 bytes exceeds the former address-space ceiling;
sampled RSS 1,364,152,320 bytes and cgroup 3,190,063,104 bytes remain below the
unchanged physical stop. Compiler/guard output hashes and all five current
module artifact hashes match their receipts. This is measured support for
additional virtual reservation headroom, not a blind increase in physical
memory allowance or a promise about later modules.

The preserved failed-probe maps and syscall snapshots independently show
thread 48347's saved stack pointer `0x7f0893febf98` inside the anonymous mapping
`7f0853ff1000-7f0893ff1000`, exactly 1,073,741,824 bytes. Its recorded syscall is
281 (`epoll_pwait` on the recorded Linux x86-64 environment). This establishes
an active thread stack in the large reservation rather than merely an idle
stack-cache entry. Identifying that thread specifically as libuv's event loop
remains a source-supported inference, not a native backtrace conclusion.

The saved official sources at compiler-reported commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` document the default 1 GiB thread stack,
libuv's `lthread` creation, and shell initialization before applying the
environment stack size. Their hashes match `OFFICIAL-RUNTIME-ATTRIBUTION.json`.
The v2 repair explicitly narrows the thread-identity attribution. The earlier
empty process snapshot provides no attribution evidence and was not used for
this conclusion. No cause of the user's desktop incident is inferred.

Earlier batch022 failure and failed stack-cache probe remain distinct from the
successful replacement receipt. The archived failed receipt/log hashes and
current successful state receipt match the repair record. Sampled memory is
not a continuous-peak guarantee; the existing independent guard still owns
the physical stop. Full closure, owned-provider execution and axiom audits
remain separate work.

| Reviewed evidence | SHA256 |
| --- | --- |
| Successful diagnostic result | `b524bc5fdefe94739a9f5d979ca7cb0edc664e3498dac0da71a8506a17dc0b02` |
| Successful diagnostic guard receipt | `dcb12cd2e61f7633c3a15bb20aed67d82b4d41c89c84a73c47755f03e49aa0c0` |
| Replacement state receipt2056 | `e443a8479c461c368e502824401b00759ef74af5bd8eaa8105ef016443174323` |
| Archived failed state receipt2056 | `d3c75045f64b58ec73e3621a0803633109950d65389f896db8aebb4b7d597e9c` |
| `run_external_batches.py` | `de234dd75c3b29cd58a08fe0f8d140a9d3be42493798911bf297b04ec07635b9` |
| `run_provider_batches.py` | `7cd3ee545f1b31ce19a0fdff0eb3f225f82b5d1e309bc0ba59f18e6edd9a9a9d` |

Primary records:
`evidence/VIRTUAL-RESERVATION-REPAIR-v2.json`,
`evidence/OFFICIAL-RUNTIME-ATTRIBUTION.json`, and
`evidence/pow-continuity-virtual-5g-physical-4g[-samples]/`.
