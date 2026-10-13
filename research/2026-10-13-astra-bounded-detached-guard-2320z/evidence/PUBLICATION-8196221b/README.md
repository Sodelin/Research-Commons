# One bounded detached guard — tested transport, unexecuted production profile

Status: **seven bounded stdlib dummy tests passed; production NOT EXECUTED**.
No compiler or native build was run for this packet. The existing guard and
builders are unchanged. Historical DRAFT-PINS files and preserved draft copies
retain their literal pre-execution status.

`one_guard.py` exposes only `launch`, `status`, `stop`, and `finish` for the
reserved external batch062, index2992, one fresh module. It rejects arbitrary
commands, paths, PIDs, batch sizes and resource changes. The Lean lane retains
compiler/publication ownership; actual launch requires its quiet-boundary
handoff. If that reservation changes, this source requires a reviewed successor.

The exact command is authenticated from successful ORCHESTRATOR-060 and changes
only its output directory. It directly starts the frozen guard in a new session,
with regular-file stdout/stderr and `/dev/null` stdin. No detached orchestrator,
automatic next batch, restart or retry exists. The child guard retains 900s wall,
600s CPU, 6GiB virtual address space, 4GiB physical cgroup stop, 1GiB file cap,
8GiB disk floor and 1GiB available-RAM floor. The launcher's small bootstrap is
outside that guard; the expensive builder and its compiler remain inside it.

Before Popen, exclusive launch storage contains a fsynced prebatch inventory and
intent with source/toolchain/plan/command/limit pins. LAUNCH then records Linux
boot ID, PID, starttime ticks, actual executable, argv, process group and session.
The guard receives a documented small environment (`PATH`, C.UTF-8 locale,
`PYTHONDONTWRITEBYTECODE=1`), without inherited Python import overrides or private
environment values. The pinned builder sets its existing Lean/allocator policy.

Launch records **LAUNCHED_OUTCOME_UNKNOWN**. Status never certifies completion.
Finish requires the recorded process to have stopped and checks the actual
guard receipt, command, limits, source hash and output bytes. It preserves the
guard's literal builder exit; a nonparent observer does not invent a guard
process exit code. Only actual child0/no stop/no error/no requested stop permits
the successful finish path, which then checks the one-module capture. Ordinary
capture reuses the exact reviewed `capture_batch.py`. A guard exception or stop
request instead preserves all changed indexed receipt/log bytes as explicitly
unverified; this handles the child0/KeyboardInterrupt timing race without
rewriting a historical guard receipt or inventing compiler completion.

Stop opens a Linux pidfd, rechecks the complete recorded live process identity,
requires `/proc/PID/wchan` to be exactly `hrtimer_nanosleep`, rechecks identity,
and sends **SIGINT to that guard only**. In the pinned guard its only monitor
sleep follows successful Popen assignment; reaching it establishes the child
handle exists, and the guard never starts another child. Output-file existence
alone does not establish this: SIGINT during Popen before assignment could leave
`child=None` and bypass cleanup. Unavailable or different wait channels refuse
the stop request rather than signal during that window. This relies on the
pinned Python control flow and the kernel's wait-channel observation interface.
The frozen guard catches the resulting KeyboardInterrupt,
kills its owned builder process group in `finally`, and writes its actual
interrupted receipt. There is no numeric PID/PGID signalling fallback. Unsupported
pidfds, changed boot identity, stale identity, missing readiness, or mismatched
pins fail closed. A persisted stop request alone means neither signal delivery
nor completed cleanup; STOP-SENT likewise means only that signal delivery was
requested through the verified pidfd.

This is intended to survive ordinary bootstrap exit or lost tool attachment if
the runtime leaves the independent session running. It does not override a
tool server's process-cleanup policy. **It makes no environment-replacement,
machine-restart or persistent-storage guarantee.** Files are fsynced, but no claim
of transactional power-loss durability is made. A crash between spawning and
LAUNCH persistence leaves an intent-only UNKNOWN state requiring manual readback;
the launcher never guesses a PID or retries. The coordinator's sole-compiler
ownership is still required: the read-only no-active check is not a system-wide
lock against another actor launching work simultaneously. `/proc`, pidfds, the
kernel, filesystem, Python runtime, unchanged guard and selected compiler remain
trusted boundaries. Existing outer outcomes042/057/059 remain UNKNOWN.

`test_transport.py` is a separately labelled stdlib dummy-job harness. Executed
bounded tests cover bootstrap exit persistence, stopped descendant cleanup,
stale starttime refusal, pre-monitor readiness refusal, failed-child outcome,
requested-stop/child0 refusal, and unsupported pidfds. They invoke no Lean,
Lake, Git or production action.
All dummy source/profiles, launch records, logs and actual guard receipts remain
in a fresh `ASTRA_DETACHED_TEST_EVIDENCE` directory. Parent and Lean reviewers
reviewed the source before the single separately guarded run. Passing these
cases is not a proof of universal process or native-code correctness.

Actual outer test guard: `evidence/harness-tests-v1/RECEIPT.json`, SHA256
`a993e69f8a4650970493b02b1c131d171260098a0513791365cd4aca791a8d2f`,
child0/no stop/no error, 2.503546s and 20,185,088 bytes peak child RSS. Limits were
30s wall/20s CPU/256MiB AS/16MiB file and the unchanged 4GiB physical, 8GiB disk,
1GiB RAM controls. Dummy inner guards used 10s/5s/128MiB/4MiB, serially. Six actual
inner guard receipts remain in `evidence/dummy-jobs-v1`; unsupported-pidfd refusal
created no child. Three real SIGINT tests preserve actual KeyboardInterrupt and
child-9 receipts, and actual `hrtimer_nanosleep` readiness observations. The
negative readiness observation and stop-request/child0 race are explicitly
labelled controlled test inputs, not invented kernel observations.

`VERIFICATION.json` records the actual source pins, seven receipts, output hashes,
and no-active-process readback. The detached guards and stopped test descendant
were observed as nonexecuting zombies awaiting the environment's init reaping;
we make no claim to have reaped processes owned by another parent. No further
signals or system settings were used. The test harness uses generic internal
transport profiles for dummy jobs only; the production CLI remains fixed.

The one-module production finish/capture integration has not yet executed. The
owner should publish this packet first, confirm the reserved prefix/output and
quiet compiler lane again, then invoke `python3 -B one_guard.py launch`. Read-only
`status` is separate; `finish` is allowed only after the actual guard receipt
exists and the recorded process has stopped. The owner must independently
authenticate selected module source/log/object hashes before declaring the
production compiler result verified. Launch output alone is never that result.
