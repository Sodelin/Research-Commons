# One bounded detached guard — source-only review draft

Status: **NOT EXECUTED**. No compiler, native build, production job or test has
been run for this draft. The existing guard and builders are unchanged.

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
verifies the guard has entered its output/cleanup region, and sends **SIGINT to
that guard only**. The frozen guard catches the resulting KeyboardInterrupt,
kills its owned builder process group in `finally`, and writes its actual
interrupted receipt. There is no numeric PID/PGID signalling fallback. Unsupported
pidfds, changed boot identity, stale identity, missing readiness, or mismatched
pins fail closed. A persisted stop request alone means neither signal delivery
nor completed cleanup; STOP-SENT likewise means only that signal delivery was
requested through the verified pidfd.

This protects against ordinary bootstrap exit or lost tool attachment while the
same environment/processes continue. **It makes no environment-replacement,
machine-restart or persistent-storage guarantee.** Files are fsynced, but no claim
of transactional power-loss durability is made. A crash between spawning and
LAUNCH persistence leaves an intent-only UNKNOWN state requiring manual readback;
the launcher never guesses a PID or retries. The coordinator's sole-compiler
ownership is still required: the read-only no-active check is not a system-wide
lock against another actor launching work simultaneously. `/proc`, pidfds, the
kernel, filesystem, Python runtime, unchanged guard and selected compiler remain
trusted boundaries. Existing outer outcomes042/057/059 remain UNKNOWN.

`test_transport.py` is a separately labelled stdlib dummy-job harness. Proposed
bounded tests cover bootstrap exit persistence, stopped descendant cleanup,
stale starttime refusal, failed-child outcome, requested-stop/child0 refusal,
and unsupported pidfds. They invoke no Lean, Lake, Git or production action.
All dummy source/profiles, launch records, logs and actual guard receipts remain
in a fresh `ASTRA_DETACHED_TEST_EVIDENCE` directory. The source must be reviewed
before the separately guarded test run; passing these cases is not a proof of
universal process or native-code correctness.
