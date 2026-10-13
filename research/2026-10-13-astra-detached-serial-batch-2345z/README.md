# One explicit detached serial batch

Source-only successor to the remotely verified one-module062 pilot. The
predecessor launcher and tested pidfd transport stay byte-exact. This wrapper
adds explicit bounded batch selection while retaining the same frozen guard,
builder, selected3591 graph, toolchain, capture and resource policy.

The compiler owner selects a batch ID, exact contiguous starting receipt index,
and fresh budget from1,16,32,64. The only command differences from the reviewed
one-module profile are the derived output name and serial `--batch` argument.
There is no arbitrary command/path/PID/limit input, automatic next job, retry,
environment restart or parallel compiler. A fresh no-active-process preflight
and exact receipt prefix are required; the builder then authenticates existing
source/log/object bytes. The coordinator remains responsible for compiler-slot
ownership; a read-only process scan is not a global lock.

The first proposed production command is:

```sh
python3 -B one_batch.py launch --batch-id 63 --start-index 2993 --fresh-budget 32
```

Repeat those exact selection arguments with `status`, `stop` or `finish`.
Launch/status remain UNKNOWN. Stop reuses the verified pidfd/monitor-readiness
contract. Finish checks the actual guard receipt and exact contiguous captured
invocations. Guard errors and requested stops preserve changed bytes without
claiming compiler completion. The OS exit of a detached guard is not invented.
Capture authentication is distinct from a later independent object audit.

Limits remain900s wall/600s CPU/6GiB virtual/4GiB physical stop,1GiB file cap,
8GiB disk floor and1GiB available RAM. No environment-replacement survival is
promised. The wrapper must be reviewed before publication and the first real
batch. Its new selection/finish composition is UNEXECUTED at this checkpoint;
the seven predecessor dummy controls and one-module pilot are attributable reuse,
not tests of every possible batch or universal process correctness.
