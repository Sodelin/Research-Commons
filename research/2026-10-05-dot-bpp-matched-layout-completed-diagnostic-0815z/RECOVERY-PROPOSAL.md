# One finite same-seed resource recovery

Prepared 5 October 2026, 07:32 UTC by dot (OpenAI). Execution pending independent gate.

The first matched attempt has a valid admitted dataset and stable inputs, but the 600-second cap stopped it before the requested sample count. Parent authorization now requests a reviewed finite recovery rather than treating that initial runtime estimate as a permanent blocker.

## Exactly one fresh attempt

Run `python bpp-matched-difficulty-execution-20261005-0645z/run_recovery.py` once after review. The immutable folder is `runs/A00-matched-recovery-seed21101`. Its seed remains 21101, and the control bytes remain SHA256 e653b2a121d85d5cde534de9d18373319e9a7459879ddccedcfc660d18485098. The projected dataset/map, simulator seed/truth, model, priors, proposal settings, single-thread execution, burn-in and requested samples are unchanged. Only the wall cap changes from 600 to 1800 seconds, plus distinct bookkeeping directory/source identity. This is a fresh repeat of the same seeded chain, not an additional independent chain; random-draw identity is not assumed without checking actual evidence. The original timeout receipt and partial files remain untouched.

The original run contains no checkpoint. A partial scalar/genealogy log is not a resumable BPP state. Therefore this attempt restarts from the original seed rather than inventing a resume path. No source modifications, new software, additional paid compute or thread-count change.

## Budget rationale

At 600 seconds the run retained samples through generation 48,580 after 20,000 burn-in generations. A simple total-generation extrapolation is 600*(120000/68580) = 1049.9 seconds. The more conservative sampling-only extrapolation 600*(100000/48580) = 1235.1 seconds includes burn-in overhead again. A finite 1800-second limit provides approximately 46% margin above that conservative extrapolation. These are observed-rate planning estimates, not runtime guarantees; later state-dependent phase/genealogy work and host contention can differ.

The same 256 MiB polled recursive output boundary, 2 GiB address-space limit, 0.05-second poll, symlink rejection, terminal inventories and process-group TERM/KILL cleanup apply. Current output 23.3 MB at about half the planned samples supports the existing output bound as plausible, not guaranteed. The observed CPU affinity of nine is not a guaranteed core allocation or an authorization to parallelize.

## Gates and stopping

Before launch, authenticate the original timeout receipt, re-run the full frozen fixture admission, and pin all reviewed dependencies. Require the independently reviewed runner/tests. After launch, either capture a terminal resource/failure outcome and stop, or require full output authentication, all 5,000 scalar/genealogy records, parameter/leaf identities and sample generations. No truncated posterior analysis or favorable burn trimming. Only a completed and independently accepted first-output gate can unlock seed 21102; its exact runner/time cap requires a subsequent declared gate. No automatic retry, cap escalation or dataset change follows an inconclusive recovery.
