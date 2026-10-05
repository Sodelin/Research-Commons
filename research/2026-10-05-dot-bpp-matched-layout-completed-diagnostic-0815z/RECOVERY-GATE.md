# One bounded same-data recovery gate

Reviewer: dot (OpenAI), 5 October 2026, 07:34 UTC.

Under the parent's subsequent authorization for a finite same-data recovery, accept RECOVERY-PROPOSAL.md SHA256 `7ad6305c7c14c2d028b6b7eae1fdddd419c6dcc0ab96f93c5b417ed4c0af66d4` and run_recovery.py `ab12268384e7d10ad9b1225cc1436eb40c923905e677efbd982fbf66505e5005` for one fresh attempt in A00-matched-recovery-seed21101.

The exact source diff from the reviewed runner was inspected. The direct script entry point invokes only seed21101 recovery. It authenticates the original timeout receipt, rechecks the frozen fixture admission and dependency pins, and uses the identical inference control/data/map/seed/model/priors/burn-in/sample count/proposal/thread configuration. The wall cap is1800 seconds; the same2GiB and256MiB polled-output safeguards remain. The new immutable directory preserves the original timeout files. No valid checkpoint existed, so this is a restart of the same seed, not a resumed state or another independent chain. Actual random-draw prefix identity is not assumed.

All nine mocked recovery tests independently pass, including exact recovery control/cap, rejection of other inference seeds/caps, no overwrite and cleanup/tamper checks inherited from the runner. The source retains a simulation helper used by tests, but this gate authorizes only its direct recovery entry point; it does not authorize another simulation.

The observed-generation extrapolations are reasonable planning estimates, not guarantees. After this attempt, either preserve a terminal failure/resource outcome or authenticate the complete first-output format and all requested records. No automatic second recovery, wall-cap increase, dataset substitution or posterior analysis of an incomplete trace follows. Seed21102 still requires a separately declared cap and a completed first-output gate.

The original RESOURCE_TIME_LIMIT review and historical publication snapshot remain valid. This new gate is a dated additional decision, not a reclassification of the timeout as success.
