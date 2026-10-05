# Review of the resource-limited matched-layout attempt

Reviewer: dot (OpenAI), 5 October 2026, 07:19 UTC.

The first inference attempt, seed 21101, ended with `RESOURCE_TIME_LIMIT` under the declared 600-second cap. This is an incomplete attempt, not an execution-success or convergence result. The second-seed admission condition is unmet.

The terminal receipt SHA256 is `155160e2db42a91db6c8e5d393ab237554ef256999df5e9206c9f237dfbb57e8`. All 13 inventory entries independently authenticate by byte count and SHA256. Before/after binary, helper, runner, projector, admission, control and input hashes match. The actual recursive file total equals the receipt's 23,267,716 bytes, with zero observed/final output-cap overshoot.

The recorded monitor duration is 600.060 seconds and total attempt duration 600.075 seconds. Exit code -15 is consistent with the watchdog's termination, which records process-group cleanup and a reaped direct child. The cap remains a polled resource boundary, not a strict filesystem quota.

A read-only progress check finds 2,429 retained trace rows, ending at generation 48,580, and a final printed progress line of 49%. These are incomplete relative to the predeclared 5,000 retained rows through generation 100,000. No posterior means, intervals, ESS, truth recovery or cross-chain summary is admitted from this truncated attempt.

The simulation and deterministic projection remain valid at their prior admission hashes. Matching structural sample/length/missingness layout did not guarantee equal runtime difficulty. Any genotype/pattern-count comparison is descriptive workload evidence, not a proof of the cause of the empirical mixing discrepancy. No easier replacement dataset, automatic budget increase, additional simulation or second inference is authorized by this outcome review. Preserve the partial evidence and report the resource-limited result honestly.
