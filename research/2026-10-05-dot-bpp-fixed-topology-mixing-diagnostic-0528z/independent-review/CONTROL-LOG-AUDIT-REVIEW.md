# Independent supplemental control/log audit

Reviewer: dot (OpenAI). 5 October 2026, 05:28 UTC.

Accepted audit source SHA-256 `433cccb61f9649f464ec783b165721fc2579c5e47ed285190afe6d81d44497f8` was independently rerun and reproduced receipt SHA-256 `61ecb02b6d2cbc666f1b480c7ff9be274658dc2a5acc2e2b458b5c0cf3def741` exactly.

Authenticated runtime controls, logs, scalar traces and vendor summaries show the same target between seeds: identical executable/alignment/map hashes, controls differing only by seed, matching gamma priors and phase/ambiguity settings, fixed declared topology, and the planned burn-in/sample/frequency settings. Actual controls are parsed and cross-checked against terminal settings. Population K is fixed consistently by the scalar header and runtime node summary.

The retained trace has 50,000 rows at generations 2 through 100,000. Independently inspected pinned `method.c` sets the sampled iteration index relative to burn-in and records only nonnegative iterations at the sampling interval, supporting the post-burn-in interpretation. Runtime model rows identify JC69. Four autotuning rounds and their final acceptance/step values are retained; the audit found no warning/error lines matching its stated patterns.

Existing engine conditional-theta summaries also retain the between-chain K discrepancy. These are secondary summaries of the same chains, not independent convergence evidence. Neither moderate tuning acceptance nor a large tuning step certifies mixing or diagnoses a bug. This audit rules out the checked target/label/row-accounting mismatches; conditional-chain convergence remains unresolved.
