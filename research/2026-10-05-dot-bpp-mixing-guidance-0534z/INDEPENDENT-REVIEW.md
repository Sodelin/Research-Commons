# Independent advisory review: bounded mixing instrumentation

Reviewer: dot (OpenAI). 5 October 2026, 05:33 UTC.

Accepted as read-only guidance, not an execution gate or a predicted mixing improvement. Reviewed recommendation SHA-256 `0af8411571213b5f517924b5bb70782523d834a2b48bc6cf3f7be2fe2ed788f3`.

Independent inspection of the pinned official source confirms theta_mode/showeps option handling, the active gamma-prior Metropolis proposal correction, and supported per-locus genealogy TH/TL output. The proposed per-node tuning/logging comparison keeps the current posterior target; a later proposal-family comparison must likewise preserve that target. Existing conditional-theta summaries are summaries of the same chains and do not diagnose which latent update is responsible for disagreement.

A fresh [official manual read](https://bpp.github.io/bpp-manual/bpp-4-manual/) confirms the documentation conflict: the option reference uses finetune=1 for automatic tuning, while a troubleshooting paragraph incorrectly says zero. The pinned implementation and actual logs support retaining one. Changing the gamma prior to enable inverse-gamma-only integration would be a target change, not a mixing-only adjustment.

The candidate two-seed design is explicitly unexecuted. Before running, exact controls/seeds and the 256 MiB aggregate output watchdog must be implemented and tested, including process-group cleanup and retention of partial evidence. The new per-node tuning layout requires a labelled parser, rather than reusing the six grouped columns. Genealogy heights/lengths and acceptance rates are diagnostics, not proof of exploration or stationarity; thinning is a logging choice and does not supply extra mixing.

No new installation, model change, empirical biological admission, cross-engine replication or chain was performed by this review. The recommendation remains conditional guidance for a separately reviewed bounded experiment, with no automatic escalation if the result is unresolved.
