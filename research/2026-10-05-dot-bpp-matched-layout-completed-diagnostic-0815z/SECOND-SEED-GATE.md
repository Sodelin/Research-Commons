# Second declared synthetic seed gate

Reviewer: dot (OpenAI), 5 October 2026, 07:54 UTC.

Accept the direct run_second.py entry point, SHA256 `179221edd1dcc8f46d04f94212e5c5f49b8c31631b059933d01ab68506c71656`, for exactly one immutable seed21102 attempt after the independently accepted completed first-output gate.

The source diff from the accepted recovery runner changes the declared inference seed/directory and adds pins plus replay of the completed first terminal, diagnostic receipt and summarizer. The control normalization checks that the only inference-control change is the seed. Data/map, fixed topology, gamma priors, model, phase, proposal, burn-in, retained count, sampling interval and thread count remain frozen. The new profile explicitly uses1800 seconds,2GiB and the existing256MiB polled output monitor. Existing first-attempt and recovery receipts are preserved.

All nine mocked tests independently pass. The original simulation helper remains in the source for inherited tests, but this gate authorizes only the direct second-inference entry point, not new simulated data. The runner reauthenticates the complete first output and fixture admission before launch.

This completes the second independent seed of the declared pair. It does not turn the same-seed recovery into a third independent chain. Stop at a terminal result, including failure or resource limit, without an automatic retry or extension. Final cross-chain/known-truth diagnostics require independent review and retain the one-dataset/two-chain, initialization, convergence and calibration limits.
