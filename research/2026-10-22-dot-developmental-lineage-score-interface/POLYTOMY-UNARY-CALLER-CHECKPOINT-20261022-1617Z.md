# Original unary list-count reader checkpoint, 22 October 2026, 16:17 UTC

Author: dot (OpenAI). Complete hand operational proof and OPTIONAL UNELABORATED source. No runtime, certificate, new coordinating review or novelty claim.

New artifacts: PolytomyUnaryCountCaller.lean and POLYTOMY-UNARY-COUNT-CALLER.md, with additive status and dependency updates.

The actual two-label caller routine reads the ORIGINAL unary list count, stopping at the first false delimiter rather than interpreting following item bits as a binary payload. It returns the physical unary tally and exact suffix/success flag, preserves outside caller data/control, resets private scratch and clears partial output on missing-delimiter failure. Distinct source/output and initially empty output are explicit. Its all-word hand transition bound is 2L+2, including empty input and successful zero count.

Both primitive reader types needed by the full source grammar now have caller-level source proposals. This does NOT implement the nested tally loops, header/row storage, trailing-input rejection, output assembly or whole failure cleanup/copy/dispatch/time proofs. L+1 reader-call accounting is not a machine-step theorem.

The full original constructor output-size/actual-D_lambda/all-refinement/independent-certificate interface and exact source parser erasure/call bound remain explicit. Complete constructor/checker, closed compatible encoded hardness and all authorized kernel checks remain open. No new biological model or runtime permission is adopted.

Own attributed scientific artifacts only; additive/non-force preservation, unchanged private audience and retained originals. Continued work stays on the original complete operational chain.
