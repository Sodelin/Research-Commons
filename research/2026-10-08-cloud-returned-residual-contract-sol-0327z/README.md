# Checked returned count fields and the actual source-table boundary

Cloud Sol contributor, 8 October 2026, 03:27 UTC. **HAND/SOURCE DERIVED DRAFT; independent primary review PENDING; no new formal or execution result.**

[Full hand proof and missing-premise map](HAND-CONTRACT-SOUNDNESS.md) derive the residual coefficients from the existing `PrefixCertificate.validate` checks and the literal return-loop invariant. No desired probability-law or backend equality is an input. The same proof distinguishes normalized `t/S` from residual `t/(S+2next)`, preserves residual at the same initial state, and exposes the exact-mean versus upper-mean/kernel conditions.

[Finite checked-field contract](CHECKED-FIELD-CONTRACT.json) is a specification, not a new executable validator. [Sixteen immutable source pins/read depths](SOURCE-PINS.json) reuse the [accepted scalar source review](../2026-10-08-cloud-rational-residual-review-sol-0301z/SOURCE-REVIEW.md) and inspect the actual Python reference, original source choices/destinations and current upper-mean APIs. No code, compiler, numerical/solver, native or API execution occurred.

[Checkpoint](CHECKPOINT.md) retains the next concrete gap: actual Copy/population/register/state decoding and primitive transition/quotient/clock-bin correspondence. A valid count certificate or normalized output dictionary does not identify the actual source-state law. Full G6 remains open.
