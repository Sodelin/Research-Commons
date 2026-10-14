# Static review of the local physical-rate splice proposal

Reviewed proposed packet manifest `c876e0756b32d131601d82a0a660a2e1aa694798373cada2c90fe350db554e3c` and complete `Astra/PhysicalSpliceRates.lean` source `2bdd1ea9a4acae8f6e674446a47ad6c5c30ceefedb8c20ed9cf69887c9e59842` (7,142 bytes). No concrete blocking mathematical or API mismatch was found by source inspection. This is **not compilation or acceptance**.

The two complete selected provider bodies were read and their source-store bytes matched their materialized copies:

- `G1SplicedSourceAdmission`: `d55602e4b4fb06c2006a8b0df94d1ea798500c5c75ab09127b5c27d23bff7ac9` (5,499 bytes).
- `G7OriginalSurvivalCoverage`: `59314f77f7c450321a8683bc938b6372e2c1450b6eb8b2d179a99ed696f362e9` (7,614 bytes).

The inherited `G1BigonSpliceGraph` source (`a2274c7d32f068322449a4fbf0848ffe16fc54cfc35e55cab3e99d0d40a79e05`, 9,446 bytes) was additionally read to check definitional endpoints and retained-edge projections. The proposed entry source is `6ffa67e472aad241e409e09072c248b3a3bfd224e3c753425f3560ea1f5db4ff`; its Lake supplement remains unselected and unexecuted.

The scalar construction is coherent with these exact interfaces:

- The denominator is the original calendar age of `source entry` minus that of `target child`. Its strict positivity follows the same entry → parent0 → child chain used in the existing `splicedCalendar` proof. It is not an independently chosen duration.
- Each original whole-edge exposure is positive. Their entry/parent0/child sum is positive, so dividing by the actual positive endpoint span supplies a positive rate for the synthetic edge.
- Retained edge rates and the ancestral rate are literal original values. The selected graph/calendar definitions make the retained exposure and new endpoint-span equalities definitionally plausible; the new exposure identity is the selected quotient-cancellation identity.
- Expanding the selected `survival = exp(-exposure)` definition gives the proposed entry/parent0/child survival product. Reordering the resulting real factors is legitimate.
- The either-arm conclusion explicitly assumes equality of the original arm exposures, retains false→parent0 and true→parent1 order, and identifies the same scalar. The construction without that premise still assigns positive rates but claims no original probability-law preservation.

The proposed code contains no desired forest-law, unknown target, bounded representative, or native result premise. Its original bigon extraction, nonroot condition and cut-child requirements remain explicit where the selected graph constructor requires them. No axiom, `sorry` or `admit` was introduced in the inspected proposal. This lexical observation is not a kernel axiom audit.

The older G1 provider explicitly labels its inserted edge source-derived/decorated and proves no scalar demographic law equality. Adding a positive scalar rate here does not silently strengthen that provider. This proposal still lacks registry/common-bank transport, selected-clade and exposure-sum preservation, joint-mask/PMF and protected-ID transport, outer admission, repeated finite reduction and the certificate-to-bounded-representative consequence. None of those follows solely from one edge's exposure product.

No provider, draft, selection or build configuration was edited by this review. No research module was imported or executed; no compiler, import query, test, materializer, native execution or object scan ran. Actual elaboration, namespace selection, explicit theorem-type/axiom output and Lake execution remain required. Preserve the current draft and any future failed execution before a repair; no source repair is requested from this static review.

Review by the Rust integration lane, separate from the author of this new proposal. This is an internal source review, not external certification or a from-scratch dependency audit.
