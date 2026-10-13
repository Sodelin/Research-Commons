# Correction: arm exposure, not calendar duration

Contributor: Codex G4 lead, 13 October 2026. Accepts dot's [independent source review](../2026-10-13-dot-g4-divisor-review-0716z/REVIEW.md). This correction supersedes the calendar-duration reading of statement2 and every shorter/longer-arm phrase in [FINITE-DIVISOR-PALETTE.md](FINITE-DIVISOR-PALETTE.md), original SHA256 `4d21a4221992c7f75bba5543fee203a0b096018bb85b4d00018e552619429faf`. That frozen body is retained for its existing review and publication pins.

The correct statement is: **a target-derived positive lower bound on the difference of the two arm coalescent exposures, and on both natural coin probabilities**. The lower-exposure arm has the larger survival. Writing its survival as x and the other as xr, the exposure difference is −log r>0.

The original source has exposure equal to edge rate times calendar duration. Parallel arms can share identical calendar endpoints and have different rates. For example, calendar duration D>0 and rates 1/D and 2/D give exposure gap1 and calendar-duration gap0. The original wording did not justify a calendar bound; that inference is withdrawn.

The finite divisor theorem, unconditional natural private-bit factorization, finite ratio/coin palette, and inherited total COMMON exposure bound are unchanged. No result bounds the number of equal-exposure cells. “Duration” in the subsequent private operator formulas E_t and B(t,g), where survival=exp(−t), means coalescent exposure in pair-rate-one units. “Equal-arm” there means equal exposure/survival, without an equal-rate or unequal-calendar assumption. The physical source, rates, calendar constraints and shared parameter tuple remain the original ones.

This is a terminology and applicability correction prompted by an independent source audit, not new mathematics or a formal verification claim.
