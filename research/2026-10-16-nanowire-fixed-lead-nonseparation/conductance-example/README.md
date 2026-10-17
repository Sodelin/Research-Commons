# Reviewed conductance separation for the finite nanowire pair

17 October 2026. Contributor: dot, working with Nolan.

The [preserved candidate](CONDUCTANCE-SEPARATION-CANDIDATE-03.md) has subsequent [independent hand/source review and exact replay acceptance](review/INDEPENDENT-CONDUCTANCE-REVIEW-03.md). Its candidate heading records its original status. A coordinating review additionally checked the gap, thresholds and declared-model scope. These are internal scientific reviews, not journal peer review or a Lean proof.

In the exact rational finite pair, one ideal zero-bias local conductance separates the two devices by more than 1.205 e²/h; the nonlocal conductance gap exceeds 0.787 e²/h. The conservative symmetric readout-error radii are strictly below 0.6025 e²/h locally or 0.3935 e²/h nonlocally. This is a two-device benchmark with fixed leads, grounded condensate, zero temperature and internal dissipation, at B=2 meV. It is not a practical resolution claim or source-class-wide identification guarantee. The 1 eV onsite physical-admission limitation remains.

## Explicit citation correction

Rosdahl et al., Eqs. (3)–(5), are on article page **045421-3**, PDF page **4** including the TU Delft cover (zero-based index 3), not the page stated in the preserved candidate. The formula and current-polarity conversion are unchanged. [Primary PDF](https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf).

## Verification and prior interpretation

The unchanged own-code kernel and controls plus new verifier are supplied with exact results and logs. All 13 arithmetic controls and the conductance verifier passed in construction and independent replay; the result bytes agree. Replay uses the same source, not an independently implemented second numerical method. See [review receipt](review/REPLAY-RECEIPT.json).

The companion [directed novelty comparison](../NOVELTY-COMPARISON-20261017.md) and [scoped review](../NOVELTY-ROOT-REVIEW-RECEIPT-20261017.md) classify the mechanism as established prior work and the contribution as a model-specific microscopic realization and finite benchmark. Historical novelty remains unresolved. No original-paper error, experimental validation or protected-qubit result is established.
