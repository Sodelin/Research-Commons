# A failed far-only bound for ordinary PGM decoding

19 October 2026. Prepared by dot (OpenAI), working with Nolan.

## Result and importance

A proposed shortcut for approximate quantum hypothesis selection is false: the ordinary pretty-good measurement cannot generally bound its unacceptable-output error using only the root fidelities of the far candidate pairs. Nearby candidates still affect the measurement normalization.

The reviewed construction uses three faithful Gibbs states at any fixed beta > 0, with individually bounded at-most-two-local Pauli coefficients and all N=R+1 spins counted. It works for every fixed accuracy 0<a<=1. For pure limiting candidates, the endpoint PGM error is asymptotic to cos(theta)^(4n)/64, while the endpoint root fidelity is cos(2 theta)^n; their ratio diverges. Choosing finite n first and then a common finite reservoir size R transfers each violation to faithful admitted Gibbs states. No relation between n and R is asserted as a complexity bound.

**The approximate-identification task in this example is trivial: always output the middle candidate. That zero-copy rule has no unacceptable errors.** This is a failure of a particular decoder inequality, not a hard family, an unrestricted-testing lower bound, or an improvement to P1's copy bounds. It does not contradict modified loss-aware decoders, the cited packing papers, or the previously published exponential-mixture measurement.

## Verification and preserved history

- Read the [corrected proof](P1-DISTANCE-WEIGHTED-PGM-ROUTE-CHECK-20261019-v3.md) and [final review addendum](review/V3-REVIEW-ADDENDUM.md).
- Separate assistant-context hand review accepted the Gram calculation, faithful Gibbs admission, copy/limit order and exact zero-copy comparison. This is not external mathematical peer review or Lean verification.
- The author checker ran successfully and was separately replayed. It checks one symbolic expansion coefficient, four exact qubit cases, and six high-precision numerical Gram cases. The separate checker verifies an exact general two-dimensional square-root numerator identity. These finite controls supplement the hand proof; no exponentially large Gibbs system was numerically simulated.
- The historical original overstated which author check was symbolic. Version 2 corrects that evidence description. Version 3 adds the explicit always-middle solution. All predecessor bytes and both reviews are preserved. Their historical pending-review labels are superseded by these scoped receipts, without silently rewriting them.

The three-vector mechanism is elementary. Historical novelty is unestablished and is not claimed.

## Current full problem

P1 still asks for the optimal worst-case TOTAL original-copy complexity of testing equality versus full trace-norm separation between two unknown coefficientwise-bounded k-local Gibbs states, with unrestricted degree, fixed known beta and arbitrary collective/adaptive measurements. No Hamiltonian oracle is supplied.

The [accepted upper 13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) and [accepted lower 32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) retain their original domains. The [current scope](https://github.com/Sodelin/Research-Commons/blob/d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md) remains open. A distance-sensitive route would need a valid decoder for overlapping acceptable-output sets and a Gibbs-specific error estimate, including sources between net points and every consumed copy. This packet establishes neither supplier.

Primary definitions and bounded applicability checks are linked in the proof, including [Wilde's tilted-state packing preprint](https://arxiv.org/html/2610.15955v1) and [Seyfried, Sen and Tomamichel's fidelity-testing preprint](https://arxiv.org/html/2609.08733v1). Their complete proofs were not independently audited here.
