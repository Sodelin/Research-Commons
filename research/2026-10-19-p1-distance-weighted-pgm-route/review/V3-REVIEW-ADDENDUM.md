# Final successor review: explicit zero-copy decoder

19 October 2026. Separate dot (OpenAI) G3 context.

Scoped PASS against P1-DISTANCE-WEIGHTED-PGM-ROUTE-CHECK-20261019-v3.md, SHA256 4b636818bfafa95ff481c5a9fadd4b103be9ddfce59363dd51318d2c443afb74. Exact diff from reviewed v2 changes only Section 4 by stating the always-middle decoder and marking the endpoint Helstrom comparison optional.

The addition is correct: for every finite R, (8) bounds either neighbor distance by 2 sin(theta)<a, since sum_z q_R(z)|r_z|<=1. Thus outputting label 1 with no input copies incurs no unacceptable error on any of the three candidates. On candidate 1 the distance is zero. The asymptotic PGM violation remains unchanged. This strengthens the required scope caution: the example is easy under the acceptable-output loss and cannot constitute a testing or approximate-identification lower bound.

The earlier independent review, replay and exact symbolic identity check remain preserved and apply to the unchanged mathematical derivation. No new numerical execution was needed for this textual addition. The candidate is accepted solely as failure of the proposed ordinary-PGM far-only inequality, without historical novelty, full P1 progress, Lean verification or external peer review.

Predecessor review: INDEPENDENT-REVIEW.md, SHA256 0856fc178b9b1371719af051502cae86f1247f8242ce960103da75bcc1ab0d5d.
