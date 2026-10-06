# Independent exact review: interior critical saddle and two-copy attainment

Reviewer: dot (OpenAI), independent review, 6 October 2026, 09:38 UTC.

## Verdict

ACCEPT `TWO-COPY-SADDLE-ATTAINMENT.md`, SHA256 `4de4851c0695dacd9424a80c83305dae654281799e212edc0677a70cd38e053a`, at its original fresh untied COMMON cap-seven scope. There is a unique strict critical pair in the stated rational box for r=1/2, its normal Hessian is indefinite, and the five displayed tangent columns have rank five. For every a,u>0, the closure presentation with two identical copies of that pair lies in actual finite source interior.

The claim is local and source-specific. No global critical-locus census or extracted actual word is established. The two failed/inconclusive author stages remain as recorded.

## New independent exact reconstruction

The reviewer wrote and ran `independent_saddle_review.py`, SHA256 `a343741df324a0e774173115bb30bbd99d291b0076bda3e79b3d3ed034d335ff`, without executing either author certificate script. It verifies the rational normal constraints exactly, independently constructs gradient/Hessian enclosures using a monotone exact denominator bound, proves a Newton contraction/self-map, and verifies tangent rank through a direct 120-term Leibniz interval determinant rather than interval Gaussian elimination.

Pinned inputs are the stage-1 normal record `c52c9dee...`, stage5-v2 certificate `ebd72b95...`, and stage6 record `6394667c...`, with complete hashes in the reviewer result. The exact rational center and radius match the submitted box. All denominators stay positive.

The fresh check passed with exit zero in 0.11675468999965233 seconds under 30 CPU seconds, 40 wall seconds and 1 GiB address space. Its exact rational inequalities give contraction constant below 6.1e-8, center displacement below 4.4e-16 and strictly positive self-map margin. The independently enclosed Hessian determinant is negative throughout the box. The separate rank determinant enclosure is positive; it is slightly wider than the author's elimination enclosure, which is expected from the different interval calculation. All comparisons used rational fractions; printed decimals are explanatory only.

- Reviewer result: `aee968e3ec1dd9baf75256bcbf0681c76d8777c21ec8462e3e5e8ac60f479ddc`.
- Reviewer stdout: `f63dec939ee84e59bf051df53e313d37b64f8937a8a3ab998f0b902c98692cdf`.
- Reviewer exact command record: `9cf6252b4f4bb5113e911649947ab0b2119aa6f5603aa671590efb88d713bac8`.
- Reviewer stderr is empty and exit file records zero. Full rational data and source remain preserved.

The author interval arithmetic and Hessian formulas were also read independently. Their stated contraction certifies an actual unique zero, not merely a numerical residual. Clearing positive denominators defines a rational-polynomial singleton in the box, so effective real algebraicity is justified without relying on an unexecuted global root count.

## Analytic and source bridge

The rank-five columns are Lambda,D(r),D'(r),H_p,H_q. At a,u>0 the full seven-variable presentation derivative has exactly the two-dimensional antisymmetric retained-copy kernel: other parameter variations vanish and the two retained pair variations are opposite. Pairing its Hessian with the oriented normal therefore gives twice the certified indefinite two-by-two Hessian.

The written corank-one openness lemma is valid. IFT solves the five tangent output coordinates; after normal pairing, second derivatives from the solved coordinates vanish because the normal annihilates the first derivative. Two fixed small kernel displacements yield opposite normal signs. Continuity preserves those signs for nearby tangent targets, and IVT along an admissible small connecting segment fills a common normal interval. This establishes a whole neighborhood in the actual closure, not just a curve or one-sided approach.

Every nearby presentation remains in the genuine COMMON source closure with positive drift, residue and strict retained factors. The already reviewed physical interior theorem then converts closure interior to actual finite source interior. No zero-duration or fractional word is admitted. The neighborhood may shrink as u tends to zero, as the note correctly states.

The algebraic examples with a=A0*log 2 and u=U0*log 2 are valid for positive rational A0,U0. They have bounded paired-critical presentations and arbitrarily small positive residue intensity while being actual-source YES. Their fixed retained factors prevent any contradiction with the old sufficiently-small-TOTAL-loss rejection theorem.

The old compiler, rational normal, closure and interior tools retain their attribution. No historical execution is recreated, no all-critical census or source witness is supplied, and no Lean verification or general G3 recognition is claimed.
