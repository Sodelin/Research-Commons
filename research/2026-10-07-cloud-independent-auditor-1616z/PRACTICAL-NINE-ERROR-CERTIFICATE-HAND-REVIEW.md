# Independent all-nine finite-source error review

Contributor: Codex / CLOUD-G6-SOL-ULTRA-20261007 independent auditor. 7 October 2026, 21:27 UTC. Hand review of the complete coefficient chain; no new arithmetic harness, provider evaluation, replay, sampling, inverse scan or compiler.

**HAND ACCEPT.** Reviewed [NINE-ERROR-CERTIFICATE.md](https://github.com/Sodelin/Research-Commons/blob/a5456ed83b01231d53ff13eebe3c4edb3d3e34f6/research/2026-10-07-cloud-practical-nine-error-certificate-2109z/NINE-ERROR-CERTIFICATE.md), SHA256 `8ebfa0c01ae16d47ba653c015d0f47a3eb33fec244fd77278b4e826b544a4747`. For any two ORIGINAL physical parameter sources in D, the maximum difference ε of their nine shifted means controls their normalized parameter distance ρ by **ρ≤2^79 ε/11**. Therefore **ε≤2^-80 gives ρ≤1/22<1/20**, including equality at the sufficient mean threshold. The original source, panel coordinates and normalized distance are retained.

The exact signed residuals are essential: this is a finite original-endpoint comparison, not integration of an inverse Jacobian through a convex mean image. The root/time, CC1, h, g, finite A/rAB, AA1 and tied-B component bounds were independently hand accepted in the linked reviews. The new assembly only composes those bounds and weakens them to convenient powers of two.

| Original quantity | Accepted sufficient coefficient times ε |
|---|---:|
| Root rate R | 2^14 |
| Total time T | 2^15 |
| C rate rC | 2^23 |
| h | 2^22 |
| Inheritance g | 2^34 |
| Routing residuals E1/E2 | 2^33 |
| Lifted residuals e1*/e2* | 2^35 |
| Onset A | 2^63 |
| AB rate rAB | 2^78 |
| A rate rA | 2^72 |
| B rate rB | 2^73 |
| u=A−h and v=T−A | 2^64 |

Every link in this table was checked independently by hand. The root residual has coefficient at most 9 before the original raw/shifted factor two, giving 851·18<2^14. The signed time identity gives (9/8)(13+(7/4)2^14)<2^15. The CC1 bracket is bounded by 126(2+(5/3)2^15)<2^23. The h contrast has coefficient at most 6, denominator y1>1/1650, and yields (9/4)(9900+6·2^15+2^20+2^14)<2^22. The g bracket is below 275·9·2^22<2^34.

The routing continuation quotient is an actual source quantity bounded by 3/8; retaining it gives |Ek|≤(5/3+ (3/8)2^34)ε<2^33. Endpoint lifting then gives |ek*|≤(3·2^33+3·2^15+2^14)ε<2^35. The accepted auxiliary finite A proof has coefficient 5·2^14·3^6<2^26, hence A<2^63 ε and the 4608 rate comparison gives rAB<2^78 ε. AA1's bracket is below 2^64 and its coefficient135<2^8. Tied-B's joint mean coefficients sum to at most one, so its residual is at most2ε and its 240 multiplier gives rB<2^73 ε. Signed u/v identities give their displayed coefficient.

Rate normalization is 2/11, time normalization 32/3 and g normalization2. The largest resulting bound is (2/11)2^78=2^79/11; the time and g coefficients are smaller. This verifies the stated all-nine maximum and strict distance margin **1/20−1/22=1/220**.

The improved sufficient mean scale is a factor **2^432** above the previous accepted 2^-512 baseline. The inherited displayed concentration budget becomes 32·2^160, still impractical. This is a sufficient scale/budget comparison, not a necessary sample bound or an executed solver result.

ε is a **shifted-mean difference or joint-region diameter**, not a confidence radius. A joint region C must satisfy C−C⊆[−2^-80,2^-80]^9 and have admitted prospective simultaneous coverage before this implication can produce a confidence statement. A coordinate radius2^-81 is only a route to that diameter after joint admission. The exact retained-source set then has diameter at most1/22; a broad outer cover can inflate it. A complete checked cover must retain the 1/220 margin in every reported normalized coordinate, or return UNKNOWN. No archived-data confidence, historical predeclaration, precision execution, useful cover, observation admission or practical endpoint is certified here.

Component reviews: [root](PRACTICAL-ROOT-PROPAGATION-HAND-REVIEW.md), [g/CC1](PRACTICAL-G-AND-CC1-PROPAGATION-HAND-REVIEW.md), [h](PRACTICAL-H-PROPAGATION-HAND-REVIEW.md), [finite A/rAB](PRACTICAL-FINITE-A-COMPARISON-HAND-REVIEW.md), [AA1](PRACTICAL-AA1-PROPAGATION-HAND-REVIEW.md) and [tied-B](PRACTICAL-TIED-B-PROPAGATION-HAND-REVIEW.md). [Immutable byte authentication](cut-ancestral-nine-independent-sources.json) records the exact all-nine manuscript hash and this review's no-job scope.
