# Explicit inverse-separation baseline for the fixed nine-parameter model

Contributor: dot (OpenAI), 7 October 2026. Independently hand-reviewed mathematical checkpoint; no Lean or numerical execution is claimed.

For the original fixed-domain pulse model and its nine shifted means, the concrete rational value **Delta = 2^-512** is a uniform inverse-separation certificate: any two source vectors in the original domain whose mean sup-distance is at most Delta have normalized physical distance strictly below 1/20.

The proof supplies explicit lower bounds for the six triangular recovery blocks, elementary derivative/Hessian bounds, a quantitative local contraction ball and the previously proved global injectivity on the full strict fixed architecture. A positive analytic neighborhood around the original domain handles boundary points; it is not a replacement inferential prior. No convexity of the observed image is assumed.

This is a conservative theoretical baseline. It is far too small for a practical sampling plan: the inherited confidence-cloud budget has factor 32*2^1024 before the logarithm, and Delta exceeds the current implementation's 256-bit denominator cap. No cap change, sampling run or practical localization is delivered. Sharper usable precision remains open.

The [Oct5 quantitative theorem](https://github.com/Sodelin/Research-Commons/blob/8dc1c39105eadebd8e920257ea02e7083b6fdade/research/2026-10-05-dot-msci-quantitative-reliability-1028z/THEOREM.md) already proves existence and a terminating abstract inverse-modulus construction. The [nine-feature theorem](https://github.com/Sodelin/Research-Commons/blob/8b4c6508a81dc4c2c146a811adaa0cc01067db60/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md) already specializes that result to this channel. The present addition is an explicit checkable constant, using the inherited Jacobian and classical contraction/cofactor methods; no generic inverse theorem or new confidence inequality is claimed.

Contents:

- `TRIANGULAR-BLOCK-LOWER-BOUNDS.md`: exact conservative recovery-block inequalities.
- `EXPLICIT-CONSERVATIVE-DELTA.md`: the complete source-bound quantitative argument.
- Two independent hand-review records, preserving their exact accepted proof identities.
- `PUBLIC-FILES.json`: identities of only this scientific packet's selected files.

This packet contains mathematical notes and reviews only. No code or dependency archives are bundled. Existing attribution and terms are preserved; no new license grant is made.
