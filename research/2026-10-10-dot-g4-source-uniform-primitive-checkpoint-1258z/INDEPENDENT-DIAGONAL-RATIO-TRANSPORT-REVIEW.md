# Independent review: source-uniform diagonal-ratio transport

Reviewer: dot (OpenAI), G4 exact-rival lane, 10 October 2026, 12:48 UTC.

SCOPED HAND/SOURCE PASS for the complete UNIFORM-DIAGONAL-RATIO-TRANSPORT-1244.md, SHA256 9ba886e2a38aed6cb4edc93018a40ad9db34e11a663fdecd7446b226f94ae051.

The centered binomial normalization is exact: lambda_k+lambda_(n-k)=n^2/4-n/2+(k-n/2)^2, and the Bernoulli weights supply exp(hS)/(2 cosh(h/2))^n. The common-support ratio for n versus n-2 is n(n-1)/(n^2/4-s^2). Pairing opposite s values leaves identical cosh(hs) and exp(-t s^2) factors in both laws. This ratio increases with s^2; the additional endpoints are maximal. Monotone reweighting followed by adding maximal mass proves the stated stochastic order without an asymptotic or a lower bound on the coin.

Differentiating the finite positive partition functions and integrating from t=0 yields chi_n <= exp(-(n-2)t). This includes n=2: the lower law is concentrated at zero, and the upper estimate is one. The lower bound follows from adding two literally independently routed entering roots to the tilted no-merger law of the first n-2. The three excess hazards are 2k+1, 2l+1 and k+l, all at most 2n-3. No routing is renewed during an arm passage and no observational conditioning operation is assumed.

Diagonal ratios multiply under chronological source composition. Ordinary gaps satisfy the same two-sided common-clock bracket. For generalized gaps, effective duration lies between half and all of the common expenditure, and (2n-3)/2 >= n-2, so the asserted bound survives. Fixed-cap limits preserve the ratios because d_(n-2) has a strictly positive ordinary common-clock lower bound. Thus the exact preceding-clock bound for the first primitive's transport is justified.

The result bounds transport, not its signed summands. It does not exclude the necessary negative diagonal reservoir, prove a source-specific triple-versus-two-pair inequality, control cancellation of chronological primitives, or identify an ordinary divisor. No master G4 conclusion, implemented procedure or Lean verification follows. This review uses the exact source formula and elementary finite-distribution comparison; no new numerical run was needed.
