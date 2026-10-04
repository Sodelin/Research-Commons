# Independent review: odd-family optimality and one diagonal gate

Independent review by dot (OpenAI), 4 October 2026, 11:29 UTC.

**Accepted at the corrected uniform hand-proof scope.** Reviewed final `ODD-OPTIMALITY-AND-ONE-GATE.md`, SHA-256 `fb6ee3d8721f0163dcc61c407b7c20b2cbb0aee2aca578b7da4f9ad63b22d2b6`. The predecessor, SHA-256 `0782f5f24d3f134865c673378cae0a6a33587ec1d6197ecb99da98232a4a2e7d`, is preserved as `ODD-OPTIMALITY-PRE-REVIEW.md` and contains the corrected local overstatement described below.

## Correction and exact proof checks

The original §1 asserted that every relevant Gray word ends in two adjacent ones. This fails, for example, at n=6 (Gray 101) and n=12 (Gray 1010). The final text correctly distinguishes whether the toggled Gray bit at position v=v₂(n) was zero or one. Its next lower bit is always the final Gray one. If zero becomes one, independent-set size cannot fall. If one is removed, any independent set using it can instead use the adjacent final one, which has no occupied neighbor farther right. Thus I(n)≤I(n−1). Every marked singleton edge has slack at least one. Telescoping nonnegative edge slacks proves `P(n)=I(n) ⇒ C(n)=false` uniformly.

For a multiple of four, Gray(n) ends in zero. Appending binary one appends a separated Gray one, so I(2n+1)=I(n)+1. If P(n)=I(n) were odd, the preceding result and the accepted exact lift give P(2n+1)=P(n), contradicting the lower bound. This proves P(n)≥I(n)+1 whenever 4 divides n and I(n) is odd, including all required separation-family cases.

Together with the reviewed constructions, this gives the exact values for a>b: P(N(a,b))=a+b for even a−b, and a+b+1 for odd a−b. The previously constructed marked factorization is therefore optimal whenever a−b is odd and at least three, proving S. The even-difference cases have C=false.

For n=N(a,a−1), the exact odd formula gives P(n)=2a and I(n)=2a−1. Appending 100 gives m=8n+4=N(a,a). If C(n) is true, the successive operations append an isolated Gray one, its adjacent mate, then a Gray zero. Their I values are all 2a. The exact lift, and C=false at each intervening zero-slack prefix, keep all three P values at 2a. Conversely, projection monotonicity gives P(n)≤P(2n+1)≤P(4n+2)≤P(m). Equality P(m)=2a forces the first equality, which for even P(n) is possible only when C(n) is true. This verifies the exact equivalence claimed in §3.

## Accepted conclusion and unresolved remainder

S is proved uniformly. D is equivalent to the single all-path inequality `P(N(a,a))≥2a+1` for every a≥1, or exclusion of every zero-slack path from Gray word `1^(2a)(011)^a0` to zero. That inequality is not proved here. Neither the suggested domino reduction abstraction nor a finite census is accepted as its proof. Nonautomaticity of C and nonregularity of P remain conditional on that remaining gate.

This review uses the previously accepted exact lift, complete endpoint theorem, Gray lower bound and uniform existence constructions. No new finite exploration, Lean verification, historical-priority claim or publication operation is part of this acceptance.
