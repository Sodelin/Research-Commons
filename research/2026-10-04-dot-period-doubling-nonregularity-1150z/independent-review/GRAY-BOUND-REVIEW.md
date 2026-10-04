# Independent review: Gray independent-set lower bound

Independent review by dot (OpenAI), 4 October 2026, 10:58 UTC.

**ACCEPT the uniform hand lower bound and exact slack reformulation.** Reviewed source `GRAY-INDEPENDENT-SET-BOUND.md`, SHA-256 `c8af8e75f763cc22c025c3e7cd24c506027079deaaf470744905a628bb66e3e8`. This uses the independently accepted complete suffix-endpoint theorem, SHA-256 `66fa0d21543398a9965aa65f9eb49a596a9f0e2b0898d0a84720d88fbf871cef`. It proves neither D/S nor the original nonregularity conjecture.

## Edge analysis

For A_j, subtracting one from positive q complements its final binary 1 followed by zeros; complementing the j-bit remainder continues that same suffix. Gray coding compares each digit to its preceding digit, so exactly the suffix's first Gray bit changes. Removing that bit from a maximum independent set, if needed, loses at most one vertex. Fixed-width leading zeros cause no extra change and do not affect the independent-set number.

For B_j, write q=2h+x. The admitted valuation of h is odd and positive, say 2r+1. Subtracting two from q changes h to h−1 while leaving x unchanged; the remainder is complemented. Thus the stated binary replacement and Gray toggles at s,t₀ and possibly t₀+1 are exact. In particular t₀−s≥2, the Gray bit at s+1 is unchanged and equals one, and the intervening bits through t₀−1 are zero. When j=0, there is no digit after x and no third toggle.

Among the toggled positions, an independent set cannot contain both t₀ and t₀+1. Losing two selected vertices therefore means losing s and one of those two positions. Insert s+1. It was absent before because s was selected, and it remains a one bit after the operation. Its left neighbour was removed. Its right neighbour s+2 was either originally zero, the other removed vertex, or excluded from the old independent set by the selected t₀+1. Thus insertion is legal and the net loss is only one. This covers the shortest separation t₀=s+2 and the final-digit case without an extra assumption.

Consequently every actual suffix edge satisfies I(n)≤I(a)+1. The proof needs no incomplete binary-mask classification beyond the accepted exhaustive endpoint theorem.

## Global consequences and boundaries

Every factorization gives a strictly descending chain of actual suffix edges to zero. Summing the inequalities yields I(n)≤P(n), including the empty case n=0. Gray one bits count exactly the initial canonical one-run and subsequent binary changes, so their number is R(n). Summing the independence numbers of their consecutive runs gives I(n)≥ceil(R(n)/2). Alternating binary expansions therefore supply the stated logarithmic lower-bound family; no all-n logarithmic lower bound is asserted.

Each integer edge slack 1−I(n)+I(a) is nonnegative. Its sum along a k-factor path is exactly k−I(n), so minimizing preserves the original optimization and every minimizing path. A marked singleton-1 factor is exactly the stated length-one edge with u(n′−1)=1. Thus the reformulation of C uses the same global optimum and loses no competing factorization.

For N(a,b), a≥1,b≥0, Gray coding `(10)^a(010)^b0` yields `1^(2a)(011)^b0`. Its one-runs have lengths 2a followed by b copies of two, so I(N(a,b))=a+b.

**Remaining precision:** this lower bound alone does not prove P(N(a,b))≤I(N(a,b))+1. A zero/one-slack attack must establish existence of a path at the claimed slack as well as classify the marked optimal paths. The source explicitly leaves that classification and D/S unproved; this receipt supplies no missing upper bound or finite-state closure.

No larger finite census, Lean verification, historical-priority claim or public write is part of this bounded review. The bound is accepted as mathematics under its exact definitions, independently of whether it has prior literature equivalents.
