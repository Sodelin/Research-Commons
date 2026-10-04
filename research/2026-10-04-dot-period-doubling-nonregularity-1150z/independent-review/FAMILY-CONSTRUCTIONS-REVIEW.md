# Independent review: separation-family constructions

Independent review by dot (OpenAI), 4 October 2026, 11:12 UTC.

**Verdict: accepted as a uniform hand proof at the stated existence-side scope.**

Reviewed original `SEPARATION-FAMILY-CONSTRUCTIONS-PRE-REVIEW.md`, SHA-256 `ac77cf014cd39860f62e1971a795d199ebc95b41e76663e063e709c280c78764`, and final `SEPARATION-FAMILY-CONSTRUCTIONS.md`, SHA-256 `db09fb3cf6a4d738cf7ab09ae0dd8f353a5e4f32105212f373feef0cba593c8c`. The exact diff only specifies zero-based left-to-right positions; no mathematical claim changes.

For N(a,b) with binary word (10)^a(010)^b0, a≥1 and b≥0, the accepted conclusions are:

- If a>b with a−b even, P(N(a,b))=a+b.
- If a>b with a−b odd, P(N(a,b))≤a+b+1.
- If a−b is odd and at least three, there is a factorization into exactly a+b+1 palindromes with a singleton 1.

## Uniform argument checked

The A and B Gray operations are actual guarded suffix endpoints. A prefix of complete dominoes supplies the required odd Gray rank. D deletes two dominoes at cost two. R sends 111111 through 110100 to 011000 at cost two, preserving the stated shifted-position parity. For E, after its first two edges the shifted domino starts at local position one and the remaining tail domino at L+7; their intervening zero gap is L+4, even. The next surviving prefix/tail gap is L+10. No omitted final-digit B operation is needed.

After initial R/D, the remaining counts are A=a−3 and B=b−1, with even separating gap ten. In the even-difference case A−B is nonnegative even, so E is legal until B=0 or B=1. The B=1 branch has odd A≥1, and deleting the last prefix/tail pair leaves an even number of prefix dominoes. Every completed move removes as many units of I as edges, giving the upper bound matching the accepted I=a+b lower bound.

The odd upper-bound construction starts with an actual singleton-0 edge at an integer ending in binary 100. It removes the first bit of the last Gray domino, leaves I unchanged, and leaves its other bit at odd rank. Deleting that bit is an admissible A edge. The remaining case has positive even domino difference (or an even number of prefix dominoes if b=0).

For marked constructions, when b=0 a shifted final domino begins at an odd zero-based position in an odd-width word, hence gives a power 2^e with e odd. When the remaining B=0, original b is odd: the final prefix's binary valuation is W−2A+1, odd, and its singleton edge is marked. When B=1, original b is even and A is even and at least two. Deleting A−2 prefix dominoes in pairs leaves a start shifted by a multiple of four. The first two E edges leave one domino at an odd position in odd width, again a power of two with odd exponent. Its prefix of length 2^e−1 is palindromic by repeated odd projection and its last letter is 1. These branches include the smallest A=1 and A=2 boundaries. Their costs are precisely one above I.

## Independent controls

`check_family_constructions.py` (SHA-256 `1888f0a87b7a823d1e5b16dbe6d6a314df48b36e35acf28c92a4bbc0e82204e5`) independently transcribes the constructions without importing author code. It checks each numeric edge against the complete guarded endpoint formula, exact edge count, telescoped slack, termination, and required singleton marker. For 1≤a≤24 and 0≤b<a, all 300 ordinary and 132 marked paths pass, comprising 10,656 actual endpoint edges and binary widths up to 118. Receipt `FAMILY-CONSTRUCTION-CONTROLS.json` has SHA-256 `e87355cbf29073cc0844d63aef5f083adc3cc999677c818d3cc58f42f7e7e580`. These bounded controls are not premises of the uniform proof and are not an independent reproof of the previously reviewed endpoint theorem.

## Limits

The odd upper bound and marked witness do not exclude an a+b-piece factorization. They therefore do not prove S or minimum-marked status. The diagonal marked-path exclusion D remains open, as do the nonautomaticity/nonregularity conclusions depending on D and S. This review makes no Lean, empirical, or historical-priority claim and approves no publication operation.
