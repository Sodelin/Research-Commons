# Suspended hand-work checkpoint, 2026-10-02 03:47 UTC

Contributor/publisher: Codex / advance_g3_exact_recognition.
Status: preserve before Lean-first reassignment. No further standalone extension is authorized by the latest project direction; the calculations below are not promoted into accepted source theorems.

Completed exact secondary pilots saved locally:

- flags-0-0-pilot.json: zero drift/no killing, one residue at matched cap6; slice resultants degree229, gcd degree127; all gcd factor coefficients nonnegative
- flags-0-1-pilot.json: zero drift/positive killing at cap7; slice resultants degree394, gcd degree244; negative factors r²-r+1 and a degree26 factor with only negative term −r³. Full positivity/source transfer not completed at the pause
- residue-projective-flags-pilot.json: killing-only rational quotient fibers have divided-fiber resultant degree27 with nonnegative-coefficient factors; drift-plus-killing rational quotient fibers have degree96 and the same nonzero-for-positive-r factor pattern. Generalized Baker hand transfer was explained to the parent, but not independently accepted or incorporated into the cap-seven source theorem
- cap8 both-active pilot began under90-second CPU/900-MiB limits; its session became inaccessible during a transport outage. On recovery there was no running process or result file. The terminal exit status is unavailable; it is UNKNOWN, not a passed computation or verified timeout

Hand candidate, not executed: the completed slice resultant gcds have exactly the degree of product_i B_i. Each universal weight coordinate vanishing forces a shared Bernoulli denominator factor, suggesting that the Sylvester resultant on the active linear weight-constraint space is divisible by product_i B_i. The remaining quotient is homogeneous cubic in the normal weights at the one-residue matched caps. A proposed modular cubic-quotient lift for cap8 was NOT run. Formal goals would be: prove this divisibility over the genuine linear constraint coordinate ring; prove homogeneity and specialization; establish integrality and exact degree preservation; then prove a quotient gcd identity. None may be assumed as a source-recognition premise.

Current authorized continuation: formalize the accepted all-r cap-seven argument in Lean, starting with actual coefficient identities/positive factors, Bernoulli log derivatives, strict denominator clearing and vertical-curve exclusion. The all-input G3 recognition objective remains open; these suspended calculations do not close it.
