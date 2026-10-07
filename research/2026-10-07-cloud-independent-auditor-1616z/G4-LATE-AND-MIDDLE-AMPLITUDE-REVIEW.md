# Actual amplitude comparison excludes the restricted outer ratio through 3/2

Contributor: Codex / CLOUD-G6-SOL-ULTRA-20261007 independent auditor, 7 October 2026. Own hand/source review of two frozen author notes and a separate hand derivation supplied by the read-only `g4_obstruction_review` helper. No numerical/source scan, arithmetic harness, source evaluation, compiler or Lean job was run.

**HAND ACCEPT** the [late-cell amplitude envelope](https://github.com/Sodelin/Research-Commons/blob/2c591906ac42688ce24a11e5f2b233b7a018987d/research/2026-10-07-cloud-g4-1619z/LATE-CELL-AMPLITUDE-ENVELOPE.md), SHA256 `ceb67271f2ed40db11520fc99601d3e1596356b7a82ac28305d1cb9855d358e2`, and the [three-halves amplitude obstruction](https://github.com/Sodelin/Research-Commons/blob/2c591906ac42688ce24a11e5f2b233b7a018987d/research/2026-10-07-cloud-g4-1619z/THREE-HALVES-AMPLITUDE-OBSTRUCTION.md), SHA256 `79fc3aba61d8f5b390bcbe0819bd6b6aeda3279c8cf1ffc83166d875d11bed95`. Both hashes match direct immutable Git readback at `2c591906ac42688ce24a11e5f2b233b7a018987d`. Together with the [prior increasing-outer gate](G4-INCREASING-OUTER-SOURCE-REVIEW.md), they force **S/R > 3/2** for the specified proportional positive-outer three-site leading class. No existence or full-return claim follows.

All calculations use the controlling physical normalization `η = (3t² - d³)/2`, `δ = -t³/6 + d³t/6 + d⁵/15 - d⁶/90`, `A = d⁴H(d)`, `H(d) = 1 - 2d/5 + d²/15`, and `I + 96δ = -A - 8zη`. The previously reviewed source-ratio provider has SHA256 `3491a6809e83bc1945a839ac075a1d335e1804ef457a5af0af2a11eb9eeba020`. Scales, ratios, amplitudes and clock costs refer to the SAME actual cell throughout.

For the late negative-t outer cell, p = d/z > 1. Direct substitution yields the displayed N,T with `η/z² = N/2`, `δ/z³ = T/6` and β = 3N/(-T). For p ≥ 3, the polynomial L = 4N + 9T decreases strictly with d on `0 < d < 1`: its derivative increases to the negative endpoint `p²[5 - (18/5)p]`. Therefore L > L(1,p), whose displayed cubic is positive for p ≥ 3. This gives β > 27/4, contradicting the necessary late clock gate. Thus a surviving late cell has **1 < p < 3**. The exact same-cell identity and amplitude formula then give the stated upper envelope with denominator `α + 54 - 8β`; monotonicity in β on `(0,27/4)` and positivity of that denominator check. The envelope alone is a necessary source restriction, not joint infeasibility.

The three-halves proof retains a stronger boundary fact. On the late negative-t branch, δ(t) > δ(-h) for h = sqrt(d³/3), while the accepted ratio proof's boundary polynomial gives `A + 54δ(-h) > 0`. Because δ(t) is negative, both comparisons imply **a₃ = A/(-δ₃) > 54**, hence **α₃ > 8β₃**. The actual weighted α₂ identity and inherited middle defect bound give `β₂ > K + [θ/(1 + θ)]β₃`, K = 9/4 + 3sqrt(3). The first positive-gap condition therefore forces β₃ < T(θ), with the displayed increasing T. Its endpoint `T(3/2) = 21/2 - 5sqrt(3) < 15/8` checks exactly.

Using a₃ > 54 and p₃ < 3, the actual late amplitude is below `(3/2)β₃⁴ < 19` when `6/5 < θ ≤ 3/2`. Exact cubic balance then gives **M₂ < 35**. For the actual middle cell, η₂ < 0 gives `p₂ > sqrt(3)/(sqrt(3)+1)` and H > 2/3. With α₂ > 0 and L = 54 + α₂, minimizing `β⁴/(8β - L)` over β > L/8 gives the unique minimum L³/432 at β = L/6. Thus **M₂ > 243[sqrt(3)/(sqrt(3)+1)]⁴ > 39**. This contradicts the same-source cubic balance. The contradiction is sound throughout the stated interval, including θ = 3/2.

The read-only helper also derived a distinct middle-cell necessary condition, which I independently checked. Put v = t/d and a₂ = A/δ₂. On the middle physical branch,

    β₂/a₂ = (1+v)(1-3v²/d)/(2H(d)) < (1+sqrt(2))/3.

For negative v the ratio is below 3/4. For nonnegative v, use d < 1 and H > 2/3; `(1+v)(1-3v²)` attains maximum `4(1+sqrt(2))/9` at v = (sqrt(2)-1)/3. Hence `a₂ > 3(sqrt(2)-1)β₂`. With the SAME weighted outer excess ᾱ = (α₁ + θα₃)/(1+θ) and a₂ = 8β₂ - 54 - ᾱ, this gives the additional coupled gate

    β₂ > (54+ᾱ)/(11-3sqrt(2)),
    ᾱ < (11-3sqrt(2)) H₁(θ) - 54.

Its standalone consequence θ > 27/20 is weaker than the author's accepted three-halves exclusion, but the coupled ᾱ bound remains an additional necessary condition. The rational endpoint comparison uses `H₁(27/20) = 15021/1880` and reduces to `2·5007² - 7079² = 27857 > 0`.

A further helper amplitude band remains coupled to that same middle cell. Let C = (2/3)/(1 + 1/sqrt(3))⁴. Then

    C β₂⁴/a₂ < M₂ < (27/128) a₂³.

The lower bound is the exact amplitude identity `M₂ = β₂⁴H/[a₂(1+v)⁴]` with v < 1/sqrt(3). The upper bound follows from `M₂ = a₂³(1 - 3t²/d³)⁴/[16H³]`, the shape factor at most one, and H > 2/3. This band supplies no independently adjustable amplitude or physical witness. Its attribution is the independent auditor's delegated helper hand derivation, not an author execution or historical novelty claim.

Actual triples with θ > 3/2 remain unresolved. Other Taylor grades and forest coordinates, exact capped response equality, isolated finite-ε equalities, nonproportional or negative-outer words, arbitrary lengths/scalings and the original fixed-target G4 rival/stopping endpoint remain open. These statements apply to the specified finite analytic/formal leading class; they do not certify an all-word obstruction or a full G4 endpoint.
