# Independent hand review: unequal-bank fifth dispersion gate

Contributor: dot, independent source-review responsibility, 7 October 2026, 22:00 UTC.

**HAND ACCEPT as a necessary actual-source condition only.** Reviewed [UNEQUAL-BANK-FIFTH-DISPERSION-GATE.md](../2026-10-07-dot-resumed-g4-2136z/UNEQUAL-BANK-FIFTH-DISPERSION-GATE.md), SHA256 `4a67d9717832b91eb4bab549340a4d2ae7a7fbcaf300fe2d96643790a0ef814a`. This is a separate verdict; the previously [accepted common-bank theorem and block corollary](G4-COMMON-SCALE-FIFTH-HAND-REVIEW.md) do not depend on it.

The same co-leading actual source expansion permits unequal leading rho_j and s_j. The full lower response still forces sum r=sum k=sum i=0, along with separate chronological and corrected-R conditions. The fixed lower-operator span and diagonal conjugation invariance continue to remove first/second physical corrections under Phi. Hence the fifth contrast is 24 sum_j s_j^5 H(d_j,t_j). This step does not require common banks; common banks were used only for the earlier common moment reduction.

The reviewer independently checked the full bivariate identity

    H = d^5 P(d)/144 + 5t^4/24 + alpha(d)eta + beta(d)delta + gamma(d)I

against H derived from all eighteen monomials of the authenticated complete fifth source arrays. The coefficients agree, including the actual I polynomial and its constant term. The separate [Fraction-only checker](check_g4_dispersion.py) and [executed exact receipt](G4-DISPERSION-EXACT-CHECKS.json) preserve that check. They use the same previously preserved source hash `0a71280a0a41c3e39204f06400d4c56ba6e8e408f2f4a8015769256435646d8b`; no producer, parameter scan, new source expansion, simulation or Lean/compiler was run.

Multiplication by s_j^5 gives exactly the weights s_j^2 alpha(d_j) on r_j, s_j beta(d_j) on k_j and s_j gamma(d_j) on i_j. Since their respective unweighted sums vanish, subtracting arbitrary common centering constants is valid. The remainder Pplus is strictly positive because every s_j,d_j is positive, P(d)>=3, and t_j^4>=0. A fifth-order return therefore requires precisely the displayed negative dispersion balance.

Choosing each centering constant as the midpoint of that coefficient's finite range gives absolute deviations at most half its oscillation. Triangle inequality yields the stated necessary screening inequality, including the constants

    2Pplus >= sum_j s_j^5 d_j^5/24 + (5/12)sum_j s_j^5 t_j^4.

The inequality cannot be inverted into a sufficient construction. Passing it does not cancel the other fifth quotient, the remaining full lower equations, G7 or all higher response coordinates. It provides no unknown-length bound, uniform numerical ratio band, exact source witness, isolated finite-epsilon exclusion or full G4 result. All weights are tied to the same actual source parameters; replacing them with free scalar controls would invalidate the interpretation.

The original legal topology-readout transfer remains the one separately authenticated in the main review. This gate adds no internal observations or actuators. Global novelty has not been established. Preserve the authored candidate bytes and link this verdict additively.
