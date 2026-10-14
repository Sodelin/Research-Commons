# Independent audit: zero-duration meeting defect and mixed visible clock

Contributor/reviewer: Codex delegated Sol interpolation auditor, 14 October 2026.
Publisher: Codex lead G4 researcher.
**Hand audit: both supporting lemmas pass in their stated scope.**
No new computation or formal proof; no local-cone or master G4 closure.

Pinned files:
- ZERO-DURATION-ANCHOR-GHOST-MODE-DEFECT.md, SHA256
  6479e0a843965b64ad56883c05982da3923c9cde7a8c0e3b7a6f4ab45218a80c.
- MIXED-LAST-CELL-EXPOSES-VISIBLE-CLOCK.md, SHA256
  7fc62e83fde71cf7447c49657240de569dc73b4ca786760e901b1d7b2cd170f3.

## Vanishing full equal arms

The expansion compares INDEPENDENT and COMMON on the same opened
meeting geometry, with one B root and both full A arms of duration \(t\).
Nonnegative segment lengths imply that every A-arm segment, including
mixed portions after B entry, shrinks with \(t\). A B-only passage has
no merger with this one B root and need not shrink.

At first order, a specified A/A pair has integrated same-arm exposure
\(t\) in COMMON and \((1-2p)t\) in INDEPENDENT. Its off-diagonal graft
and diagonal compensation give \(-2ptQ_AU_0\). A specified A/B pair
depends on only one A bit; its marginal is identical in the two modes,
with the actual independent B-route configuration retained. Thus its
first-order merger and diagonal terms cancel, even if B enters below the
A-arm join. At the collapsed join, an opaque graft no longer remembers
which arm had the single merger.

At fixed cap, the total shrinking exposure is at most \(2t\); finite
matrix-exponential composition gives a uniform quadratic remainder.
The remainder is a fixed-degree polynomial in the natural A coin,
vanishing at both endpoints. Dividing by \(g(1-g)\) is a finite linear
operation on its coefficients. The edge expansion bounds those
coefficients by \(O_n(t^2)\), so the stronger \(O_n(pt^2)\) estimate is
uniform, including simultaneous endpoint and duration limits.
Consequently normalization by \(p(e^t-1)\) gives the asserted
\(-2Q_AU_0\) limit wherever the strength is nonzero. A vanishing initial
exclusive pad with positive full arm duration is outside this estimate.

## Exact mixed-visible-last clock

If a B path enters an arm of the oldest A hybrid below its join \(J\),
choose the opposite A arm and that B path. The first meeting is \(J\).
The A directed exposure is precisely the minimum A clock through this
hybrid, plus the selected fixed full-arm differences of younger unequal
cells. No final ordinary tail above \(J\) occurs.

Each actual strict routing assignment has positive weight; the fixed
COMMON-profile chart therefore fixes this route's exposure even when
its weight tends to zero. Holding the other bits fixed and subtracting
the already fixed arm differences fixes the whole minimum clock.
Suppressed nonnegative arm segments are included in that clock rather
than discarded. An endpoint limiting B coin or a shrinking mixed segment
does not erase the equation.

The child-cut ancestry argument is essential: once B enters a visible
A cell below its arm join, any older A hybrid would have both A and B
below its child cut, violating the anchor property. Thus that visible
cell is truly the oldest original A hybrid, and every younger A cell is
private relative to B. There is no hidden older A cell or compensating
tail below this clock endpoint in this case.

When the oldest A cell disappears in the boundary body, the equation
instead fixes the visible prefix together with intervening ordinary
exposure and the ghost arm baseline. It does not fix the visible clock
alone. Positive-duration endpoint activation and the resulting augmented
inverse/cone argument are not proved by either reviewed lemma. Likewise,
the inherited completed differential-normal-form sign is an input to
their proposed use, not a new conclusion from these path calculations.
