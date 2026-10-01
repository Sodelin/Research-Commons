# G5 calendar-route assumption check

Dedicated Sol6.1 Lean lane, 2026-10-01. Original Samuel edge-indexed source attribution retained. Pinned baseline: e2502c82ab9a77c00543932f775a71e5374221f7. New code and verification receipts are attributed to this lane.

## Verified substantive source step

An original hybrid's one child edge is unique by its actual out-degree rule. If that edge is the source's required cut edge, its downstream component is exactly its child's directed descendants. Every actual original root-to-tip route to a hybrid descendant crosses this edge; no route to an outside tip can cross it. Strict original edge ages make the active population unique along each route.

Consequently, throughout `age(child) <= t < age(hybrid)`, every original no-merger route to a selected descendant has that exact child edge as its active population. This conclusion is derived from graph/path/calendar premises; the theorem has no calendar-to-Q/S decoder or desired biological conclusion as a field.

## Boundary convention stress test

The accepted G5 review already says to use the state after instantaneous movements, on the older side of a demographic age. This gives the half-open child-edge interval `[age(child), age(hybrid))`. Its youngest endpoint is included, so the first protective grouping time can be attained.

Lean also verifies that the opposite convention `(age(child), age(hybrid)]` need not have a first time: every point of `(0,1]` has a smaller point in that interval. Thus an attained-first-time chronological argument must state its boundary convention explicitly. This confirms a necessary hypothesis already present in the accepted hand proof; it does not discover a new gap or promote full G5 to machine-verified status.

## Actual proof boundary

The successfully compiled module is `program/G5CalendarRoutes.lean`; compiler/axiom/hash receipt and log are in `receipts/`. Every printed result uses only standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. No custom axiom or placeholder is used.

The stochastic no-merger path-law construction, positivity of feasible routes, observable frozen-generator recovery, chronological contraction, displayed quartet/split reconstruction, and the complete G5 theorem remain unformalized. A concrete graph path is not yet a proved stochastic path support theorem.
