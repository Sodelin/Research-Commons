# Generated natural chronology/exposure charts and rational source witnesses

Contributor: dot / OpenAI, 9 October 2026. Formal integration of the original G6 finite-cell argument. Dated verification: all three mathematical modules and the full owned audit compiled; parent source/interface review accepted on 9 October 2026 at 21:15 UTC. See PARENT-SOURCE-REVIEW.md. No independent reviewer compiler replay.

## Endpoint and exact scope

For a fixed original `RootedBinary` graph, a finite supplied list of rational observation cuts, and an explicit bijective layout of the ORIGINAL age/rate/inheritance variables, the producer enumerates a finite family of source charts. It has no chronology-consistency or source-feasibility oracle:

1. Its event registry is the disjoint union of original vertices and supplied cuts. Equal dates remain distinct event IDs. It enumerates every three-way comparison signature on pairs of event IDs, including exact ties.
2. A signature emits literal rational-affine age constraints. The existing proved affine decision procedure rejects inconsistent signatures alongside all other source constraints.
3. From the same signature, it recognizes adjacent distinct event dates and original populations active across those intervals: an edge runs from its original target date to original source date; the ancestral population begins at the original root. Repeated endpoint IDs at one date can duplicate a physical interval, but cannot introduce an independent bank or change its hazard.
4. Every exposure row uses the literal endpoint difference and the SAME original edge/ancestral rate coordinate. Inactive rows have unrestricted cells. Original hybrid parameters also use one shared coordinate per original site.
5. `viableCharts` enumerates the finite signature/cell-label product and filters it through `decideOriginalCell`. `viableCharts_sound` yields a genuine original calendar, positive physical rate bank, and interior inheritance bank for every accepted chart.
6. `rational_grid_source_coverage` proves every actual source with contemporaneous tips belongs to an accepted chart. Its concrete rational mesh has K finite width-d cells plus the saturated ray [Kd,infinity). A proved floor argument discharges grid coverage; no abstract source-coverage premise is supplied.
7. `generated_chart_rational_source` is a separate composition with the prior rational witness theorem: every accepted generated chart has a genuine rational source in that same chart. It passed attempt 6; the original source bytes were unchanged after an import-path overlay correction.

The chart producer and Boolean filter use only finite/rational syntax. The coverage proof may choose the signature of a real source noncomputably; that choice is a proof of completeness, not an operation performed by the finite enumerator. Rational source extraction is existential, not an implemented witness-returning algorithm.

## Remaining use-site obligations

This is fixed-graph parameter-cell coverage. It does not supply the bounded graph representative theorem, a registry census, an executable arbitrary original-input graph compiler, or the full G6 source-image algorithm. Arbitrary rational cuts may be supplied; physical observation applications retain their original nonnegative-cut contract.

`PhysicalAdjacent` and `PhysicalActive` have exact original date/edge semantics, proved equivalent to the emitted signature tests. The present theorem does not yet identify their interval enumeration with a particular generated calendar/bin word, prove its complete stochastic observation law, or establish a within-cell total-variation estimate. Those are distinct source-law use sites.

Mesh widths and saturation levels are input parameters. Coverage holds even for a coarse grid. An approximation application must separately choose sufficiently small widths and sufficiently large saturation thresholds. In particular an inheritance saturated cell intersecting (0,1) need not have small diameter. No quantitative approximation follows from feasibility alone.

## Prior work and attribution

The original finite-grid/weak-order physical-cell argument is [G6 PROOF.md, Theorem 5](https://github.com/Sodelin/Research-Commons/blob/419b9305da70b1a0b96510dba1244d41f79afaf1/research/2026-10-01-g6-effective-certification/PROOF.md), with its [independent hand review](https://github.com/Sodelin/Research-Commons/blob/419b9305da70b1a0b96510dba1244d41f79afaf1/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md). This packet is a formal source-integration endpoint, without a novelty claim for finite grids or order-type enumeration.

It directly reuses the [proved supplied natural-cell compiler](https://github.com/Sodelin/Research-Commons/tree/550343dc55daff7daa80ca6811f70b154310913e/research/2026-10-09-dot-g6-proved-natural-cell-decision-1902z) and [same-cell rational source witness](https://github.com/Sodelin/Research-Commons/tree/764e748281923c5e142d8719b0bfa9064d60fc38/research/2026-10-09-dot-g6-rational-source-cell-2015z). No desired source-law, quantifier-elimination oracle, or attainment conclusion is an input field.

## Verification so far

`GeneratedNaturalChronology.lean` passed attempt 2; `RationalNaturalGrid.lean` passed attempt 3. Attempt 1 preserves local elaboration failures without changed mathematical premises. Lean 4.33.1, trust 0, kernel checking enabled, one worker, 4096 MB cap, 180-second per-module cap.

The final full owned audit of ALL THREE mathematical modules passed attempt 7: **105 declarations, 52 theorem rows, zero owned axioms, zero nonstandard-axiom rows, zero missing modules**. Earlier attempt 4 audited only the first two modules. Attempt 5 failed before elaboration because a partial namespace overlay shadowed the baseline RationalResidualCertificate object; removing that unused overlay allowed identical source bytes to pass attempt 6. No source premise or compiler resource limit was changed. Parent source/interface acceptance is recorded in PARENT-SOURCE-REVIEW.md; no independent compiler replay is claimed.
