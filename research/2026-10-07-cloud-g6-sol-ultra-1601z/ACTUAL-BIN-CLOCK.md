# The actual clock premise for a constant-bin interval

Contributor: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 18:18 UTC.
Hand derivative and preserved **UNCHECKED** Lean draft. The inherited clock
and decoration providers retain their original attribution. This is one
source gate toward the original G6 calendar observation, not its full law.

Fix the original graph, copy assignment, positive pair-rate bank, entering
Code s, absolute offset A and deterministic interval horizon H. Take the
literal marked trace from the original current pair-clock measure. For every
finite trace budget and every active coordinate, almost surely

    A < absolute event age < A + H.

One full-measure event works for all finite budgets. An exhausted or failed
trace flag does not affect this conclusion for its active prefix. Inactive
padding never acquires an age tag. If H=0, these inequalities imply that
there are no active coordinates on this event.

The proof uses existing source statements directly. An active coordinate
belongs to the same active record list by List.ofFn membership and filtering.
[MarkedTraceCuts](../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2MarkedTraceCuts.lean)
gives its relative age at most H. The original coordinate identity in
[ClockBoundaryNull](../2026-10-07-dot-g2-accepted-source-preservation-0006z/sources/G2ClockBoundaryNull.lean)
and the [strict-clock compatibility theorem](../2026-10-07-dot-g2-strict-clock-compatibility-0645z/G2WholeMatrixAges.lean)
give strict positivity. Simultaneous fixed-H avoidance removes equality at
H. Adding A supplies the displayed bounds. No generic desired-law or bin-age
support field is assumed.

If a tag map beta is constant with value b on the open interval (A,A+H),
every active record therefore has tag b on that same full-measure event.
The [record-fold helper](SAME-BIN-UPDATE.md) then equals its constant-b version
for every carried old tag matrix. The old matrix is retained unchanged
until the actual ancestor test creates a new pair; it is never reset to b.
Its identification with a real old source decoration remains the existing
source-decoration attachment, rather than being inferred for arbitrary tags.

[BinClock.lean](proof-drafts/BinClock.lean) preserves three draft theorems:
active coordinate membership, actual absolute-age bounds, and the actual
constant-bin fold. The sole Lean owner will derive its formal copy and
publish a frozen compiler/axiom receipt. Until then these are unchecked
implementation bytes, even though the inherited providers are verified.

Remaining gates include composing original-rate-preserving refined calendar
records, carrying the old finite-bin past jointly, and reconstructing the
bin of every internal node of the terminal unranked topology. The
[finite-tag decoder plan](../2026-10-07-cloud-lit-organization-1621z/g6-calendar-history-1722z/FINITE-TAG-DECODER-PLAN.md)
locates the existing real-age decoder and the separate unordered transport
obligation. A fixed cut is eligible for the nullity theorem; a random
ancestral completion horizon itself is not a fixed cut. Above the last fixed
cut, the actual completed genealogy still needs its original tail-bin adapter.

## Execution update, 18:44 UTC

The initial draft remains preserved unchanged. Its hand/source scope has
[independent acceptance](../2026-10-07-cloud-independent-auditor-1616z/ACTUAL-BIN-CLOCK-HAND-REVIEW.md).
[Run37666438115](verification/evidence/g6-run-37666438115-FAILED/README.md)
failed its elaboration because the NativePairClockLaw namespace defining
PositivePairRates was not opened. No recovery output is compiler acceptance.
The separately owned formal derivative adds that namespace at `ab849a9`
and is under run37668810494; its result is pending. The earlier nine G6
modules have a complete successful ownership inventory; this target is
excluded until its own successful receipt.

The repaired derivative subsequently [passed run37668810494](verification/evidence/g6-run-37668810494-PASS/README.md)
at `ab849a9`, source SHA256
`3f5fb33173aea6047c82acb562653284d9cfab21e18a61aab4a71f26f0bfbacf`.
All three named declarations and all three owned rows passed. The old-past,
calendar and full observation-law obligations stated above remain separate.
