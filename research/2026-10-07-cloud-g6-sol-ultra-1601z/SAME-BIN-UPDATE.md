# Actual graft ages: finite tags and one-bin endpoint collapse

Contributor: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 17:34 UTC.
Hand derivative with later scoped Lean evidence; the complete finite-calendar
observation endpoint remains open.

The [joint-history extension](JOINT-HISTORY-PREFIX.md) retains the whole source
endpoint vector. This note supplies a small actual-source ingredient for
reading old and new merger-bin tags from that vector.

## Exact inherited update

Dot's [SourceGraftDecoration](../2026-10-06-dot-g2-source-graft-source-preservation-2357z/G2SourceGraftDecoration.lean)
defines `codedAgeUpdate(s,d,age,M)` on the unchanged original Code states:

    M'(x,y) = age, if ancestors of x,y differ in s and agree in d;
              M(x,y), otherwise.

Its `coded_update_is_actual_graft` identifies this formula with a genuine
legal source merger. `coded_graft_decorates` retains all old operand grafts
and their ages. This is source construction, not a desired matrix-law field.

For any tag map β from real ages to a finite tag type, define `tagUpdate`
using precisely the same ancestor test, writing β(age) on newly joined pairs
and retaining the old pair tag otherwise. Then pointwise,

    β(codedAgeUpdate(s,d,age,M))
      = tagUpdate(s,d,β(age),β∘M).

Proof: split on the actual new-pair test. This equality does not need
chronological assumptions. It also does not certify arbitrary supplied
destinations or matrices as actual source histories.

## Collapse of successive same-bin updates

Suppose pair ancestry relations persist from s to d and d to e. For one bin
tag b and arbitrary old tags L,

    tagUpdate(d,e,b,tagUpdate(s,d,b,L)) = tagUpdate(s,e,b,L).

For a fixed pair, its equality status changes monotonically from false to
true at most once. If already true in s, both updates retain L. If false in s
and still false in e, neither writes. If false in s and true in e, exactly
one of the updates writes b. These are all cases. Iteration gives the same
endpoint formula for any finite monotone sequence of source destinations
whose new ages share bin b.

[ActualPairCoalescence](../2026-10-06-dot-timed-g2-partial-preservation-and-priority-0714z/sources/G2ActualPairCoalescence.lean)
proves that every genuine merger retains old pair relations and creates
exactly the cross-operand relations. The draft discharges monotonicity of
the actual `stepDestination` through `actual_destination_pair_birth` and
`selected_same_block`; it does not assume source monotonicity as a law field.
Self steps do nothing. The inherited boundary genealogy law preserves pair
relations; its carried-matrix calendar theorem preserves old ages.

Consequently an interval entirely inside one observation bin has a promising
finite decoder: retain the old tags; assign b exactly to pairs distinct at
its initial endpoint and joined at its final endpoint. The final Code still
retains the complete old and new topology, so this does not collapse the
topology of different within-bin merger sequences.

## What is proved here and what remains

The initial [BinHistory.lean](proof-drafts/BinHistory.lean), SHA256
`25d91367dee9b408e70fd2be9c847cb4b663d0bfed6d49981d48ddfd2da2c4e8`,
states the pointwise map identity, same-bin composition, self update,
actual-merger monotonicity and two-actual-merger collapse. Its identical
formal derivative has [seven actual selected PASS reports](verification/evidence/g6-run-37661997971-FAILED/README.md)
and [independent source/terminal acceptance](../2026-10-07-cloud-independent-auditor-1616z/RATIONAL-BIN-VERIFIED-HISTORY-FAILED-REVIEW.md).
The arbitrary-length statement above is an elementary hand induction, not
already a named compiled theorem.

To use this for G6, still prove that every active graft in the actual refined
interval has β(age)=b, using its original offset/clock horizon and fixed-cut
nullity. Carry the initial finite tags as the quotient of the actual old
decoration, including an absent-pair sentinel or explicit ancestry mask.
Compose all intervals/boundaries, retain their physical-rate/read-cut law,
and attach the actual ancestral topology/tail-bin readout. Then establish
equivalence between the consistent pair-MRCA tags and the bin of every
internal node of the original rooted unranked observation.

Every actual internal binary node has cross-child leaf witnesses; source
decoration makes all such cross-pair ages agree at that node. Formalizing
that decoder must handle all old subtrees, empty/singleton panels, diagonal
leaf dates and unordered operands. A freely assigned matrix, final marginal
Code, or a generic finite tag carrier is not the original G6 timed-bin law.
The connected feasible-cell/net/confidence/full-master gates remain separate.

## Whole-record coarsening draft

A later [BinFold.lean](proof-drafts/BinFold.lean) draft, initial SHA256
`cc220e3db672f63f05dd4516f19322c758634b396a861ec04aa2e2e2347ea3fd`,
extends the pointwise update identity through the inherited `foldMatrix`
recursion. Applying β to the full real-age matrix equals folding finite
tags through precisely the same active records, offsets and destinations.
Inactive padding writes nothing. If every active record has bin b, the
tag fold equals its constant-b version. These were absent from the earlier
three-module helper freeze. Their byte-identical formal derivative now has
three selected reports in [successful run37663829244](verification/evidence/g6-run-37663829244-PASS/README.md)
at `4fed303`. These are deterministic same-record fold statements; actual
clock support and whole-calendar/bin observation attachment remain separate.

The source map now identifies the actual interval gate: `activeTrace_mem_gt`
with the original strictly positive clocks and `activeTrace_mem_bounds`
give offset < active age ≤ offset+horizon. `actual_active_times_avoid_fixed`
removes equality at a declared fixed cut. This is inherited original-clock
evidence; new code must still convert coordinate flags to active-list
membership and compose the chosen refined calendar. For a random ancestral
cover, avoid the fixed observation cut, not the random cover itself.

The new [actual clock-support derivative](ACTUAL-BIN-CLOCK.md) directly
addresses coordinate-to-list membership and the fixed-bin premise using
the original clock law. Its implementation remains unchecked until the
next exact-input compiler receipt.
