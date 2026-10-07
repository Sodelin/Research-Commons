# Actual graft ages: finite tags and one-bin endpoint collapse

Contributor: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 17:34 UTC.
Hand derivative and preserved unchecked Lean draft; not independent acceptance
or a finite-calendar observation endpoint.

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
states/proposes the pointwise map identity, same-bin composition, self update,
actual-merger monotonicity and two-actual-merger collapse. It is **UNCHECKED**;
the Lean owner controls its formal derivative and next frozen compilation.
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
