# Reuse of the original G1 unranked epoch theorem

Contributor: Codex Rust implementation role, 10 October 2026. Status: sourced
finding and hand-derived proof route. This corrects the outstanding-obligation
wording in [the earlier local quotient argument](SOURCE-POPULATION-ARGUMENT-20261010.md).
The earlier argument and its finite execution evidence remain preserved.

The source PMF's independence of current representatives and child orientation
is already an inherited theorem. It is not a new unsolved mathematical claim
of this Rust port. The remaining obligations concern the native encoding,
reachable finite support and exact polynomial implementation correspondence.

## Exact providers and assumptions

The original complete G1 package supplies:

| Provider | SHA256 | Relevant statement |
|---|---|---|
| [G1UnrankedSourceView](../../2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedSourceView.lean) | `91eb2667a473cb2dc7f1b7c7105baad33f40ec20ab00c3f394dd0dd75a398c92` | `unrankedView` quotients each labelled genealogy by child swaps and retains every original population and the entire original vertex register. |
| [G1UnrankedActualGenerator](../../2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedActualGenerator.lean) | `70f7f49954c09f54d37594ada58a98364c95d1bfc088c5a4e00f68ea8071f909` | `actual_unranked_step_row_independent` gives equality of the actual source-step PMF pushforwards for equal unranked selected views. |
| [G1UnrankedActualEpoch](../../2026-10-04-dot-complete-original-g1-1549z/src/G1UnrankedActualEpoch.lean) | `6c69a4ab1e3957e4162dc078add91a47cffcdc4bb0c1ed7144ec3836e911958c` | `actual_unranked_epoch_row_independent` gives equality of actual `sourceTimeKernel` pushforwards for every nonnegative epoch duration. |

Both row-independence theorems quantify over a supplied original typed
`RootedBinary N`, its sample assignment, actual `Code N sample` values,
positive original pair rates, an arbitrary selected-copy set and equality of
the full unranked selected view. The epoch theorem additionally takes
`t : ℝ≥0`. This is an exact labelled child-swap quotient; it introduces neither
associativity nor a count-only observation. Equal populations and the same
original register are part of the view equality.

The original `selectedView` stores an ancestor's pruned ordered genealogy for
each selected copy, its original copy location and the complete vertex
register. The Rust ordinary forest is a different finite representation:
one canonical tree for each actual live representative. Leaf-fibre partition
and injective label transport must establish the correspondence between those
representations. A mixed-population frontier additionally needs its locations
retained; forgetting them before applying the inherited theorem is invalid.

At 11:21 UTC this role ran the original package's `verify_certificate.py`.
It exited zero with `delivered_byte_certificate:PASS`, 467 exact sources,
467 recorded fresh source targets, a recorded successful separate Lake check
and the recorded full-closure audit. This validates the delivered historical
source/evidence bytes; it is not a fresh Lean kernel rebuild in this session.
See the [original receipt](../../2026-10-04-dot-complete-original-g1-1549z/certificate/fresh/SERIAL-BUILD-RECEIPT.json)
and [package verification scope](../../2026-10-04-dot-complete-original-g1-1549z/README.md).

## Consequence for the remaining proof route

For a source-valid co-located population input, sum the inherited exact
population polynomials over an entire destination fibre of the full unranked
selected view. The inherited `actual_population_coefficients` theorem turns
evaluation of that finite polynomial sum at the physical survival coordinate
into the actual source-time-kernel pushforward probability. The old epoch
row-independence theorem therefore already proves equality of these evaluated
fibre sums whenever the entering full unranked views agree.

A possible coefficient-level transport is then polynomial extensionality:
fix the relevant positive original pair rate to one, and use the infinitely
many distinct survival values `exp(-t)` for nonnegative durations. Equality at
those values implies equality of the rational coefficient polynomials after
the usual embedding into real polynomials. This is a hand-derived proof route,
not a newly accepted Lean theorem. It needs the finite pushforward-sum and
coefficient embedding lemmas, the exact canonical-forest/view correspondence
and an explicit proof of distinct evaluation points.

The actual half-rate recurrence still matters for porting literal rows. Each
ordered merger retains its first representative and ordered graft; the reverse
orientation has a different literal destination. Summing both entire unordered
fibres, rather than multiplying an arbitrary literal destination by two,
remains necessary. Equality of the native ordinary path kernel to the
inherited fibre polynomial also needs the divided-difference recurrence
identity or a separate source-kernel transport.

The current Rust probe has independently checked all literal coefficients and
unordered fibres on eight fixed entering-state fixtures. Its original typed
Lean coefficient extraction is pending. New source-support and canonical
encoding lemmas are saved by the reuse role and await actual integration
checks. None of these local results promotes arbitrary graph source admission,
natural initialization, full-epoch panel reassembly, boundary/hybrid routing,
ancestral completion, physical calendar image, admitted observation semantics
or full statistical recovery. The full intended solver remains in progress.
