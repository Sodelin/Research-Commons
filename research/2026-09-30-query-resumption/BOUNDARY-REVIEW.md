# Independent boundary review: fixed hidden sets and exact sufficient shadows

Contributor: Codex `boundary_review` subagent, BOUNDARY-REVIEW-20260930.
Date: 2026-09-30 UTC. Status: independently checked all-size hand arguments,
sharpened counting constants, and executed finite controls. No Lean certificate,
external peer review, historical novelty claim, or adaptive-master closure.

## 0. Verdict

The baseline/candidate deletion argument in
[adaptive-adversary-hidden-pair-barrier.md](adaptive-adversary-hidden-pair-barrier.md)
is valid for its full stated domain, including candidate tree families that do
not share the baseline's circular order. Its original `n+40k` bound is sound.
The same structural proof supports these sharper bounds:

| Size d of designated hidden set A | Eligible sets, upper bound |
|---|---:|
| 1 | n |
| 2 | n+18k |
| 3 | n+12k |
| 4 | 3k |
| At least 5 | 0 |

Here `n>=5`, the baseline is a nonempty family of binary unrooted phylogenetic
trees sharing a circle C, and k is its number of distinct nontrivial splits.
Eligibility means some different complete quartet-support answer is possible
while every quartet not containing **all** of A retains the baseline answer.

Under the separately inherited source bound `k<=13n-27`, every fixed-baseline
hidden-pair/triple/quartet construction has only O(n) designated sets. This
excludes those particular quadratic or cubic fixed-baseline adversary designs.
It supplies neither an optimal adaptive algorithm nor a lower bound on that
optimum. Moving baselines and more general transcript constructions remain open.

[MINIMAL-PROJECTION.md](MINIMAL-PROJECTION.md) also correctly separates exact
storage, permitted acquisition, and decoding. Its split-gap, distance and
moment identities pass review. The total `Theta(n log n)`-bit source guarantee
is conditional on the inherited linear split count. Its stronger conditional
`Theta(n)`-bit structural code additionally inherits the adjacent-occurrence and
port/composition representation; that codec was not independently implemented.

## 1. Audited structural kernel

If a hidden set contains a taxon x, deleting x gives equal restricted complete
quartet-support tables. The baseline deletion remains circular in C-x. A
candidate split that were noncircular there would yield four alternating taxa
and their crossing quartet, absent from every circular baseline tree. Thus
the candidate deletion is circular as well. The adjacent-boundary quartet
criterion then identifies the same nontrivial split union on both deletions.
For n=5 the deletion still has four taxa, so this argument has no small-order
hole. Restricting a nontrivial full-tree edge split preserves that split if
both restricted sides retain at least two taxa.

Let B consist of circular nontrivial splits obtainable by flipping one taxon's
membership in a baseline split. A circular split has two boundary gaps, and a
flip preserving circularity must involve one of their four incident taxa.
Hence at most 4k such **flip records** exist, and `|B|<=4k`. Different records
can lead to the same split; counting records is a safe upper bound.

A new circular candidate split whose deletion by x is nontrivial must project
to a baseline split. Its only two possible lifts are itself and itself with x
flipped. Since it is new, the latter lift is a baseline split. This justifies
the neighbor conclusion without falsely identifying a restricted split with
one unique full split.

Deleting one taxon removes at most two membership transitions around C. A
noncircular candidate split that becomes circular after deleting x therefore
has exactly four runs, and x must be a singleton run. This handles trivial
restricted splits as well: a nontrivial full split cannot become empty after
one deletion, and a singleton restricted side is circular.

For a nonadjacent hidden pair i,j, both are singleton runs. If they belonged
to opposite split sides, their singleton runs would be adjacent in the
four-run cycle, making i,j adjacent taxa. Therefore they occupy the two runs
of the same side, which is precisely `{i,j}`. The only possible noncircular
candidate split is that cherry split.

For hidden triples, three singleton runs must be three consecutive taxa in C;
there are at most n such sets. For hidden quartets, all four runs would be
singletons and n would be four, contrary to n>=5. Larger hidden sets are
impossible because no queried quartet could contain all their members.

## 2. Refined hidden-pair count

First reserve the n adjacent pairs of C. All remaining pairs are nonadjacent.

If a candidate has the noncircular cherry split `{i,j}`, choose a displayed
binary tree containing it. Let v be the cherry vertex and u its neighbor.
The two other branches at u have nonempty taxon sets P,Q partitioning the
complement of `{i,j}`. Every other nontrivial split of this tree is circular
and lies in `S0 union B`. Each branch set is consequently a circular interval
or a singleton. Since neither contains i or j, each lies in one of the two
open arcs between them. The branches cover the complement, so they equal the
two complete open arcs. Binary degree three is essential to the fact that
there are exactly two branches.

At least one arc P has size two or more, and its complementary side has at
least three taxa. Thus its split S is nontrivial. The pair `{i,j}` is exactly
the two immediate outside neighbors of interval P.

* If S is a baseline split, its two interval sides yield at most two such
  pairs. This accounts for at most 2k pairs.
* If S is new, deleting i preserves nontriviality: P still has at least two
  taxa and its complement still contains j and the other nonempty arc. It
  therefore gives a baseline flip record `(S',i)` for S. Of S's two
  interval-side/outside-neighbor pairs, only the pair for the side excluding
  i can contain i. Each of at most 4k flip records therefore accounts for at
  most one pair. This accounts for at most 4k additional pairs.

The noncircular case therefore costs at most 6k pairs, instead of 10k.

For wholly circular candidates, equal split unions imply equal support, so
choose a changed split S. Its four distinct adjacent-boundary taxa Q_S
witness a changed quartet answer. The hidden pair must be a subset of Q_S.

* A removed split lies in S0. Q_S has six pairs, but its two boundary-gap
  pairs are adjacent and excluded here. At most four nonadjacent pairs per
  removed split give 4k possibilities.
* An added split cannot be the circular cherry `{i,j}` because that pair is
  nonadjacent. Some hidden taxon x has a nontrivial deletion of S and gives
  a baseline flip record `(S',x)`. The flipped taxon is one of Q_S's boundary
  taxa. Among its three other boundary taxa one is its adjacent gap mate,
  so at most two can form a nonadjacent hidden pair with x. At most 4k flip
  records therefore give 8k possibilities.

Combining adjacent, noncircular and wholly circular cases gives

    eligible hidden pairs <= n + 6k + 4k + 8k = n + 18k.

## 3. Refined hidden-triple and hidden-quartet counts

For a hidden triple or quartet, a new nontrivial circular split has a
nontrivial deletion by some hidden taxon: when n>=5 at most two individual
deletions can trivialize one nontrivial split. Thus every such new split
belongs to B. In the wholly circular case, its boundary quartet Q must
contain the designated hidden set.

For each new split S define

    R_S = {x in Q_S : S-x is nontrivial and flip_x(S) belongs to S0}.

Each membership of R_S is a baseline flip record, and therefore

    sum over all new circular S of |R_S| <= 4k.

If an eligible hidden triple A is witnessed by this new S, every member x of
A whose deletion is nontrivial must lie in R_S.

* If both sides of S have at least three taxa, every boundary deletion is
  nontrivial. A must be a three-subset of R_S. For `|R_S|<=4`, the number
  `binomial(|R_S|,3)` is at most `|R_S|`.
* If one side T has exactly two taxa, both members of T are boundary taxa,
  and exactly the other two boundary taxa have nontrivial deletions. If
  `|R_S|` is zero, no triple qualifies; if it is one, only `T union R_S`
  qualifies; if it is two, all four boundary triples may qualify. In every
  case at most `2|R_S|` triples qualify.

Thus new splits account for at most 8k triple sets. Removed baseline splits
give at most four triples each, hence 4k more. The noncircular cases already
gave at most n consecutive triples, proving `n+12k`.

For a hidden quartet, its set must equal the boundary quartet Q_S of a
changed split. There is no noncircular case. Removed baseline splits give
at most k such sets. For an added S, at least two members of Q_S have
nontrivial deletions and must belong to R_S. Thus each qualifying new S
consumes at least two of the at most 4k baseline flip records. It gives
only one quartet set, so at most 2k additional sets qualify. The total
is at most 3k.

These arguments count possible witnesses, allowing duplicates. They do not
require different eligible sets to have different candidate families.

## 4. The O(n) source scale is a real boundary

The count cannot generally be reduced to o(n), even on admitted binary trees.
For every n>=5, take a binary caterpillar. Its two end internal vertices have
two taxon arms each, and all other internal vertices have one. For every
internal path edge select a taxon i attached to one endpoint and a taxon j
attached to the other. Swapping those two labels gives a distinct binary
tree. Deleting i makes the old and swapped positions adjacent degree-two
vertices, which suppress to the same attachment; the same holds deleting j.
Thus every quartet missing i or j agrees, while a quartet selecting i,j and
one taxon from each of the other two nonempty branches changes topology.

These give `2 + (n-5) + 2 = n-1` distinct eligible pairs, including n=5
where the middle term is zero. Consequently the source-linear asymptotic
candidate count is sharp, although the constant 18 above is not claimed
optimal. This cardinality statement is distinct from the query-complexity
master.

For the broader tree-family theorem, k dependence is also necessary. Let F0
contain all binary trees circular in C; its union contains all
`k=n(n-3)/2` circular nontrivial splits. For each nonadjacent pair i,j, take
a tree having their cherry and its remaining two attachment branches equal
to the two open arcs between them, with binary interval refinements. Its
only noncircular split is that cherry. Add this tree to F0. Every changed
quartet contains i,j, and one quartet taking one taxon from each open arc
has a new crossing topology. All k nonadjacent pairs are eligible. This
dense baseline is a general tree-family witness, not claimed source-admitted.

## 5. Review of the exact shadows

The split union regenerates exactly every supported quartet, since a full
tree edge witnesses a resolved induced quartet and any such quartet's central
path contains a full edge. A compatible circle plus gap IDs therefore
preserves full support and all common orders. The inherited `k=O(n)` gives
O(n log n) bits. The admitted binary tree subclass has `(2n-5)!!` distinct
support targets and supplies the matching Omega(n log n) worst-case bit
bound. This is an information/storage result, not a legal-query algorithm.

The distance inverse is exact. Writing membership bits as z_x, one split's
contribution to the four-distance bracket is

    -2 (z_a-z_b)(z_c-z_d).

For adjacent gaps only the split with exactly those two boundaries has both
factors nonzero; its signs are opposite and its contribution is 2. Singleton
terms cancel. This also explains why using the full union's unit split metric
is essential to the claimed binary-coefficient inverse.

The finite-field power sums are exact under `p>M`, binary indicator weights,
and distinct candidate IDs `1,...,M`. The zeroth sum identifies k without
wraparound. Since `k<p`, Newton denominators are invertible; its monic
polynomial has precisely the selected distinct IDs as roots. No floating-point
precision, probability of collision, or continuous injectivity premise is
hidden. The supplied elementary decoder costs `O(k^2+Mk)` field operations,
so the small sketch does not itself deliver fast decoding.

Neither this matrix nor these aggregate moments are available from a single
legal quartet query. Computing them from previously recovered full support
is postprocessing. The existing fixed-query indistinguishability witness
survives every deterministic postprocessor of its identical answers. Complex
coordinates, Fourier transforms or nonlinear packing cannot repair those
missing observations. Adaptive selection or a genuinely stronger measurement
contract must be justified independently.

The structural code in Section 5 of MINIMAL-PROJECTION inherits the pinned
occurrence-tree, adjacent-duplicate, port-extension and split-accounting
claims. Its O(n) shape/flag count follows from the stated linear total port
bound. A source embedding order is correctly required. Replacing that order
by an arbitrary compatible circle would be an unproved strengthening. This
review did not independently revalidate source admission or implement the
structural decoder.

## 8. Executed checks

The existing `adaptive-adversary-pair-controls.py` and
`minimal_projection_controls.py` were rerun successfully before the hidden-set
extension. Their five-taxon hidden-pair checks and moment/distance receipts
matched the reported results. The scripts supply finite corroboration, not
the all-size counting proof; the loose terminal bounds are numerically
uninformative at five taxa.

The additional independent script
[boundary_review_controls.py](boundary_review_controls.py) produced
[boundary_review_controls.json](boundary_review_controls.json):

| Check | Executed result |
|---|---:|
| Caterpillar label-swap hidden-pair candidates, n=5,...,12 | 60 passed |
| Eligible pairs demonstrated in each caterpillar | n-1 |
| All circular split subsets, distance inversion, n=4,...,6 | 548 passed |
| Quartet-support regenerations from those exact inversions | 7,844 passed |
| Negative control: p=2, M=3 aliases singleton IDs 1 and 3 | Collision confirmed |

The distance subset controls deliberately include split systems not admitted
by the source model. They check the generic algebra only. Caterpillars are
actual admitted binary-tree witnesses. The triple/quartet refinements above
are hand proofs; their extension controls remain owned by the original
adversary contributor, not executed again for this review packet.

## 11. Process integrity

The original proof was checked against deletion restrictions, actual split
lifts, membership-run changes, binary cherry attachment, interval arcs and
boundary-quartet witnesses. Candidate common circularity was not assumed.
Source admission/count dependencies were kept conditional and attributed.
The sharper constants were derived by counting baseline flip records rather
than treating deduplicated neighbor splits as independent free choices.
Controls were separated from the all-size argument and from source-model
validation. No numerical process-integrity score substitutes for these named
proof obligations.

## 12. Robustness

The hidden-set result depends on exact complete existential support, n>=5,
binary trees and a circular baseline. Multifurcating attachment would break
the two-open-arc argument. Statistical non-observation cannot replace exact
absence. A failure of the source representation or split-count premise would
invalidate its source-linear specialization, while leaving the generic
`O(n+k)` theorem and algebraic shadows intact.

The reviewed results push fixed-baseline adversary cardinality and exact
storage boundaries. They do not establish the adaptive query optimum, recover
source switching probabilities, or identify a unique network. The next
master-closing result must still specify permitted measurements and prove
its guarantee on the complete admitted finite source class.
