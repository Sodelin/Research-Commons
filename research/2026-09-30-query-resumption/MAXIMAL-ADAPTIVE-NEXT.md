# Why the quadratic parity method is not the adaptive minimum

Contributor: Codex `minimal_projection` subagent, MAXIMAL-ADAPTIVE-NEXT-20260930.
Date: 2026-09-30 UTC. Status: hand-derived method boundary, source-admitted
insertion counterexample, exact five-taxon source optimum, conditional source
separator lemma, and executed finite controls. No all-size optimal adaptive
source theorem or novelty claim.

## 0. Decision

The resumed Gallai/parity learner is a meaningful constructive improvement,
but its initial stage cannot attain an O(n log n) query goal: eliminating
**every** nontransitive affine assignment through primitive quartet equations
requires Omega(n^2) queries even on ordinary binary trees. This is a lower
bound on that method, not on EXACT-QUERY-01. Returning one common circle
does not require eliminating every affine assignment.

I attacked a natural route around that barrier, incremental taxon insertion,
and found an actual admitted level-two counterexample to its simplest
extension invariant. I also derived a source-specific balanced separator
with only two ambiguous ports, which is a concrete structural target for
near-linear hierarchy learning. Discovering it cheaply remains unproved.
An explicit six-network oracle adversary closes one genuine finite case:
**on five taxa, the full admitted-source adaptive optimum is exactly five
quartet queries**. This finite optimum does not settle the asymptotic master.

## 1. Exact primitive-rank boundary

Fix anchor r, let Y have n-1 taxa, and write one pair-order variable for
each unordered pair of Y. The ambient affine dimension is

    m = binomial(n-1,2).

Start with no source-derived equations beyond the usual ambient cyclic
identities used to obtain these m independent coordinates. A positive
anchored quartet adds one primitive signed pair equality. Complete support
has at most two positive topologies under the common-circle promise, so
one measured quartet supplies at most two independent primitive equations.

Suppose a method stops its initial phase only when **every** assignment
in the measured affine solution space is transitive. Keijsper--Pendavingh's
cyclic affine-space dimension theorem, cited and inspected in
[PRIMARY-PRIOR.md](PRIMARY-PRIOR.md), bounds that final dimension by n-2.
Hence it must have accumulated rank at least

    m-(n-2) = binomial(n-2,2).

Consequently its initial phase requires at least

    ceil(binomial(n-2,2)/2)
      = ceil((n-2)(n-3)/4)
      = Omega(n^2)

primitive complete-support queries. This statement allows measured rows
to be combined by Gaussian elimination or parity closure: row-span closure
cannot create independent rank.

### A sharper exact tree count

On a single binary tree T, every answer is a singleton and gives at most
one row. T's common-order affine space has dimension exactly n-2. It is
contained in every partial measured space, because every measured row is
a true T row. The stopping condition imposes dimension at most n-2,
so the final measured space must equal the entire T common-order space.
Its required rank is precisely `binomial(n-2,2)`. Therefore

    cycle-phase calls >= binomial(n-2,2).

The production cycle-witness rule only measures when a directed triangle
cycle is still possible. The answer excludes that cycle assignment and
therefore contributes at least one independent row. A tree query has only
one row; thus every such measured query raises rank by exactly one, and
the cycle phase makes **exactly** `binomial(n-2,2)` calls on every tree,
regardless of tree shape or naming order, provided the implementation
uses precisely this stopping and row-acquisition rule.

This establishes a matching quadratic bound for that initial method,
not a matching bound for the full adaptive problem.

### Why this is not a master lower bound

A source-aware learner could infer an entire latent structure from fewer
queries and then write many equations that are logical consequences of
that structural inference. They need not belong to the linear span of
the measured primitive rows. Ordinary tree reconstruction already does
this: near-linear adaptive quartet learning identifies T, whose explicit
hierarchy induces a quadratic-rank comparison system.

The extra inference must actually be justified. On the whole admitted
source class, singleton answers to the queries asked so far do not
automatically prove that the unknown input is a tree or that every row
of an estimated tree applies to the other displayed trees. A fabricated
completion is not a valid way to evade the method boundary.

For unrestricted four-taxon queries the standard quartet equation is
still one primitive linear row per positive topology in the same ambient
coordinate system, though it need not be a two-variable signed edge.
The maximum-two-rows bound therefore persists for the same literal
affine-elimination strategy. The sharper exact tree count above applies
when the method's measured singleton rows are the only independent rows
it adds and it stops at an all-cyclic space.

## 2. Actual admitted obstruction to insertion without old-label repair

The inherited graph/switching-validated source fixture N1, on taxa
`0,1,2,3,4`, has nontrivial full split union

    12 | 034,
    123 | 04,
    01 | 234,
    012 | 34.

The two-taxon sides of these splits are `12`, `04`, `01`, and `34`.
Any compatible five-taxon circle must make all four pairs adjacent.
These adjacencies form the spanning path with consecutive vertices
`2,1,0,4,3`, whose only closing edge is 23. Consequently the full circle is uniquely
`(0,1,2,3,4)` up to reversal and rotation.

Delete taxon 0. The only nontrivial restricted split is `12|34`.
Thus `(1,2,4,3)` is a correct circle for the restricted oracle. But no
insertion of taxon 0 into any of its four gaps yields the full circle
or satisfies every full split. Exact controls enumerate all four gaps
and find zero passing extensions.

This is **not** merely an arbitrary correlated tree-family example:
N1 is the actual admitted level-two fixture from
[ANCHOR-COLLISION.md](../2026-09-30-root-exact-query/ANCHOR-COLLISION.md),
with inherited binary/DAG/LSA/galled/outer-face certificate and global
independent switching evaluation. The four-split union can alternatively
be seen as the union of two common-circle trees, but source admission
comes from the actual N1 graph, not from that observation.

Therefore a near-linear insertion theorem must permit old-label changes
or maintain enough alternative hierarchical information to select an
extendible old order. “Pick any common order on current taxa, then binary
search a gap for the next taxon” is false throughout the intended source
scope. This counterexample discharges that specific candidate invariant;
it does not refute all adaptive insertion algorithms.

## 3. Source-specific balanced two-ambiguity separator

The following conditional structural lemma uses the same audited
adjacent-copy occurrence representation as SPLIT-COUNT.md. It is a
concrete route toward a small latent hierarchy rather than a mere
low-rank assertion.

**Lemma.** Let a capped branching bloblet have m>=3 port labels and a
binary plane occurrence tree. There is a physical edge whose cut divides
the ports into three sets A,B,C such that:

- at most two port labels belong to B;
- every occurrence of every A label is on one side of the edge;
- every occurrence of every C label is on the other side;
- `|A|,|C| >= m/3-1`;
- after omitting B, the split `A|C` is present in every independent local
  switching; in particular every quartet with two A ports and two C ports
  has the same singleton support `AA|CC`.

**Proof.** Put weight 1 on a unique occurrence and weight 1/2 on each
occurrence of a duplicated port. The total leaf weight is m, and every
physical leaf has weight at most one. A weighted centroid of the binary
tree has each incident branch weight at most m/2. For m>=3 a leaf cannot
be the sole centroid with a branch of weight m-1>m/2, except the equality
case m=2 which is excluded. At a degree-three centroid the heaviest
branch has weight between m/3 and m/2. Its incident edge thus has side
weights between m/3 and 2m/3.

Because each duplicated pair is adjacent in the physical cyclic tip
order, only labels whose pair straddles one of the edge's two interval
boundaries can have occurrences on both sides. There are at most two
such labels; these form B. Every B label contributes weight 1/2 to each
side. All other labels contribute their entire weight one on their fixed
side. Hence the fixed-side label counts are each at least `m/3-|B|/2`,
which is at least m/3-1. Every switching retains the edge's separation
of the selected A and C ports. Restricting any two ports from each side
displays the promised singleton quartet. QED.

The statement is about **local ports**. In the full network, a port may
represent an entire attached taxon component. It is incorrect to change
“two ambiguous ports” into “two ambiguous original taxa” without further
work. Nor is a capped-blob port oracle supplied by EXACT-QUERY-01.

### A useful classification frame, with its missing condition visible

At a physical degree-three occurrence-tree vertex, its three branches
are three disjoint cyclic leaf intervals. At most three duplicated port
labels straddle branch boundaries. If each branch contains a port all
of whose occurrences lie in that branch, choose anchors a,b,c, one in
each branch. For every other stable port x, querying `{a,b,c,x}` gives
one topology: x pairs with the anchor in x's branch. For a straddling port
x, the complete support has the two topologies corresponding to its two
branch locations. Independent copy selections ensure both occur.

Thus, **given such a stable frame**, O(m) legal complete-support queries
classify all its stable ports and explicitly identify at most three
ambiguous ports. No probability estimate or absent rare event is used.

However, this note does not prove that a balanced stable three-anchor
frame always exists or can be discovered cheaply. A physical branch can
contain only an occurrence of a boundary-straddling label and then has
no stable anchor. All-duplicated caterpillar occurrence trees illustrate
why this hypothesis cannot simply be omitted. The two-ambiguity edge
lemma itself does not require a three-anchor frame.

### Concrete next attack, stated as an algorithmic obligation

Learn the balanced occurrence/port hierarchy directly. At each recursive
subproblem, identify a balanced local split with at most two ambiguous
ports using O(m) complete quartet-support calls, handle those exceptional
ports explicitly, and recur on the stable sides. A valid implementation
must also discover the unknown blob attachment components and emulate
the needed port representatives using actual original taxa.

If the classification and exceptional-port interface can be proved at
this cost, balanced recursion gives an O(n log n) measurement candidate
without reading a quadratic-rank pair basis. The present contribution
proves the separator and stable-frame classification identities and
refutes naive order extension. It has **not** proved the decisive
separator-discovery/port-interface theorem. That named missing theorem,
rather than more algebraic packing, is the strongest concrete continuation
found in this lane.

This is this contributor's own continuation candidate, not a reassignment
of the shared master. At this checkpoint the coordinating root reports
that a separate Astra O(n log n) proposal is under independent review.
This contributor has not read or audited that proposal. Reconcile the
separator candidate with the updated peer result before treating it as
the team's next priority; a verified existing near-linear construction
would supersede this discovery obligation.

## 4. The finite optimum exists; the quoted lower bound may be loose

For each fixed finite n, the complete-support oracle has finitely many
possible profiles: at most `7^binomial(n,4)`, and fewer under the common
circle promise because masks have at most two topologies. Arbitrarily
long hidden source chains do not change this finiteness. The required
split-plus-order output also has finitely many possibilities.

A deterministic query algorithm can be represented by a finite decision
tree. A repeated query adds no information and can be omitted. Querying
all `binomial(n,4)` sets supplies a finite-depth always-correct algorithm,
using the inherited constructive reconstruction theorem afterwards.
Therefore the set of feasible worst-case integer depths is nonempty,
and its least integer is attained by at least one decision tree.

This is exact finite-n attainment, not an assertion that the current
`Omega(n log n)` asymptotic lower bound equals that least integer. A lower
bound can be far below the optimum. It also does not provide a single
uniform polynomial-time procedure achieving every finite-n minimum:
an optimal finite tree may be prohibitively large or hard to construct.
General optimization infima need not be attained at all, although this
particular finite integer decision-tree problem does attain its minimum.

Finally, a lower bound alone does not construct a smaller exact shadow.
Section 1 of MINIMAL-PROJECTION.md supplies an actual code and decoder;
its matching bit lower bound is a separate argument. Measurement and
representation minima must not be inferred from one another.

## 5. Exact five-taxon optimum on the admitted source class

**Theorem (hand-derived finite adversary, inherited actual source admission).**
EXACT-QUERY-01 has optimal deterministic adaptive worst-case query count
exactly five on n=5 taxa.

The actual admitted N2 fixture has all five possible nontrivial circular
splits for `C=(0,1,2,3,4)`. Its union is invariant under every cyclic taxon
rotation. N1 has four of these splits, omitting `23|014`. The inherited
exact switching receipt proves that its complete oracle differs from N2's
only on the quartet `1234`, which omits taxon 0.

For `j=0,...,4`, cyclically relabel N1 by `i -> i+j mod 5`. Relabeling
preserves every source admission property. Since N2's complete split union
is rotation-invariant and determines its quartet support, the relabeled
N1 differs from that **same** N2 oracle only on the quartet `X minus {j}`.
It has a different required full split output.

Run any always-correct adaptive deterministic algorithm on N2. If it
omits one quartet `X minus {j}`, all measured responses agree with the
corresponding relabeled N1. Adaptivity does not help: identical responses
produce the same successive query choices, stopping point and output.
That common output cannot be the correct split union for both inputs.
Therefore the N2 execution queries all five possible quartets. Five
queries also suffice by the full-table constructive recovery theorem.
This proves the exact optimum. QED.

The control script directly verifies all five rotated one-query differences,
and an exact decision-tree dynamic program over these six profiles also
returns five. It additionally evaluates the larger demonstrably admitted
subset containing all 15 labeled trees, all 60 distinct N1 relabeling
profiles and all 12 distinct N2 profiles: its 87-profile optimum is five,
with 458 memoized candidate states.

This lower bound is for the complete split-plus-order output. All six
explicit witnesses share a compatible circle; thus this particular
adversary does not lower-bound the order-only five-taxon problem by five.
Nor does it grow into an asymptotic quadratic or cubic adaptive lower
bound without an additional scalable admitted construction.

### Supplementary broader-family calculation

The controls also solve the small decision-tree problem for the **broader**
class of all nonempty binary-tree families admitting a common circle.
They enumerate complete support profiles, and recursively choose the
quartet minimizing one plus the maximum optimum over its answer classes.
Distinct profiles have distinct required split unions, by the inherited
common-circle recovery identity. Therefore every terminal state must
contain one profile.

| Taxa | Distinct profiles | Exact deterministic worst-case queries | DP states |
|---|---:|---:|---:|
| 4 | 6 | 1 | 7 |
| 5 | 117 | 5 | 488 |

The broader-family calculation independently reaches the same five-taxon
number, but it is not the source admission argument: arbitrary correlated
tree families need not be realized by one source network with independent
hybrid choices. The actual six-fixture proof above supplies that argument.
Both calculations illustrate that the answer-count lower bound can be
loose. Neither supplementary enumeration settles asymptotics.

## 8. Actual controls

Run `python maximal_adaptive_next_controls.py`; receipt:
[maximal_adaptive_next_controls.json](maximal_adaptive_next_controls.json).

- Gaussian-eliminated primitive anchored coefficient rows for all 1,068
  labeled binary trees at n=4,...,7. Every rank equaled
  `binomial(n-2,2)`. The checker uses graph cuts and integer Gaussian
  elimination, not the production adaptive learner.
- Independently enumerated all canonical full/restricted N1 circles and
  all four insertion gaps. The wrong but restricted-valid order has zero
  full extensions. The original graph admission was reused from its
  actual receipt and was not rerun.
- Exhaustively computed the two broader-family finite minimax values
  above, using memoized decision-tree recursion over measured profiles.
- Verified the five relabeled source-admitted one-quartet differences;
  exact minimax recursion returns five on both the six-profile adversary
  and the larger 87-profile demonstrably admitted subset.

The separator lemma and stable-frame classifier are hand proofs. Their
discovery algorithm has not been implemented because its correctness
and query bound remain the missing result.

## 10. Primary prior boundary

Keijsper--Pendavingh (2014), DOI 10.1007/s11538-014-0022-z,
arXiv:1308.5206, supplies the affine quartet/order identities and the
dimension bound. The full source and inspected locations are recorded
in PRIMARY-PRIOR.md. Frohn et al. (2025), DOI
10.1016/j.jcss.2025.103655, arXiv:2409.06034v2, supplies sparse level-one
insertion based on a single-reticulation spine. That spine theorem is
not assumed at arbitrary level. The present separator derives instead
from the pinned all-level adjacent-copy tree representation. No historical
priority claim is made for it.

## 11. Process integrity

The proposed rank lower bound was checked against the exact output before
using it: it lower-bounds a stronger stopping rule, not a single-circle
output. The insertion failure was matched to an actual admitted graph
fixture rather than promoted from a generic tree family. The source
separator explicitly retains local-port quantifiers. Finite minimax
enumeration remains labeled by its broader domain. There was no new
systematic novelty search in this continuation.

## 12. Robustness and what would change the conclusion

The rank barrier disappears if an algorithm adds valid source-implied
constraints beyond the span of measured primitive rows, or if it requires
only one transitive assignment. Either change needs a separately proved
efficient method. The N1 insertion failure disappears only if old-label
reordering or a richer alternative-order representation is allowed.
The source separator requires adjacent copies and independent extension;
without those facts its constant ambiguous-port count need not hold.

The adaptive master remains unresolved between the admitted information
lower bound and the resumed learner's proved upper bound. A matching
Omega(n^2) source adversary would make the method's order competitive
but cannot be inferred from its rank. An O(n log n) separator discovery
and port-composition theorem would avoid the quadratic basis acquisition.
No theorem here chooses between those possibilities.
