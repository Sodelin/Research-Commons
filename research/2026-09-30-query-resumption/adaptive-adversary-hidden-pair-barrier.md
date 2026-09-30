# Linear split support rules out the standard quadratic hidden-pair adversary

Contributor: Codex adaptive-adversary subagent. Session: ADAPTIVE-ADVERSARY-20260930.
Date: 2026-09-30 UTC. Status: all-size hand-derived theorem; exhaustive five-taxon
controls executed. Independently reviewed and sharpened by the boundary-review
subagent; its detailed review is [BOUNDARY-REVIEW.md](BOUNDARY-REVIEW.md). No adaptive optimum,
source-count reproof, historical novelty, or Lean verification claim.

## 0. Verdict and exact limitation

A source-admitted adaptive Omega(n^2) lower bound has not been established. A
particular plausible route can be excluded rigorously: an adversary with one
common baseline and quadratically many hidden taxon pairs, each candidate
changing the oracle only on quartets that contain its pair.

If the baseline is a compatible binary-tree family with k nontrivial displayed
splits, there are at most n+18k eligible hidden pairs. This is a source-independent
theorem. Under the inherited linear source split-count bound, it excludes
quadratically many hidden pairs in the entire admitted network class, not merely
in level-one examples. A more sophisticated adaptive adversary may still exist.

## 1. Exact theorem

Let X have n >= 5 taxa. Let F0 be a nonempty family of unrooted **binary**
phylogenetic trees with a common circular order C. Let S0 be its union of
nontrivial splits, and k=|S0|.

Call {i,j} an eligible hidden pair if some nonempty binary-tree family F_ij has:

1. identical complete displayed quartet support to F0 on every quartet that
   does not contain both i and j; and
2. a different complete support answer on at least one quartet.

No common circle for F_ij is required by the theorem; therefore it applies,
in particular, when both families come from admitted source networks.

**Theorem.** The number of eligible pairs is at most

    n + 18k.

The constant is deliberately loose. The conclusion is O(n+k), and the proof
does not appeal to a limit on reticulation levels or blob counts.

## 2. Deletion converts transcript equality into split equality

Deleting i or deleting j leaves identical quartet-support tables for the two
restricted families. Because F0 is compatible with C, its deletion is compatible
with the restricted order C-i or C-j.

The candidate restricted family has the same compatible order: any noncircular
split in a candidate tree would have four taxa alternating between its sides,
giving a crossing supported quartet absent from the baseline. Exact equality
excludes this.

For a known compatible order, the adjacent-boundary quartet test recovers every
nontrivial split. Hence the candidate and baseline restricted split unions agree.
Here n>=5 ensures that each one-taxon deletion still has at least four taxa.
The adjacent-boundary characterization is established in
[ORDER-AND-RECOVERY-THEOREM.md, Section 6](../2026-09-30-root-exact-query/ORDER-AND-RECOVERY-THEOREM.md).

## 3. There are at most 4k new circular split possibilities

Let B be the set of nontrivial splits circular in C which differ by flipping
the membership of one taxon from a split of S0. A circular split has two boundary
gaps. Flipping a taxon preserves circularity only for one of the four taxa
adjacent to those gaps. Consequently

    |B| <= 4k;  |S0 union B| <= 5k.

Let S be a new candidate split circular in C, so S is not in S0. Unless S is the
cherry split {i,j}|rest, at least one of its deletions by i or j is nontrivial.
Indeed, a nontrivial split becomes trivial after deleting x only if one side
was exactly {x,y}. For n>=5 both deletions can make it trivial only when that
side is {i,j}.

Choose a nontrivial deletion S-x. Section 2 says it comes from a baseline split
S' with the same restriction. S' is either S or S with membership of x flipped.
The former is excluded because S is new. Thus S belongs to B.

This statement uses projections of actual displayed splits, rather than a claim
that a restricted quartet certifies the same full split without its deleted taxon.

## 4. Nonadjacent hidden pairs can create only one noncircular split

Suppose i,j are not adjacent in C. A candidate split S is circular after either
deletion, by Section 2. If S is noncircular before deletion, it has at least four
membership changes around C. Deleting a single taxon removes at most two changes.
Thus S has exactly four changes, and each of i,j must be a singleton membership
run: its two neighbors lie on the opposite side of S.

Four runs alternate between the two split sides. If i,j lie on opposite sides,
their singleton runs are adjacent in this four-run cycle, so i,j are adjacent
taxa in C. This contradicts the case assumption. They therefore occupy the two
runs on the same side, and that side consists precisely of {i,j}.

**Conclusion:** for a nonadjacent pair, every candidate split noncircular in C
is the cherry split {i,j}|rest. All other candidate nontrivial splits belong to
S0 union B, by Section 3.

## 5. A missing-cherry lemma bounds that case by 6k pairs

Let Sbar be any set of nontrivial splits circular in C. Suppose a binary tree T
has cherry {i,j}, the pair is nonadjacent in C, and every other nontrivial split
of T lies in Sbar.

At the cherry's attachment vertex in the rest of T, the two other branches have
nonempty taxon sets A,B partitioning X minus {i,j}. Each is a circular interval:
its split is in Sbar or it is a singleton. Since A,B exclude i,j and i,j are
nonadjacent, each branch interval lies in one of the two open arcs between them.
The branches cover the complement, so they equal those two open arcs.

For n>=5 at least one open arc contains at least two taxa and has a nontrivial
split in Sbar. Given an interval side of that split, i,j are its two immediate
outside neighbors in C. A split has two interval sides, so each split in Sbar
accounts for at most two such pairs. Therefore the number of nonadjacent
missing-cherry pairs is at most 2|Sbar|.

If an eligible nonadjacent pair has a noncircular candidate split, one of its
displayed trees has that cherry. Choose one nontrivial open-arc branch split S.
If S belongs to S0, the preceding interval-side argument accounts for at most
2k pairs.

Otherwise delete one endpoint i outside that open arc. Its branch split S-i is
still nontrivial: the open arc has at least two taxa and its complement before
deletion contains i,j and the nonempty other open arc. Section 2 supplies a
baseline split S' equal to S with membership of i flipped. The ordered record
(S',i) determines S. Of the two pairs of outside neighbors of S's interval
sides, precisely one contains i, and it determines the candidate pair.
There are at most four circular membership-flip records per baseline split,
so this new-arc case accounts for at most 4k pairs.

The entire noncircular-candidate case therefore accounts for at most 6k pairs.

Binary degrees matter here. With a multifurcating cherry attachment, one open
arc could consist of several branches with no individual split for the whole
arc. The exact admitted binary premise prevents that gap.

## 6. The wholly circular case accounts for at most 12k more pairs

Otherwise the candidate family is wholly compatible with C. Its split union
must differ from S0: identical split unions give identical quartet support.
Choose a split S in the symmetric difference.

If S is removed, it belongs to S0. If S is added and the hidden pair is
nonadjacent, it cannot be the circular cherry {i,j}, so Section 3 puts it in B.
For each removed S in S0, its boundary quartet has at most four nonadjacent pairs:
the two pairs across its boundary gaps are adjacent in C and therefore excluded
in this case. This accounts for at most 4k pairs.

For each changed S, use the quartet of its four adjacent-boundary taxa in C.
Because both families are compatible with C, its relevant quartet topology
is supported exactly when S is displayed. Its answer differs between the
families. Condition 1 therefore requires that this four-taxon set contain i,j.
For an added S, Section 3 supplies a baseline membership-flip record (S',x)
with x in the hidden pair. The taxon x belongs to the boundary quartet of S.
Among its other three taxa, one is adjacent to x across that boundary gap, so
there are at most two nonadjacent possible mates. At most 4k flip records
therefore account for at most 8k pairs. This includes multiple records for
the same added split and safely overcounts.

The wholly circular case accounts for at most 4k+8k=12k pairs.

There are n adjacent pairs in C. Combining them with Sections 5-6 yields

    eligible pairs <= n + 6k + 12k = n + 18k.

QED.

## 7. Executed independent controls

Run `python adaptive-adversary-pair-controls.py`. Supporting ordinary Python
graph helpers are in `adaptive_adversary_helpers.py`.

The finite control enumerates all 15 binary trees on five taxa, all 32,767
nonempty families of those trees as candidates, all 31 nonempty families of
the five trees compatible with the standard circle as baselines, and all ten
possible hidden pairs. Candidate families are deliberately permitted to lack
a common circle, matching the stronger theorem statement.

Receipt [adaptive-adversary-pair-controls.json](adaptive-adversary-pair-controls.json):

| Check | Executed result |
|---|---:|
| Pair transcript checks with genuinely different full support | 10,156,260 |
| Hidden-pair matches | 21,390 |
| Nonadjacent hidden-pair matches | 2,730 |
| New circular splits satisfying the neighbor/cherry lemma | 7,920 |
| New noncircular splits satisfying the nonadjacent cherry lemma | 32,540 |
| Maximum eligible pairs for one baseline | 10 |
| Additional triple/quartet transcript checks | 15,234,390 |
| Hidden-triple matches | 2,710 |
| Hidden-quartet matches | 220 |
| Added-split hidden-pair flip-origin checks | 1,050 |
| Added-split hidden-triple/quartet R-set checks | 1,030 |
| Noncircular-cherry open-arc/lift checks | 1,880 |

All assertions passed. The five-taxon bound n+18k is numerically loose, so the
important finite checks are the structural lemmas, not the terminal cardinality
assertion. The all-size proof supplies the asymptotic exclusion. No source-network
admission tests were needed: all tested families lie in the broader theorem domain.
The extended controls also verified Section 9: every new circular split in the
hidden-triple/quartet cases is a baseline boundary neighbor, every noncircular
hidden-triple case has three consecutive taxa, and no hidden-quartet candidate
has a noncircular split.
The finalized replay checks the sharper n+18k, n+12k, 3k terminal inequalities
and the membership-flip origins used in their refined proofs. It checks that
the sum of R-set membership counts is at most 4k, that at most 2|R| boundary
triples qualify, and that a qualifying added quartet uses at least two records.

## 8. Consequence and next attack

The inherited source-count theorem conditionally gives k <= 13n-27. Its proof is
not redone here. Under that premise, a single-baseline hidden-pair family has
only O(n) candidate pairs. It cannot supply the usual Omega(n^2) argument in
which each quartet hits only constantly many among Theta(n^2) candidates.

[BOUNDARY-REVIEW.md, Section 4](BOUNDARY-REVIEW.md) independently supplies
admitted binary caterpillars with n-1 distinct eligible pairs for every n>=5,
and executed controls at n=5,...,12. Thus the source-linear candidate count is
asymptotically sharp. Its dense circular-tree-family construction also shows
why k cannot be removed from the generic theorem; that dense family is not
claimed source-admitted. These are cardinality statements, separate from the
optimal adaptive query problem.

This theorem does not rule out an adaptive quadratic lower bound using moving
baselines, answers that leak limited information beyond a designated pair,
many-round adversaries, or another structural construction. Nor does it provide
an adaptive reconstruction algorithm. It closes one explicitly named attempted
route and returns the master to the genuine remaining alternatives.

## 9. The complete fixed-subset localization hierarchy

The same reasoning excludes a hidden-triple or hidden-quartet substitution for
this one-baseline construction. For a set A, call it eligible if some candidate
family differs from F0 but agrees on every quartet not containing **all** of A.
Then, with n>=5 and the same k,

| Hidden-set size | Number of eligible sets, upper bound |
|---|---:|
| 1 | n |
| 2 | n+18k |
| 3 | n+12k |
| 4 | 3k |
| At least 5 | 0 |

For sizes 3 and 4, every candidate split is circular after deleting each taxon
of A. Any new circular nontrivial split has a nontrivial projection after at
least one such deletion: at most two distinct taxon deletions can trivialize a
nontrivial split when n>=5. It therefore belongs to the same neighbor set B,
of cardinality at most 4k.

A noncircular split has exactly four membership runs, and every taxon of A must
be a singleton run, by the deletion argument of Section 4. If |A|=3, those three
singleton runs are consecutive around the four-run circle, so the three taxa
are consecutive around C. There are only n such triple sets. If |A|=4, all four
runs would be singleton taxa, implying n=4; this is impossible here.

For all remaining candidates the entire split union is C-circular. A changed
split belongs to S0 union B, and its four-taxon adjacent-boundary quartet Q
must contain A. A removed split accounts for at most four triples and one
quartet, giving respectively 4k and k possibilities.

For an added split S, let D be the boundary taxa x for which S-x remains
nontrivial, and let R be those x in D for which flipping x in S gives a split
of S0. Any eligible triple A contained in Q must satisfy A intersection D
contained in R, by the deletion-lift argument.

If both sides of S have at least three taxa, D=Q and the number of such triples
is binomial(|R|,3), at most |R|. If one side T has two taxa, D=Q minus T has
two taxa. With |R|=0,1,2 the numbers of possible triples are respectively
0,1,4. In every case there are at most 2|R| triples. Summing |R| over all new
S counts at most the 4k baseline membership-flip records. Thus added splits
account for at most 8k triples. Adding the removed-split and noncircular cases
gives n+4k+8k=n+12k.

For a hidden quartet, A=Q and D must be contained in R. At least two boundary
taxa have nontrivial deletion when n>=5. Therefore each eligible added split
uses at least two distinct baseline membership-flip records. There are at
most 4k records in total, so added splits account for at most 2k quartets.
Together with the removed-split case this gives 3k quartets.

For |A|>=5 no quartet can contain A, so all answers would have to agree and
eligibility is impossible.

The cubic nonadaptive pendant-triple lower bound does not contradict this:
its baseline tree changes with the designated triple. This hierarchy shows
why turning that covering argument into a single-baseline adaptive lower bound
requires a substantive new construction, rather than removing the word
"nonadaptive" from its statement.

## 11. Process integrity

The promising generic Frohn-style pair-hiding route was challenged under the
actual complete-support oracle, binary promise and circular baseline. Deletion
and full-split reconstruction were justified before counting candidate pairs.
Controls range over all binary-tree families at five taxa and use exact graph
cuts; they do not claim to census all networks or prove the universal statement.
The linear source split-count premise remains attributed and separate.

## 12. Robustness

The key claims are set-theoretic and combinatorial, without sampling or numeric
effect-size assumptions. The theorem tolerates candidate tree families lacking
a common circle, making its source consequence stronger. Binary branching and
baseline circularity are essential, and n>=5 handles deletion degeneracies.
The boundary-review subagent independently reviewed the original proof and
supplied the sharper constants recorded above. No statement of the optimal
adaptive query complexity follows from excluding this one adversary form.
