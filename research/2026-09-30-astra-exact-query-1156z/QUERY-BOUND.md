# Adaptive acquisition bound: common order in O(n log n), joint source recovery in Theta(n log n)

Contributor: GPT-6 Astra Pro / ASTRA-EXACT-QUERY-20260930T1156Z. Date: 2026-09-30 UTC. EXACT-QUERY-01.

**Status:** complete hand-derived asymptotic argument with an implemented order learner and initial graph-derived controls. Independent proof review is requested and not yet received. Exact finite-n minimax constants and historical priority are not settled. This file does not relabel those unfinished audits as completed.

Dependencies: the all-family path-insertion invariant in ORDER-SPACE.md, the exact insertion-slot lemma in INSERTION.md, and the attributed committed sparse split decoder. The source specialization also uses the previously committed linear split-count theorem, not a newly assumed count or a bounded-level extrapolation.

## 1. Theorems and explicit upper bound

Let F be any nonempty family of binary unrooted trees on a known n-taxon set, admitting a common circular order. An oracle query on four distinct taxa returns the COMPLETE set of distinct resolved quartet topologies displayed by F. There is a deterministic adaptive algorithm that learns the entire common-order circular-tree representation, and therefore returns a compatible circular order, with O(n log n) oracle calls and no supplied order, tree, or blobtree.

A conservative explicit bound for the stated implementation and analysis is

    B_order(n) = (n-3)(11 ceil(log2 n)+15),   n>=4.

Caching also gives Q_order<=C(n,4). These constants are sufficient upper bounds, not proposed optimum constants.

If the full nontrivial split union has size k, composing with ASTRA-SPARSE-20260930-0938Z's exact known-order rectangle decoder gives

    Q_joint <= min{ C(n,4),
                    B_order(n) + 2n-6 + 4k ceil(log2(n-1)) }.

The same cache is used across both stages after topology-preserving relabeling. The two-stage bound does not mistake an order representation for full split support; the inherited level-two anchor collision still applies.

For the admitted binary semi-directed LSA-rootable outer-labeled planar galled network class, the prior source theorem gives

    k <= min{ n(n-3)/2, 11n-23 }.

It follows that joint exact recovery across arbitrary finite levels and blob counts uses O(n log n) queries. The admitted ordinary-tree subclass supplies the matching Omega(n log n) lower bound, so the asymptotic deterministic adaptive optimum is Theta(n log n), subject to the stated proof/audit status and inherited source dependencies.

## 2. The measured local object

The old state is the circular tree B of ORDER-SPACE.md, learned inductively from the oracle, not supplied. At each internal vertex v its old port order C_v is rigid up to reversal, and its local insertion set J_v is either one corner or the two gaps around an arrow port. Local representatives are ordinary old taxa, one from each incident branch.

Two primitives are already justified:

(1) Given a specified port p with predecessor and successor representatives a,c and its own representative b, one quartet tests the arrow v->p exactly:

    Q(z,a,b,c) = {zb|ac}.

(2) Once v is known to be a corner, its unique gap can be learned with at most E(d_v)+4 queries, where E(0)=E(1)=E(2)=0 and E(s)=1+E(s-floor(s/3)). This is the promised insertion learner; its promise is proved locally by the full common-order invariant.

For s>=3, floor(s/3)>=s/5. Thus each reduction retains at most 4s/5 candidates, giving the convenient bound

    E(d) <= 4 ceil(log2 d).

Both primitives use complete exact support. A single positive topology in a two-topology answer is not a singleton arrow certificate.

## 3. Biased local classification

To locate a corner without scanning the whole old tree, we need a local search that is cheap when the arrow points into a heavy branch. Suppose positive integer weights w_p have been assigned to the currently possible arrow ports. Zero-weight arrow alternatives have already been excluded by a search-region invariant. Let W=sum w_p.

Maintain all candidate local gaps G, initially every gap of C_v. A port remains a possible arrow only if BOTH gaps adjacent to it remain in G. Querying z and three ports forbids one cyclic arc of gaps for each supported quartet topology: the crossing topology cannot occur in a valid insertion. True gaps and the true arrow, if there is one, are never removed.

Repeat while a possible arrow remains.

**Heavy-port case.** If some possible port p has w_p>W/6, apply the one-query arrow test to p and its two immediate cyclic neighbors. A singleton arrow answer identifies p and terminates. Otherwise at least one gap adjacent to p is forbidden, so that arrow alternative disappears. At least W/6 of possible-arrow weight is eliminated.

**Balanced case.** Suppose every possible weight is at most W/6. Traverse possible ports cyclically. Take a first consecutive group of weight at least W/4 and stop immediately on reaching that threshold; do the same for a second group. The remaining group has weight greater than or equal to W/6. Each of the first two groups has weight less than W/4+W/6=5W/12, so all three groups are nonempty and each has at least W/6. Query z together with the first port of each group. Any supported topology forbids one of the corresponding three gap arcs. Every possible arrow whose port lies in that group loses at least one adjacent gap, including its boundary port. Thus at least W/6 of weight disappears.

If no possible arrows remain, v is a corner: all actual arrows were among the alternatives by the search invariant, and the local classification has only the arrow/corner cases. Its specific corner can then be learned separately by primitive (2).

Every nonterminal query reduces possible-arrow weight by a factor at most 5/6. If the true arrow is p, its positive weight w_p survives. Consequently its classification cost is at most

    2 + log(W/w_p)/log(6/5)
      <= 2 + 4 log2(W/w_p).

If v is a corner, integer positive weights ensure termination after at most

    2 + 4 log2(max{1,W})

queries. These bounds concern real queried quartets. A small representation dimension alone is not used as a measurement-cost argument.

The implementation uses integer tests 6*w_p>W and 4*group_weight>=W, avoiding floating-point choices. Gaps can be filtered in linear time from their membership in the three cyclic arcs; a whole order need not be rebuilt for every gap.

## 4. Centroid search with an exceptional edge case

Let U initially contain every vertex of B. The invariant is:

- if a nonempty corner path P exists, all its vertices are in the connected search region U;
- if no corner exists, both endpoints of the unique attachment edge are in U.

Choose a centroid v of the induced tree on U. For each incident port p set its weight to the number of U vertices in that branch after removing v. Branches outside U have weight zero. Thus W=|U|-1 and every positive weight is at most |U|/2. A true arrow must point into a positive-weight branch, unless an earlier edge identification has already ended the search. For an old taxon leaf, its sole arrow is known without querying.

Apply biased local classification at v. If it is a corner, search has succeeded. If it points to neighbor u, test the reverse arrow u->v. When both arrows hold, all attachment positions lie in the edge vu, so the no-corner case is identified. Otherwise delete v from U and continue in its component through u.

If a corner path exists, v is outside it and the whole path lies in that component. If the exceptional edge exists, v cannot be one of its endpoints without the reverse-arrow test identifying it; hence both endpoints remain in the chosen component. This proves the invariant including pendant-edge cases. It also proves that excluding zero-weight arrows is legitimate.

Every continuing step shrinks |U| by at least a factor of two. More importantly, the cost of an arrow step is bounded by

    3 + 4 log2(|U|/|U_next|),

including the reverse-arrow check. These logarithms telescope. Adding the final corner classification or edge detection gives at most

    7 ceil(log2(2n)) + 2 <= 7 ceil(log2 n)+9

queries for one search, since B has at most 2n-2 vertices. This avoids the extra logarithm that would arise from paying an unweighted O(log degree) search at every centroid.

## 5. Discovering the full path and updating

After finding a corner, learn its unique gap. Follow its two gap directions. At a neighbor, one reverse-arrow test either stops that arm or proves the neighbor is another corner; in the latter case learn its gap and continue through the other gap direction. ORDER-SPACE.md proves this traces all and only the corner path, without inspecting unrelated branches.

For a path of k vertices, the path phase uses k calls to the promised local gap learner and at most k+1 arrow predicates. The rotations are spliced with aligned z markers and the path is replaced by one new circular vertex. In the exceptional edge case, simply subdivide the edge and attach z. These updates preserve ALL common frontiers and the common-refinement invariant.

The implementation starts from the first three supplied taxon labels and proceeds in their supplied deterministic order. It uses deterministic representatives and tie-breaking. It never receives the displayed family, its attachment positions, a true full order, or its blobtree. These objects appear only in the proof and in independent truth generation for finite controls.

## 6. Global accounting

Let L=ceil(log2 n), and perform n-3 insertions. Every insertion creates one internal vertex; a path update deletes its k old corner vertices. Since the final tree has q_n>=1 internal vertices,

    sum k = n-2-q_n <= n-3.

Therefore all corner-learning calls together use at most

    (n-3)(4L+4)

queries. All arm arrow predicates together use at most 2(n-3). All centroid searches together use at most (n-3)(7L+9). Summing yields

    Q_order <= (n-3)(11L+15).

Repeated quartets are answered from the cache. The final split decoder's queries are also routed through that cache. This proves the explicit upper bound in Section 1, with no maximum level, maximum blob size, or average-case assumption.

The amortization counts retired representation vertices, NOT biological reticulations or graph size. Arbitrarily many source vertices do not appear in the learned state.

## 7. Reusing the committed split decoder exactly

The second stage is the existing sparse rectangle algorithm, not a new claim in this packet. Its source is research/2026-09-30-astra-sparse-query/sparse_quartet.py, blob 49933337ce26ce0d5ef58bbfa458bf5706d8e817, read at initial Commons head f0783cfaa8df877dd10bbd904fd9c3882fccb9f6. It receives positions 0,...,n-1 in the learned order and tests rectangle emptiness with exact support, returning nonadjacent gap pairs.

When the original labels are permuted, topology masks must be remapped by their bipartitions. Bit 1 on the sorted ORIGINAL labels is not necessarily bit 1 on the sorted ORDER POSITIONS. The adapter decodes each supported pair partition, relabels it, and re-encodes it before calling the unchanged provider. This exact relabeling preserves oracle answers and the represented split target. The provider's original crossing-topology and nonempty-support checks remain in force.

Independent integration execution and provider-byte receipts belong in the executable packet; they are not asserted merely by this design description. Before recording integrated PASS, execute the actual pinned provider rather than a rewritten imitation.

## 8. Source specialization and matching lower bound

The order theorem applies to an even larger abstract class than the registered networks: any nonempty family of binary trees sharing a circle. A finite binary outer-labeled planar network supplies such a family through its displayed trees and an outer-face embedding. The required source linear split bound is reused from ASTRA-STRUCTURAL-4S-20260930T1033Z's SUPPORT-BOUND-AND-PRIOR.md, blob 79cde7a26d325354ab51d03b4f7fbbc0f662d326. Its three-port correction gives k<=11n-23, improving the root's earlier 13n-27 bound. It remains conditional on the same committed source port-localization and adjacent-duplicate occurrence representation; this packet does not silently extend that count beyond its domain.

Ordinary labeled binary trees are admitted. There are (2n-5)!! such unrooted trees. On this subclass every quartet query has only three possible answers, and two different trees have different complete split unions. A deterministic query tree recovering that union must therefore have at least (2n-5)!! terminal leaves. Hence

    Q_joint*(n) >= ceil(log_3((2n-5)!!)) = Omega(n log n).

Combining with Section 1 proves asymptotic optimality for the requested BOTH-output problem.

Even the order-only task has an Omega(n log n) lower bound. A fixed circular order is compatible with Catalan_(n-2) labeled binary trees, by rooting at a fixed leaf and counting ordered binary tree shapes with the remaining labels in the fixed sequence. Thus one returned order can cover at most that many tree inputs. The ratio

    (2n-5)!! / Catalan_(n-2) = (n-1)! / 2^(n-2)

still has logarithm Omega(n log n). This is only an additional order-only observation; the stronger split-output counting lower bound is the one used for the registered master.

No nonadaptive lower bound has been reused as an adaptive lower bound. The root's fixed-schedule cubic obstruction remains compatible with the adaptive improvement. The arbitrary-level Frohn lower-bound constructions were not transferred into the narrower source class.

## 9. Computation, storage, and output are separate

The finite query bound is independent of response-computation cost: an exact-support oracle is the stipulated input interface. The new reference order learner can be implemented in O(n^2 log n) ordinary word operations with straightforward tree traversals, deterministic minimum-leaf representatives, linear-time centroid construction, and O(d) gap filtering per local query. This is a conservative polynomial upper bound, not an optimal runtime claim. The optimized local reference implementation uses those operations; full-source oracle-generation cost in tests is additional and is not hidden in the learner runtime.

The state has O(n) tree vertices/ports, O(n) transient search/representative data, and an O(Q_order) cache and transcript. With the shared decoder cache and compact gap-pair output the space is O(n+Q_joint+k) words. The unchanged sparse decoder has its own documented O(n+k log n) expected dictionary-operation overhead. Python hash-table behavior is not an adversarial worst-case dictionary proof; a balanced ordered map would add its conventional logarithmic lookup factor without changing oracle complexity.

The complete split union can be returned as the learned taxon order plus k gap pairs, an exact O(n+k)-word representation. Expanding both sides into explicit taxon lists may cost O(nk) output time and space; with k=O(n) this can be quadratic. An optimal query theorem does not turn quadratic explicit printing into near-linear time.

## 10. Closure boundary and quantitative observation interface

This resolves the asymptotic query-gap obligation at the level of the given hand proof and implementation, rather than stopping after the insertion counterexample. Independent proof review, a verified implementation audit, formalization, and historical priority remain distinct obligations. The exact integer decision-tree minimum Q*(n), or best leading constant, is not derived from matching asymptotic bounds.

The biological-observation problem is not thereby solved. Under a separately justified exact-support confidence interface, the whole deterministic two-stage algorithm has a fixed ideal transcript for each true source. The already attributed first-error argument can charge erroneous support estimation only along that transcript. A uniform finite bound obtained by substituting k<=11n-23 can replace the earlier cubic query budget in that transfer. No independence between reused quartet estimates is required by the union bound, but their valid marginal/simultaneous error guarantees and the source observation-identifiability assumptions must actually hold. False singleton masks are not licensed by small empirical frequencies.

## 11. Process integrity

The complete assignment, current Commons ownership, existing reconstruction/sparse/count/collision/lower-bound packets, and the structural, observation and transfer records were read first. The concurrent QUERY-RESUMPTION-20260930-1144Z publication at b3e850ed1cdb95fdad1cf5b5076e6ea23b4dc9d7 was detected and its README, primary-prior audit and algebraic review read. Its work and attribution are preserved, not overwritten. A stronger explicit query-acquisition proof is offered for independent challenge rather than inferred from the older small affine representation.

The new order implementation has author-run finite controls of its full frontier invariant. Production PQ/PC libraries, subagents, biological experiments, independent reviewer execution and Lean verification have not been used in this session. A published review request is not a received review. All-size mathematical claims stand on the displayed proofs, not the number of successful finite examples.

## 12. Stress test and exact next attack

The most important review targets are: (i) the local-to-global attachment lemma over arbitrary binary-family refinements; (ii) arrow iff singleton on three consecutive ports; (iii) preservation of every old off-path split when an attachment is in an endpoint edge; (iv) exact frontier-language preservation under marker splicing; and (v) the weighted centroid accounting, including zero-weight ports and the no-corner edge case. These are named proof obligations with arguments supplied, not hidden premises.

Next actions in this active continuation are to integrate and hash-check the actual sparse provider, compare the order state with the separately authored affine learner, enlarge graph-derived and adversarial weighted-search controls, publish all executable receipts, and request independent review of (i)-(v). A failure will be preserved and the theorem revised rather than concealed. The user-facing verdict must keep asymptotic closure, finite-n exact optimality, review status, and biological identifiability separate.
