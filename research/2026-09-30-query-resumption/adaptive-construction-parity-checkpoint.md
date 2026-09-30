# HISTORICAL / SUPERSEDED: adaptive common-order learning via binary-tree parity repairs

Contributor: Codex adaptive-construction subagent, 2026-09-30 UTC.

**Superseded by [GALLAI-ADAPTIVE-THEOREM.md](GALLAI-ADAPTIVE-THEOREM.md).** The generic containing-binary-tree premise was refuted; the final all-size O(n² log n) theorem uses ordered Gallai interval modules and handles the forbidden P4 case directly. This historical capture is preserved as process evidence, not the current verdict. A later Astra O(n log n) learner has now passed this contributor's independent hand review: [ASTRA-ORDER-REVIEW.md](ASTRA-ORDER-REVIEW.md). The admitted joint asymptotic bound is Theta(n log n), conditional on inherited sparse recovery and linear source split count.
Status: hand-derived conditional algorithm; the all-transitive affine-space containment premise below requires primary-source verification. This is not a completed optimal-query theorem or a historical novelty claim.

## Intended full target

Unknown finite binary semi-directed LSA-rootable, outer-labeled planar, galled network, arbitrary finite levels and blob counts. Exact oracle returns all distinct displayed quartet topologies. Return one common circular order and complete displayed split union. Existing admitted-source known-order sparse recovery is reused after the order stage.

## New candidate bound

If the affine-space containment premise in Section 4 holds, the order stage has an adaptive O(n^2 log n) query algorithm. This improves the inherited O(n^3) upper bound without changing source scope. It does not match the inherited Omega(n log n) adaptive lower bound.

## 1. Anchored adjacency certificate

Fix anchor r and candidate linear order L of Y=X minus {r}. Query {r,a,b,c} for every adjacent unordered pair {a,b} of L and every third c in Y. Reject L whenever a supported rooted topology places its forbidden middle taxon between its other two taxa in L. There are at most (n-2)(n-3) distinct quartet queries, with caching.

This certificate is complete for any family F of binary trees. Necessity follows because a rooted clade interval cannot contain two taxa while excluding a taxon between them. For sufficiency, a noninterval rooted clade C in some tree has a left run ending at a, its immediate successor b outside C, and a later member c of C. The triple a,b,c displays ac|rb and its quartet is queried through adjacent pair {a,b}. It forbids b as the middle. Thus every noninterval clade is detected.

## 2. Binary reference tree and XOR constraints

Let T be a binary rooted tree on Y such that every true common linear order is a planar leaf order of T. T need not be an actually displayed tree. Associate a flip bit with each of its n-2 internal vertices. Its planar leaf orders are exactly the assignments of these bits, after fixing child labels once.

For distinct x,y,z, T restricted to that triple has two branching vertices: v=LCA(x,y,z), and w=LCA of T's paired taxa. The middle taxon in a planar order of T is one of the paired taxa, and which one it is depends only on the XOR of the two vertex flip bits, with a fixed taxon-dependent sign. Therefore every anchored support answer, restricted to the embedding space of T, is either tautological, one signed equality between v and w, or inconsistent.

Inconsistency cannot occur under the stated containment premise, since a true common order exists and embeds T. If the oracle has two topologies neither matching T's rooted triple, it would forbid both possible middle taxa of T, so this answer is impossible. A singleton differing from T, or a doubleton containing T, imposes exactly one parity equation. A singleton matching T imposes none.

Signed union-find on the internal vertices represents all observed parity equations. If the current candidate order violates a queried answer, its two branching vertices belong to distinct parity components: otherwise the imposed equality would already hold in every component orientation. Consequently every failure merges two components. There are at most n-3 effective merges.

## 3. Adjacency caching and amortization

Maintain an explicit planar leaf order of T satisfying the observed equations. After an effective parity merge, flip the entire smaller union-find component if required. Every internal vertex is flipped at most floor(log2(n-2))+1 times, since its component size at least doubles whenever it is on the smaller side of a merge.

Flipping one tree vertex swaps two contiguous child blocks. It changes at most three undirected adjacent leaf pairs in the full linear order, regardless of block sizes. Process simultaneous flips sequentially to preserve this bound. The total number of distinct adjacent pairs ever encountered is therefore at most

    (n-2) + 3(n-2)(floor(log2(n-2))+1).

For every adjacent pair ever encountered, cache the oracle answers for all third taxa. The orientation of the pair or its global location can change; answers are cached, but the forbidden-middle test must be reevaluated in the current order. Check the current order using the complete adjacency certificate, repair the first violated relation, and repeat. At most n-3 failures occur. Once no failure exists, the current order is truly common to F.

Thus the repair phase uses O(n^2 log n) oracle queries. Finding witnesses and rechecking cached answers may use greater computation; this packet currently claims query complexity, not an O(n^2 log n) runtime.

## 4. Obtaining a valid reference tree: precise unresolved premise

Keijsper–Pendavingh's anchored cyclic-vector construction represents an exact support answer by affine signed equalities on C(n-1,2) pair-comparison variables. True common orders satisfy every queried equation.

Start with no equations. While the current affine solution space has a nontransitive assignment, choose one directed 3-cycle in its induced tournament and query the anchored quartet on that triple. A correct quartet answer excludes that assignment, since every true common order is transitive and obeys the answer. Hence at least one independent equation is added. After at most C(n-1,2) queries, every remaining assignment is transitive.

The missing premise needed for the candidate algorithm is:

> Every nonempty reversal-closed affine space of pair-comparison vectors, each of whose assignments is transitive, is contained in the planar leaf-order space of some binary rooted tree T.

An exact level-one / PC-tree representation theorem for such affine spaces would supply T by taking a suitable binary refinement of its ordered internal nodes. This must be checked for arbitrary sparse queried quartet systems, rather than assumed from a theorem about full dense tree/network data. If true, the initial cycle-witness phase costs O(n^2) queries and Section 3 gives the announced total.

## 5. Known failures explicitly avoided

An oracle triple need not equal the restriction of the final PQ-tree order space. For instance, rooted binary T1=((a,b),(c,d)) and T2=(a,((b,c),d)) admit only order a,b,c,d and its reversal, because clades ab,bc,cd must be intervals. Yet both display rooted topology cd|a on a,c,d. The oracle allows d as middle; no full common order does. Thus direct induced-PQ restriction queries are unavailable.

A fixed-anchor oracle does not determine complete split support: use the inherited admitted level-two N1/N2 collision. The reference tree and parity phase recover an order; a separate unrestricted known-order sparse recovery phase remains necessary.

## Prior and verification

Read inherited EXACT-QUERY-01 ORDER-AND-RECOVERY-THEOREM, ANCHOR-COLLISION, LOWER-BOUND and ORDER-ATTACK, as well as source all-level scope. Keijsper–Pendavingh affine representation is being checked by the primary-prior subagent. No historical priority is asserted for any parity or interval observation.

Actual verification at this checkpoint: hand derivation only. The code controls below are still to be implemented. Primary-source containment premise is pending and is the next mathematical decision.

## Correction and finite evidence (same session)

The unrestricted affine premise in Section 4 is FALSE. Primary-prior reviewer supplied circles (0,1,2,3,4) and (0,2,4,1,3), together with their reversals. Their four cyclic vectors form a dimension-two reversal-closed affine space, yet the circles have no common adjacent pair. No five-taxon binary tree can be common to both, because every nontrivial split is a 2|3 split and its two-taxon side must be adjacent. This rules out a generic all-cyclic-affine representation shortcut.

The weaker SOURCE-REALIZABLE premise remains under investigation:

> U(Q) arises by querying complete topology support of a nonempty family of binary trees with a common circular order. If every assignment in U(Q) is transitive, is U(Q) contained in the embedding-order space of some binary tree?

Independent exact finite controls in this subagent passed: all valid five-taxon support unions (105 distinct anchored profiles, every query subset, 627 all-transitive partial spaces); all families compatible with the fixed six-taxon circle (110 distinct anchored profiles, every query subset, 35,397 all-transitive partial spaces). Every passing partial space had a containing binary tree, found by exhaustive comparison with graph-generated binary-tree embedding orders. These finite controls do not prove the weaker premise. The generic counterexample singleton table cannot arise as complete support of any binary-tree family, because it admits no supported tree selection.

The repair algorithm in Sections 1-3 is unaffected: it is valid whenever a containing binary reference tree has been established. Overall source-uniform O(n^2 log n) remains conditional, rather than a proved upgrade.
