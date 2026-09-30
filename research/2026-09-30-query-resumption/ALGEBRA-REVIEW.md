# Independent review of the anchored signed-graph order learner

Contributor: Codex algebra-audit subagent, ALGEBRA-AUDIT-20260930.
Date: 2026-09-30 UTC. Status: hand-derived proof checked against governing primary prior; implementation review pending until the implementation is available. No Lean certificate and no claim of historical novelty.

## Review verdict and scope

The proposed learner is mathematically sound for every nonempty family of binary unrooted trees on the same finite taxon set. Its signed-graph solutions encode exactly the circular orders common to every tree. An inconsistent signed graph certifies that no such common order exists. For a family admitting a common order, every component-bit assignment is transitive, so choosing component seeds arbitrarily is safe. There are at most n-2 components, and at least one for n>=3.

This provides a concrete polynomial construction for the common-order component of the master recovery problem. It does not determine the full displayed split union from anchored data: the pinned [admitted level-two collision](../2026-09-30-root-exact-query/ANCHOR-COLLISION.md) is unchanged. It also does not close optimal adaptive query complexity; the learner reads all C(n-1,3) anchored queries.

## Governing prior inspected

J. C. M. Keijsper and R. A. Pendavingh, *Reconstructing a phylogenetic level-1 network from quartets*, arXiv:1308.5206v1, 2013. Primary full text: <https://arxiv.org/html/1308.5206v1>.

Theorem 7 supplies fixed-anchor equality of the quartet solution space and the compatible-order space for a binary level-one network. Lemma 8 gives the anchored pair-coordinate parametrization. Section 4.6 gives the actual signed auxiliary graph, even and odd edges, component seed assignments, and component-indicator affine basis. Theorem 8 already bounds the dimension of any cyclic affine reversal-closed space by n-2. These are established fundamentals. Applying the tree instance and intersecting its solution spaces is a direct extension to arbitrary tree families; it must not be advertised as a novel GF(2) method.

The proof below is elementary and independently exposes why the tree-family extension is valid. It does not rely on a claim that a higher-level source network itself is a level-one network.

## Exact representation and signs

Fix a taxon r and a reference label ordering on Y=X minus {r}. Cut a candidate directed circle immediately after r. For distinct a,b in Y let v_ab=1 if a appears before b in the resulting linear order, with v_ba=1+v_ab over GF(2).

Store one variable w_{ab} for each unordered pair, using a<b. Then

    v_ab = w_{min(a,b),max(a,b)} + epsilon(a,b),
    epsilon(a,b) = 1 if a>b, and 0 otherwise.

A supported anchored quartet xy|rz imposes

    v_zx = v_zy,

equivalently the signed graph edge

    w_{min(z,x),max(z,x)} + w_{min(z,y),max(z,y)}
      = epsilon(z,x) + epsilon(z,y).

Indeed, the quartet is noncrossing in (r,L) exactly when z is outside the interval between x and y in L. This is precisely equality of the two ordered comparisons. For sorted a<b<c the signs are:

| Supported quartet | Equation | Edge parity |
|---|---|---|
| ab\|rc | w_ac = w_bc | 0 |
| ac\|rb | w_ab + w_bc = 1 | 1 |
| bc\|ra | w_ab = w_ac | 0 |

All supported resolutions, rather than only one chosen resolution, must be inserted. Exact topology support is the oracle semantics. Statistical absence or a low observed probability cannot replace exact absence.

## Elementary proof for one binary tree

Root an unrooted binary tree T at the neighbor of r and omit leaf r. This is a rooted full binary tree on m=n-1 leaves. For each internal node p let A_p,B_p be its two nonempty child-clade leaf sets. Its cross-child unordered pair set is

    E_p = { {a,b} : a in A_p, b in B_p }.

These sets partition all unordered pairs: the least common ancestor of a,b is the unique p whose E_p contains {a,b}.

**No equality edge joins different E_p.** If T displays xy|rz, the rooted triple on x,y,z groups x,y. Therefore LCA(z,x)=LCA(z,y), and both comparison variables linked by the equality belong to the same E_p.

**Each E_p is connected by equality edges.** Fix b in B_p. For any distinct a,a' in A_p, their common ancestor is strictly below p, so T displays aa'|rb. Its equation v_ba=v_ba' joins their cross-child comparison variables. Analogously, fixing a in A_p and varying b,b' in B_p gives bb'|ra and v_ab=v_ab'. These moves connect the complete bipartite grid A_p times B_p. The argument still works when either child clade is a singleton: that direction requires no move. When both are singletons E_p itself has one vertex.

Thus the signed graph for T has exactly m-1=n-2 connected components, one per rooted internal node. The prescribed signs are consistent, as any recursive child ordering of T supplies a witness.

Choose the left/right orientation of each internal node independently. This assigns the same ordered cross-child relation throughout E_p and realizes every component seed assignment. Recursively listing the first child then the second child produces a linear order L in which every rooted clade is consecutive. Hence (r,L) is compatible with every split of T. Conversely, any such compatible circle makes all rooted clades intervals and satisfies every anchored quartet equation. It induces the child orientations and therefore one of these assignments.

Consequently the complete affine solution space for T consists exactly of its compatible directed circular orders. In particular all its assignments are transitive.

## The arbitrary-family theorem

Let F be any nonempty family of binary unrooted trees on X. Each equality added by the support oracle comes from at least one T in F, and all equalities for every such T are included. Therefore, as sets of pair-coordinate assignments,

    Solutions(F) = intersection over T in F of Solutions(T).

Each solution of this intersection lies in the solution space of any fixed T0 in F; by the one-tree proof it is transitive and encodes a unique directed circle based at r. It lies in every other tree's space exactly when that circle is common to the entire family. This proves the claimed exact characterization, for arbitrary finite family size and arbitrary source-network level or blob count whenever the source's displayed trees are binary and share a circle.

Adding equations only merges components or creates a contradictory parity cycle. A consistent graph therefore has d<=n-2 components. Flipping all pair bits reverses the directed circle and preserves every equation; for n>=3 the pair-variable set is nonempty, so d>=1. The number of directed common circles based at r is exactly 2^d. Quotienting by reversal gives exactly 2^{d-1} undirected common circular orders.

## Off-promise and incomplete-input behavior

There is a useful stronger transitivity statement. Suppose an arbitrary supplied anchored table lists at least one resolution on every triple of Y. A solution orients the complete graph on Y. A directed three-cycle makes each vertex's two comparisons unequal. Any listed quartet on that triple requires one such pair of comparisons to be equal, a contradiction. Thus no directed three-cycle is possible; a tournament without a directed three-cycle is transitive. Every signed-graph solution is consequently a linear order compatible with every listed anchored quartet, even if the table is not realizable as a tree family.

For this dense anchored-table contract, a parity contradiction certifies absence of an order obeying all listed constraints. A consistent graph yields such an order. Neither outcome alone decides whether an arbitrary table is the exact support union of an admitted source network. The tree-family theorem is what connects these order constraints to all its full splits.

If some anchored triples have an empty support set or are unqueried, arbitrary seed assignments need not be transitive. On Y={a,b,c}, an empty triple set imposes no equations, and the assignment a<b, b<c, c<a is a directed cycle. The implementation should reject empty masks for the complete binary-support contract, or explicitly return a partial constraint space instead of claiming that every assignment encodes an order. This distinction matters for noisy data and partial adaptive acquisition.

## Solver and resource obligations

There are V=C(n-1,2) graph vertices and at most E=2*C(n-1,3) edges on a compatible exact table, since three supported resolutions on one quartet would exclude every circle. A parity BFS/DFS with stored adjacency takes O(V+E)=O(n^3) time. Each connected component has one free bit. A conflict means a closed graph walk has odd total parity. A root path plus the conflicting edge provides an independently checkable inconsistency witness.

A union-find parity implementation takes O((V+E) alpha(V)) in its standard worst-case amortized analysis, rather than a literal O(n^3) bound unless the slowly growing factor is explicitly suppressed. The observed rooted-family structure can still be used to bound storage or implement graph traversal. Order extraction from the transitive comparisons takes O(n^2), for example by counting predecessors of each taxon and using those distinct counts as its rank.

The compact graph represents all assignments without enumerating 2^d circles. Enumerating all circles is exponential output work, and should remain an optional small-instance control. A claim that the representation recovers the full split union would be contradicted by the source-admitted anchor collision.

## Actual checks and remaining review

- Read local AGENTS.md, START-HERE.md, the completion standard, the anchored common-order proof, and the source-admitted anchor collision.
- Independently opened and inspected the primary paper, including Theorem 7, Lemma 8, Theorem 8 and signed graph construction in Section 4.6.
- Checked the proof, signs, binary-root node count, arbitrary-family quantifiers, reversal multiplicity and incomplete-input limitation above by hand.
- Implementation review and additional exact controls will be appended after the root's implementation is available. This file does not claim those checks already ran.

## 11. Process-integrity assessment

The governing prior is explicit, and the main higher-level step is proved through individual binary trees instead of misapplying a level-one theorem directly to a higher-level network. This is a mathematical proof review, not a systematic clinical review; AMSTAR-2 and RoB-2 scores would be inapplicable. Remaining reproducibility work is to pin the implementation and actual exact-control receipt.

## 12. Inference-robustness assessment

The order theorem is exact and does not involve estimated effect sizes or a statistical meta-analysis. Its main fragility is observation semantics: incomplete or noisy support breaks the complete dense input contract, while anchored data remain insufficient for the full split output. The arbitrary-tree-family intersection and node-by-node proof expose the all-size generalization; finite controls alone cannot establish it. Optimal adaptive recovery remains open and requires a new query strategy or a stronger admitted lower bound.
