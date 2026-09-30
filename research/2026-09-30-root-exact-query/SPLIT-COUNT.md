# A linear bound on the complete displayed-split union

Date: 2026-09-30. Scope: a combinatorial interface for the sparse displayed-split algorithm. This note derives an explicit bound from the already audited source-to-occurrence-tree and tree-of-blobs representations. It does not claim historical novelty, metric identifiability, a new statistical observation model, or Lean verification.

## Statement

Let N be a finite binary semi-directed LSA-rootable, outer-labeled planar, galled phylogenetic network on n >= 4 taxa. Let k be the number of **distinct nontrivial unordered taxon splits** in the union of the split sets of all displayed trees. There is no bound on reticulation level, number of blobs, or length of chains of two-port blobs.

Then

    k <= 13n - 27.

Including all n singleton splits, the complete displayed-split union has at most

    14n - 27

distinct splits. More precisely, if q is the number of nodes of degree at least three in the reduced tree of blobs,

    k <= 8n + 5q - 17,     1 <= q <= n - 2.

These are deliberately loose universal bounds. They count distinct splits, not switched trees, graph isomorphism classes, physical tree edges, or multiplicities of switching choices.

## Inherited structural inputs

The source package at Samuel commit `e2502c82ab9a77c00543932f775a71e5374221f7` supplies the following level-independent facts:

1. Every cut edge has taxa on both sides. After contracting blobs and retaining the taxon leaves, the resulting tree therefore has no non-taxon leaves. Every non-leaf node has at least two ports. Singleton trivalent tree vertices are included as blobs.
2. Capping each incident cut edge by a distinct port leaf produces an admitted binary, LSA-rootable, outer-labeled planar, galled bloblet. Each port represents a nonempty entire taxon component; local and global switchings extend independently.
3. On a capped bloblet with m >= 3 ports, opening each hybrid into two copies of its child port gives a plane binary occurrence tree T. Each port label occurs once or twice, and its two occurrences are adjacent in the cyclic leaf order. Displayed local trees are precisely the trees obtained by independently choosing one occurrence for each duplicated label, taking the connecting subtree, and suppressing degree-two vertices.

Port labels are local terminals, not original taxon leaves. The bound below always lifts a port split by replacing each port with its entire attached taxon component. No tree-child assumption is added.

Locators:

- [ALL-LEVEL-STRUCTURAL-AUDIT.md, Section 2](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-STRUCTURAL-AUDIT.md): adjacent-copy occurrence representation and switching correspondence.
- [ALL-LEVEL-COMPOSITION-AUDIT.md, Sections 2 and 3.2-3.3](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-COMPOSITION-AUDIT.md): positive port components, capped-source admission, independent local switchings, and provenance of global branching vertices.
- [ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md, Section 4](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md): every displayed global split has a local branching-endpoint source, including bridges and two-port chains.

The present cardinality argument uses these structural facts, not the finite coefficient or support-zero certificate for the NANUQ metric.

## Local count

Fix one capped bloblet on m >= 3 port labels. Let h be its number of duplicated labels. Its plane binary occurrence tree has

    M = m + h <= 2m

physical tips, and exactly M - 3 internal edges.

For a physical edge e, either side of its occurrence split is a cyclic interval in the plane tip order. Its two boundary gaps can split at most two duplicated-label blocks: a duplicated label has occurrences on opposite sides only when one of those two boundaries falls between its adjacent occurrences. Every other label has all its occurrences on one fixed side.

After selecting one occurrence for every label, therefore, at most two labels have variable side membership. Edge e can induce at most 2^2 = 4 distinct port bipartitions over all selections. Empty sides are discarded, and forgetting orientation can only reduce the count.

Every edge of a displayed local tree comes from a nonempty path of physical edges of T. Choosing any physical edge on that path recovers the same bipartition of the selected labels. A nontrivial port split has at least two labels on each side, so its physical witness cannot be a pendant occurrence edge: a pendant edge has only one occurrence on its tip side.

Consequently every distinct nontrivial displayed local split is induced by some internal physical edge, and their total number is at most

    4(M - 3) <= 8m - 12.                         (L)

This counts the full union over all switching choices. It does not assume that those splits occur simultaneously in one displayed tree.

## Reduced tree of blobs

Contract every blob of N, retaining each taxon as a leaf, to obtain the tree of blobs. Suppress all non-taxon degree-two nodes to obtain R. A suppressed node can represent an arbitrarily complicated two-port blob; suppression here concerns only the tree of attachments, not deletion of its network structure.

R has n taxon leaves and q interior nodes, each of degree m_B >= 3. Suppression changes neither the degree of a retained node nor the taxon bipartition of an edge along a suppressed chain. The degree sum gives

    sum_B m_B = n + 2q - 2.

Since every m_B >= 3,

    q <= n - 2.

The n >= 4 leaf tree has q >= 1. Its edges total n + q - 1; exactly n are pendant taxon edges, so exactly q - 1 are internal edges. Every original bridge partition, including every partition along a chain of two-port blobs, is represented by one edge of R. A degree-two blob's local displayed tree is the unique two-terminal tree and supplies no additional bipartition.

## Every global split is accounted for

Consider a nontrivial split S of a displayed global binary tree. Its defining edge has a degree-three endpoint v. Deletion, recursive pruning and degree-two suppression create no new branching vertices, so v is an original tree vertex of one blob B.

Each of the three global taxon branches at v exits B through at least one port. A port's attached taxon component lies wholly in one branch, so these three branches require at least three distinct ports. Thus B is one of the q retained branching nodes of R, and v survives as a branching vertex of the corresponding local displayed tree.

Take the local edge leaving v in the direction of the global edge. There are two possibilities:

- It is a pendant local edge. Its lift separates one entire port component from its complement. This is an original bridge partition, hence an edge partition of R. Because S is nontrivial, it corresponds to an internal edge of R.
- It is an internal local edge. Its split is nontrivial on the port set, and S is its lift by whole port components. It is counted by (L).

If the global edge represents a suppressed path crossing two-port blobs, the same branching-endpoint argument applies. Those blobs add no branch along the path, and their bridge partitions remain the same partition. No assumption that a hybrid's child port is a single global taxon is used.

Therefore the global nontrivial displayed-split union is contained in the union of the q - 1 internal bridge partitions and the lifted nontrivial local unions from retained branching blobs. Different local splits may lift to the same global split; counting them separately is a valid upper bound.

## Aggregate bound

Using (L),

    k <= (q - 1) + sum_B (8m_B - 12)
      = (q - 1) + 8(n + 2q - 2) - 12q
      = 8n + 5q - 17
      <= 13n - 27.

All n singleton taxon splits occur in every displayed tree, so the total displayed-split union has at most 14n - 27 elements.

The arbitrary level and blob-count quantifiers enter only through the inherited structural representation. Unbounded chains of two-port blobs disappear from the attachment-tree count because they create no new taxon bipartitions.

## Algorithmic consequence and limits

For the complete displayed nontrivial split union of this source class, k is O(n). Thus an exact-oracle algorithm already proved to use O(n + k log n) queries has an O(n log n) specialization, under that algorithm's separate assumptions, including a supplied correct common circular order. This is not an algorithm for estimating that order, not an all-level biological quartet observation guarantee, and not a network-reconstruction or novelty claim.

## Verification status

This is a hand proof based on pinned structural arguments, not an inference from finite graph screens. An independent conditional proof audit by `split_count_review` accepted the bound, arithmetic, and treatment of two-port chains. That reviewer supplied an alternative decomposition: represent a surviving displayed-tree edge by an original edge before pruning and suppression; an original bridge gives a bridge partition, while an edge inside a blob partitions its ports. An empty port side cannot survive, a singleton port side is an incident bridge partition, and at least two ports on each side gives a local nontrivial split. This independently corroborates the branching-endpoint accounting above.

The reviewer did not independently reverify the pinned source-admission lemmas. This note is therefore an internally reviewed hand proof conditional on those stated structural inputs, not a complete Lean certificate or external review. No computational test is needed to establish the asymptotic cardinality bound; implementation checks of a particular split enumerator are a separate task.
