# A fixed anchor does not determine complete displayed split support

2026-09-30 UTC. Contributor: query lower-bound/source-admission subagent, using the root researcher's two enumerated occurrence-tree candidates. Status: explicit exact finite graph certificate with executed source validation and switching enumeration; hand-derived extension to every n>=5. No whole-class optimal-query closure, Lean verification, or historical novelty claim.

## Theorem

For every n>=5 and every specified anchor taxon r, there are finite binary semi-directed LSA-rootable, outer-labeled planar, galled networks N1,N2 on the same n taxa, each of level at most two, such that:

1. Their complete distinct displayed-quartet support agrees on **every** four-taxon set containing r.
2. Their unions of displayed-tree splits differ.
3. They admit the same compatible circular order.

Consequently, even all O(n^3) quartet support queries containing one fixed anchor cannot universally recover the full split union. The obstruction persists when a correct compatible circular order is additionally supplied. It does **not** say that anchored data cannot recover some compatible order, or that adaptive unrestricted queries require superlinear complexity.

## Explicit five-taxon witnesses

Taxa are 0,1,2,3,4; r=0. Each graph has ordinary vertices U0,...,U4, two hybrids, and pendant taxa T0,...,T4. The root R subdivides the ordinary taxon-4 pendant edge. The root is suppressed to obtain the semi-directed network.

Ordinary tree-skeleton and taxon edges:

| Graph | Skeleton edges | Ordinary pendant attachments | Hybrid parents and child |
|---|---|---|---|
| N1 | R-U0, U0-U1, U1-U2, U2-U3, U2-U4 | R-T4, U1-T3, U4-T2 | U0,U3 -> H0 -> T0; U3,U4 -> H1 -> T1 |
| N2 | R-U0, U0-U1, U1-U2, U2-U3, U1-U4 | R-T4, U3-T1, U4-T3 | U0,U2 -> H0 -> T0; U3,U4 -> H2 -> T2 |

These can be independently reconstructed by folding the adjacent pairs of the root's ordered occurrence-tree candidates:

```
N1 tips = (0,0,1,1,2,3,4)
topology = (0, ((((1,2),(3,4)),5),6))

N2 tips = (0,0,1,2,2,3,4)
topology = (0, (((1,(2,3)),(4,5)),6))
```

Topology integers name physical occurrences, not taxon labels. The two occurrences of each duplicated taxon have distinct parents, so folding produces no parallel incoming edges.

## Explicit source admission

Orient the ordinary skeleton away from R; orient the listed hybrid edges from their two parents into the hybrid, and the child edge towards its taxon. R has indegree/outdegree (0,2), ordinary internal vertices (1,2), hybrids (2,1), and leaves (1,0). The skeleton is a tree and every hybrid child is a pendant taxon, so there is no directed cycle. R's direct child T4 lies in one root branch, while all other taxa lie in the other; hence R is the LSA of all taxa.

Each hybrid has a cycle consisting of its two incoming edges and the ordinary skeleton path between its parents. This cycle contains no other hybrid. Its outgoing pendant child edge is a bridge, establishing the source's galled condition. Both hybrids lie in the one nontrivial level-two blob.

For outer-labeled planarity, use the cyclic rotations below. Degree-one taxon rotations are their unique neighbor; R has rotation (U0,T4).

| Vertex | N1 rotation | N2 rotation |
|---|---|---|
| U0 | (H0,U1,R) | (H0,U1,R) |
| U1 | (U0,U2,T3) | (U0,U2,U4) |
| U2 | (U1,U3,U4) | (U1,H0,U3) |
| U3 | (U2,H0,H1) | (U2,T1,H2) |
| U4 | (U2,H1,T2) | (U1,H2,T3) |
| H0 | (U0,T0,U3) | (U0,T0,U2) |
| Other hybrid | H1:(U3,T1,U4) | H2:(U3,T2,U4) |

Tracing successor darts gives 3 faces in each connected graph, with V=13,E=14 and V-E+F=2. One face encounters all five taxa in order (0,1,2,3,4). This is an exact combinatorial planar embedding certificate, rather than an inference from an attractive drawing. Suppressing R on its ordinary edge preserves that embedding and circular order.

## Exact oracle collision and different output

Enumerating the four independent hybrid choices in each graph, pruning unlabeled dangling branches and suppressing degree-two vertices, gives:

| Quartet taxa | N1 support | N2 support |
|---|---|---|
| 0123 | {01\|23, 03\|12} | {01\|23, 03\|12} |
| 0124 | {01\|24, 04\|12} | {01\|24, 04\|12} |
| 0134 | {01\|34, 04\|13} | {01\|34, 04\|13} |
| 0234 | {02\|34, 04\|23} | {02\|34, 04\|23} |
| 1234 | {12\|34} | {12\|34, 14\|23} |

N1 has three distinct displayed trees; N2 has four. Their split unions differ in exactly one split:

`SplitUnion(N2) = SplitUnion(N1) union { {2,3}|{0,1,4} }`.

This is also the boundary-quartet test in their common circular order: the split has consecutive boundary gaps (1,2),(3,4), so it is displayed exactly when 23|14 is present on quartet 1234. All four anchored quartet answers agree, while the required split output differs. Any deterministic algorithm confined to those anchored queries receives the same transcript and must fail on at least one graph.

## Extension to every larger finite taxon count

Replace the ordinary taxon 4 in both witnesses by the same fixed rooted binary tree on n-4 new taxa. Glue its root attachment at the former pendant edge and retain the original hybrid arrows. Tree grafting preserves binary degrees, the existing level-two blob, galledness and outer-face planarity. A rooted LSA partner exists by placing the root on any ordinary pendant edge in the grafted tree: one root branch is its direct leaf and the other contains all remaining taxa; ordinary skeleton edges orient away from it.

For an anchored quartet containing no grafted taxon, the original anchored support is unchanged. For exactly one grafted taxon, contract its pendant subtree path: its support is the original answer with 4 replaced by that taxon. For two grafted taxa and one other nonanchor taxon, the attachment cut edge resolves their pair against the two outside taxa. For three grafted taxa, the quartet is determined by the fixed grafted tree and its attachment to the outside anchor. Thus all anchored supports still agree.

The split {2,3}|all remaining taxa continues to be displayed in N2 and absent in N1. Restricting a hypothetical N1 tree displaying it to 0,1,2,3 and one grafted leaf would display 23|14, contradicting the explicit original support. Relabeling places any specified r at taxon 0. This proves the theorem for every n>=5.

Five taxa is minimal for this fixed-anchor obstruction: on four taxa the anchored query family contains the entire quartet support, which directly determines all nontrivial split support.

## Execution and limits

Run `python check_anchor_collision.py` from this packet's directory. It constructs the actual graphs, searches the four hybrid rotation choices, and calls the preserved inherited exact graph validator at `inputs/exact_networks.py`, copied unchanged from the normalized recovery input. The executed validator checks connectivity, degrees, rotation/Euler/outer face, rooted-partner indegrees/outdegrees, DAG, LSA by dominators, bridges/galledness and blob hybrid counts. Exact graph switchings separately produce the support masks and displayed split unions.

Receipt: `anchor-collision-receipt.json`, status PASS. Full masks in lexicographic quartet order are 7021 and 23405; their anchored lower twelve bits agree at 2925. The source-validator SHA256 is recorded in the receipt. No floating point enters these checks.

This is a bounded obstruction to a specific observation restriction. It leaves the whole-class adaptive query master open. In particular, recovering a compatible order from anchored information and then making additional unrestricted sparse queries is fully consistent with this result.
