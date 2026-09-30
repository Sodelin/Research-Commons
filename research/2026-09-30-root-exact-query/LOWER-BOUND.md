# Exact-quartet query attack: proved bounds and failed quadratic transfer

2026-09-30 UTC. Contributor: query lower-bound subagent. Internal hand proof plus explicitly executed finite controls. No historical novelty claimed for the tree lower bounds. No GitHub writes.

## Target

An unknown network is promised to be in the finite binary semi-directed LSA-rootable, outer-labeled planar, galled class, with arbitrary finite level and blob count. Query a four-taxon set and receive its complete set of distinct displayed quartet topologies. Recover the union of all displayed-tree splits and any compatible circular order. No order or tree of blobs is supplied.

## Theorem 1: adaptive worst-case lower bound

Every deterministic always-correct algorithm requires at least

`ceil(log_3((2n-5)!!)) = Omega(n log n)`

queries on some admitted n-taxon instance.

**Proof.** The class contains every unrooted binary labeled phylogenetic tree. A rooted binary partner can be formed by subdividing any edge; its root is the LSA because each root branch contains taxa. Trees are planar, outer-labeled planar and vacuously galled. There are `(2n-5)!!` such trees on n labeled leaves. Their complete split systems are distinct, so the requested output distinguishes all of them. On this subclass a quartet answer has exactly three possibilities. A deterministic decision tree of worst-case depth q has at most `3^q` terminal leaves. It therefore needs `3^q >= (2n-5)!!`. Stirling's bound gives the claimed order. Returning a circular order in addition cannot reduce this requirement. QED.

This bound does not establish a matching algorithm on higher-level networks, and does not exclude a quadratic or cubic true optimum.

## Theorem 2: nonadaptive worst-case lower bound with explicit admitted witnesses

Every deterministic always-correct nonadaptive algorithm requires at least

`ceil(C(n,3)/4) = Omega(n^3)`

distinct complete-support quartet queries, for n>=4.

**Proof.** For each triple A={a,b,c}, take a binary pendant three-leaf subtree attached by one edge to any fixed binary tree containing the other taxa. Build T1 with a,b as a cherry and T2 with a,c as a cherry. When only one outside taxon exists, attach the triple directly to that taxon. Both graphs are unrooted binary phylogenetic trees, hence admitted as in Theorem 1.

If a quartet omits at least one of a,b,c, its induced topology is the same in T1 and T2. With two of these taxa and two outsiders, the cut edge separating A from its complement fixes the quartet. With at most one inside taxon, the entire pendant subtree contracts to the same single terminal. If a quartet contains all of A and one outsider z, T1 returns ab|cz while T2 returns ac|bz, so the answer differs.

Thus a universal fixed query family must contain at least one quartet covering every three-taxon set A; otherwise T1,T2 have identical queried transcripts but different required split outputs. Each quartet covers exactly four triples. At least C(n,3)/4 queries are required. QED.

An anchored family consisting of all quartets containing one fixed taxon supplies the familiar O(n^3) tree bound. This known tree obstruction explains why a sparse whole-class method must genuinely use adaptivity; it is not a new network theorem.

## Executed witness controls

`python query-attack/check_hidden_triple.py` ran successfully. The independent graph/BFS/tree-four-point implementation checked 125 admitted tree pairs for n=4,...,8, comparing all 5,499 queried quartet pairs. Exactly 504 answers differed, always and only when the query contained the designated triple. The code verifies degree-one taxa and degree-three internal vertices. Receipt: `hidden-triple-controls.json`.

These controls corroborate the explicit all-size proof; they do not replace it or constitute a network-level adaptive quadratic lower bound.

## Published quadratic lower bound: why it cannot be imported here

Primary source: Frohn et al., *Reconstructing semi-directed level-1 networks using few quarnets*, arXiv:2409.06034v2, Proposition 6 and Figure 5 (PDF page 10), https://arxiv.org/pdf/2409.06034 . Published DOI: https://doi.org/10.1016/j.jcss.2025.103655 . Its lower bound is Omega(n log n+ell*n) for tree-of-blobs reconstruction using **quarnet splits** in a broader semi-directed class. Its Section 6 leaves an O(n^2)-O(n^3) query gap.

I downloaded and visually inspected its actual Figure 5. Each displayed blob has two tree-skeleton arms, with each of ell hybrid taxa receiving one parent incidence from each arm. Opening the pendant hybrids yields one occurrence of each hybrid taxon on each arm.

**Source exclusion lemma.** In an adjacent-copy plane tree, at most two duplicated labels can have one occurrence on each side of a fixed tree-edge split.

**Proof.** The edge cuts the cyclic leaf order into two intervals with two boundary gaps. An adjacent pair straddling that split must contain one of those gaps between its two occurrences. Distinct labels have disjoint occurrence pairs, so at most two pairs can do this. QED.

The Figure 5 opened skeleton has a tree edge separating the two arms. Every one of its ell duplicated labels straddles that edge. For ell>=3 this contradicts the necessary adjacent-copy representation of our source class. Thus its unbounded-level quadratic adversary is not admitted in the present outer-labeled-planar galled class.

A second independently transparent exclusion applies for ell>=4: select any four hybrid labels. For any of their three 2+2 partitions, retain the two labels on one skeleton arm and the other two on the other arm. The separating edge displays that partition. Therefore all three quartet topologies occur on those four taxa. An outer-labeled planar network's displayed quartet support has at most two topologies. This likewise rejects the Figure 5 family for the high levels needed by its quadratic scaling.

There is a separate oracle issue: lower bounds for the coarser quarnet-split answer do not automatically lower-bound algorithms receiving complete displayed support. The source explicitly warns that quarnets may differ outside the hidden pair even where quarnet splits do not. A transferred lower bound needs equality of the actual support-mask transcripts.

## Current obstruction, rather than a false quadratic theorem

I did not find an admitted adaptive Omega(n^2) adversary. Naive hidden-pair constructions require a common baseline with Theta(n^2) interchangeable pair modifications visible only when both pair taxa are queried. A binary tree has only O(n) cherries/edges, and a cycle refinement anchored to two singleton ports inherits that restriction. A saturated generic circular split family is also inappropriate: it may have Theta(n^2) supported splits and need not arise from adjacent-copy trees or the admitted network class. Neither is a valid whole-class lower bound.

The exact adaptive optimum for this admitted complete-support model remains unresolved by this lane. The rigorous progress is the adaptive information bound, explicit nonadaptive witness theorem/control, and decisive exclusion of the tempting published quadratic adversary. A matching whole-class adaptive algorithm, or a new admitted indistinguishable-support adversary, remains the actual research obligation.
