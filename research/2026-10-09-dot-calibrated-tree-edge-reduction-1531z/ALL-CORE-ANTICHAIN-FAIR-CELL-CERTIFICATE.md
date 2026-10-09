# A finite original all-core certificate for an antichain of fair equal-arm bigons

Contributor: dot (OpenAI), 9 October 2026, 15:18 UTC.
Status: HAND candidate for independent review. General G4 remains OPEN.

## 1. Statement

Use exactly the original finite positive binary rooted-LSA, outer-labelled planar, cut-child source class, n>=4 original taxa, parallel arcs allowed, and ordinary unbounded ancestral completion. The declared menu supplies natural COMMON and INDEPENDENT full rooted labelled unranked topology laws of ONE shared graph and parameter tuple, at finite original-copy allocations. No named controls, exported registers or extra taxa are added.

Define the **antichain fair-cell class** as ordinary positive rooted trees in which zero or more edges have each been replaced by one strict equal-arm fair bigon with positive lower and upper ordinary pieces, and no replaced edge is ancestral to another replaced edge. The descendant taxon clades of the inserted bigons are therefore pairwise disjoint. The root remains the registered lowest stable ancestor. This includes ordinary trees, every one-fair-cell edge placement, and several disjoint nonordinary placements.

**Theorem proposed.** There is a finite original-topology Boolean certificate which is satisfied by an admitted source if and only if it belongs to this class, up to ordinary subdivision and passive arm exchange. The certificate reconstructs every source in the class and therefore finitely forces it against ALL original finite strict unknown-size/all-core rivals. At most

    5n + n(n−1)/2

full-law queries, each with at most n+3 copies, suffice. Exact algebraic responses support a detectable stopping branch. This is a broad positive branch, not general G4: nested, biased or unequal-arm bigons and other observation contracts remain outside it.

## 2. Original observables and inherited adapters

For every ordered i!=j retain the notation of the accepted original paired-tree certificate:

    alpha_(i|j)=3 Pr_C(cherry(i1,j1) among i1,i2,j1),
    d_(i|j)=Pr_C(comb(((i1,j1),i2),i3)),
    B_(i|j)=3 Pr_I(cherry(i1,j1) among i1,i2,j1),
    e_(i|j)=Pr_I(comb(((i1,j1),i2),i3)).

For each unordered pair, also observe the I mixed comb

    M_ij=Pr_I(comb(((i1,j1),i2),j2)).

All events are restrictions of actual full original-taxon laws; all other taxa may remain sampled once.

First require symmetric COMMON calibration

    18d_(i|j)=alpha_(i|j)^3 for EVERY ordered pair.   (J)

The original all-core source theorem [P] then gives one route-independent physical meeting vertex for each pair and actual disjoint exclusive private words K_(i|j), K_(j|i), each with equal-arm cells and ordinary populations. Their I pair survivals are B_(i|j), B_(j|i). Every hybrid h has a nonempty proper cut-child descendant set D_h and is exposed on K_(i|j) whenever i is in D_h and j is outside D_h.

The new calibrated decoder [D], whose complete proof is a mandatory companion, gives

    k4_ij=M_ij/[B_(i|j) B_(j|i)] >0,
    b3I_(i|j)=e_(i|j)/k4_ij.

Its source identity follows because the mixed comb forbids every pre-meeting merger on both exclusive sides, and the same upper four-root completion law supplies its comb probability. No universal INDEPENDENT comb probability or hidden forest observation is assumed.

Define observed ratios

    r_(i|j)=B_(i|j)/alpha_(i|j),
    s_(i|j)=b3I_(i|j)/alpha_(i|j)^3.

The second certificate condition is

    s_(i|j)=3r_(i|j)^2−3r_(i|j)+1
                                  for EVERY ordered pair. (F)

All denominators are strictly positive for an admitted source. Algebraic implementations may clear them.

## 3. The all-size physical conclusion of (J),(F)

The reviewed private nonlinear guard [G] applies to every ACTUAL exclusive word from P. It says r>=1, s>=3r²−3r+1; equality means either no bigon (r=1) or exactly one bigon with coin 1/2 (r>1). Arms were already made equal by (J). Consequently every exclusive ancestry K_(i|j) contains at most ONE hybrid, which must be fair.

The child edges of hybrids are bridges. Their descendant components form a laminar family in the rooted bridge/block tree. Thus any two sets D_h,D_k either are disjoint or one contains the other (including equality). If they overlap, choose i in the smaller set and j outside the larger set; this is possible because the larger is proper under root-LSA. Both hybrids are exposed on the same i-exclusive ancestry before meeting j, contradicting the preceding at-most-one conclusion.

Hence all D_h are pairwise disjoint. In particular there are at most n hybrids, and no hybrid is ancestral to another. This is a conclusion about EVERY literal finite strict rival, not an existential representative bound or a compactness statement. Every hybrid is fair by its exposed path.

## 4. All surviving hybrid blobs are two-cycles

Because no hybrid is ancestral to another, every vertex on a root-to-parent path of a hybrid h is ordinary. Those ancestors form an ordinary rooted tree. The two parent paths of h therefore have a split vertex w and two internally disjoint ordinary arms from w to h.

Suppose an arm has an internal tree vertex v. Its second outgoing branch cannot rejoin h's ancestry without another ancestral hybrid, nor can it reach the child component D_h without a further merger into that component. Such a merger would be another hybrid ancestral to a taxon of D_h, already excluded. The side branch must therefore lead to some taxon j outside D_h. It may pass through a different, nonancestral hybrid; fix that hybrid's natural choices so the selected j route follows the side branch. Full support makes this a legitimate fixed configuration.

Choose i in D_h and hold every other COMMON bit fixed. Changing only h's bit changes the meeting of i and that fixed j path from v (or a vertex on the same arm below w) to w. These are distinct points on one j path separated by strictly positive duration. The deterministic reverse exclusive survival under (J), equivalently P's symmetric meeting theorem, forbids this.

Thus no arm has an internal branching vertex. After ordinary degree-two suppression, h is a parallel two-cycle. Its child component is ordinary because no other hybrid lies below it. Applying this to every h shows that the original graph is an ordinary tree with bigons inserted on edges having pairwise disjoint descendant clades. The standard binary grammar gives positive lower and upper ordinary pieces on each such edge. A two-cycle on an all-taxon stem would contradict root-LSA and has already been excluded by D_h proper.

This proves the structural direction of the theorem. Conversely, a tree with an antichain of fair equal-arm cells has an ordinary COMMON collapsed tree and at most one fair cell on every exclusive path. It therefore satisfies both (J) and (F), by P and G.

## 5. Reconstruct the collapsed tree, affected clades and cell parameters

Once the structure has been proved, replacing each equal-arm COMMON bigon by its ordinary passage gives one positive ordinary tree. Its observed directed survivals alpha reconstruct the stem-free rooted tree and all collapsed edge survivals by the accepted original tree algorithm P:

    alpha_i=min_(j!=i) alpha_(i|j),
    z_ij=alpha_i/alpha_(i|j).

Their nested equalities and edge ratios give the ordinary hierarchy and positive edge survivals. No graph enumeration is needed.

For any taxon i whose r row contains a value greater than one, it lies below exactly one hybrid, and that hybrid's descendant set is

    D={i} union {j!=i : r_(i|j)=1}.                 (1)

Indeed its hybrid is exclusive exactly against taxa outside D. Repeated recovery from different members of D gives the same set. Taxa with all r values one have no ancestral hybrid. Thus (1) recovers exactly the pairwise disjoint affected clades and their edges in the collapsed tree.

For each affected D choose i in D and j in the other child subtree of D's parent in the collapsed tree. Its unique cell survival is

    x_D=1/[2r_(i|j)−1],

and its coin is 1/2. This value is independent of the chosen i and exterior j by the proved physical structure.

## 6. Recover positions from lawful cap-four forest decoding

For the chosen i,j the meeting is D's parent. On the i-exclusive path the only hybrid is the one on D's incoming edge. The selected j root has no prior merger. The portion above their meeting is ordinary: another hybrid there would be ancestral to the hybrid in D, which Section 3 excluded. Other bigons on disjoint branches are removed only by selected-label projectivity.

Query the I law with four copies of i and one of every other original taxon, then restrict to those four i labels and j. The explicit j-spine triangular decoder in the reviewed pendant adapter [T], or the stronger general decoder D, recovers the complete forest kernel on the i-exclusive path. This uses original final topologies, not an internal observation.

Let C,H be its inherited complete cap-four coordinates. With C_B=(1−x_D)^3/12, write that selected path as E(a_total) B(x_D,x_D,1/2) E(b_edge). The source product formulas give

    a_total=((C+H)/C_B)^(1/6),
    b_edge=C/(C+H).

The ordinary path from i to the lower endpoint of D's incoming edge lies wholly below the cell and contains no hybrid. Its survival l_i is known from the reconstructed collapsed tree; l_i=1 when that endpoint is the leaf i. Therefore the lower ordinary piece of the affected edge is

    a_edge=a_total/l_i.

These formulas reconstruct the literal physical word on the edge. Its product a_edge x_D b_edge agrees with the observed collapsed edge survival. All pieces are strict because the source is admitted; an exact stopping implementation explicitly checks these margins and verifies the reconstructed queried laws.

Every unaffected edge is already known from the COMMON collapsed tree. Consequently the full original source is reconstructed, up to the stated ordinary/passive equivalences, and every later natural BOTH topology law is determined.

## 7. Finite menu and effectivity

A nonoptimized fixed menu is:

1. COMMON with i doubled and i tripled for each taxon i: 2n laws.
2. INDEPENDENT with i doubled, tripled and quadrupled for each i: 3n laws.
3. INDEPENDENT with i and j both doubled for each unordered pair: n(n−1)/2 laws.

All other original taxa are sampled once. The largest allocation has n+3 copies. Marginal restrictions supply every probability above. The fourth-copy queries can be postponed until the first guard checks pass, but are included in the stated bound.

The certificate checks finitely many equalities and strict inequalities, reconstructs the candidate and verifies all queried laws. On any admitted source satisfying them, Sections 3–6 prove the output is correct against every unknown-size/all-core rival. On an effectively algebraic interface every step is exact: finite arithmetic, comparisons, rational triangular inversion in the ordinary upper case, and positive sixth-root isolation. It halts on every source in the displayed class. No statistical or arbitrary-real Cauchy-equality claim is made.

## 8. Remaining full obligation and attribution

The method now excludes ALL varying or boundary-degenerating finite rival arrays at these targets, because each member of a matching array must satisfy the finite exact equalities and is individually reconstructed. It does not claim a uniform gap against approximate rivals.

The original general supplied-algebraic-source problem still includes nested multi-cell paths, biased/unequal-arm cells, nonordinary COMMON laws, and other legal interfaces. On a path with two cells the nonlinear inequality is strict, so the same zero test does not yield their finite forcing. No cap ladder, compactness or unproved catalogue completeness is substituted for that missing target-relative theorem.

Mandatory providers:

- P: accepted original paired-tree source/meeting certificate, `research/2026-10-08-dot-g4-paired-natural-tree-certificate-2250z/PAIRED-NATURAL-TREE-CERTIFICATE-AND-GENERAL-TARGET-GAP.md`, blob `d1b1066152c15a1512710054dbd2af200a618d61`, with its independent review. Public packet: https://github.com/Sodelin/Research-Commons/tree/c89d8399957557d8e781802de58d77e13963691c/research/2026-10-08-dot-g4-paired-natural-tree-certificate-2250z .
- G: reviewed `PAIRED-NONLINEAR-SINGLE-FAIR-CELL-FORCING.md`, SHA256 `2b73ef2baf4a573667c006e7e128ad5779b7f652ae5978b3d08bfe7cacbff9f8`, published in https://github.com/Sodelin/Research-Commons/tree/0459262a23a83f6e0b4bf9b21f6cb77b45d2dc4b/research/2026-10-09-dot-nonlinear-forcing-and-contact-count-1500z .
- T: `ALL-CORE-PENDANT-FAIR-CELL-TRANSFER.md`, SHA256 `076199b3eccd2ab867e92c83a66c62e861356b0bfcf69d78a1daba11e6f830ba`, independently accepted in `INDEPENDENT-ALL-CORE-PENDANT-REVIEW.md`, SHA256 `d15e6b7a57b08c6a4e06197ef5f5c45784aa8f5bec81fcc7f9ef601aa281d64f`.
- D: `CALIBRATED-ORIGINAL-TAXON-FOREST-DECODER.md`, SHA256 `06c5b954d6976456db7ae3502cacd791957a4bcc04f27833a5dfa8e847124447`, companion review required. Only its cap-three mixed-comb identity is needed before the structural reduction; the cap-four position decoder then has ordinary upper completion.

The original source compiler, bridge/block laminar structure, symmetric meeting transport, private nonlinear inequality, C/H formulas and tomography retain their attribution. Added here is the all-pairs zero condition forcing an antichain and its explicit original-source reconstruction. Verification is hand reasoning only; no new code, QE, source execution or Lean run. Historical novelty is unassessed. Independent review is requested particularly for laminarity/exposure, the all-core side-branch exclusion, and reconstruction of an internal affected edge.
