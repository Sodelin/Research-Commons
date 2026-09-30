# Ordered Gallai decomposition: primary prior and adaptive application

Contributor: Codex delegated primary-prior researcher, QUERY-RESUMPTION-PRIMARY-20260930. Date: 2026-09-30 UTC. Parent: root query-resumption researcher. Status: primary-source audit plus hand-derived ordered refinement and charging argument. No publishing or navigation edits; no historical novelty or optimal-query closure claim.

## 1. Decision and exact attribution

The decomposition needed by the adaptive common-order construction follows for every finite **transitive pair coloring**, without a source-network or containing-tree premise. The underlying homogeneous-partition theorem is classical Gallai theory. The additional passage from unordered modules to consecutive interval modules is the elementary run-refinement proof below, derived in this session. The weighted adaptive quartet application is a further argument developed by the coordinating researchers; it is not a theorem found in the inspected Gallai papers.

This removes the invalid requirement that a partial all-transitive parity space fit inside the embedding-order space of one binary tree. Two-color prime quotients, including colored induced `P4` examples, are allowed.

## 2. Primary sources actually inspected

| Source | Exact inspected result | Scope boundary |
|---|---|---|
| Gyárfás & Simonyi (2004), *Edge Colorings of Complete Graphs Without Tricolored Triangles*, Journal of Graph Theory 46:211–216, DOI [10.1002/jgt.20001](https://doi.org/10.1002/jgt.20001), [primary full PDF](https://www.math.u-szeged.hu/~hajnal/seminars/kombszem/cikkek/szemi_gallai_color.pdf) | Theorem A: every complete-graph coloring with no rainbow triangle is obtained by substituting smaller such colored complete graphs into vertices of two-colored complete graphs. For at least two vertices, this gives a nontrivial partition into homogeneous parts with at most two colors on edges between parts. The paper attributes the underlying result to Gallai (1967), *Transitiv orientierbare Graphen*, Acta Math. Hungar. 18:25–66. | Parts are ordinary color modules, with no prescribed vertex order. It does not assert interval modules, active queries, phylogenetic support, or a quartet learner. |
| Adin, Berenstein, Greenstein, Li, Marmor & Roichman (2025), *Transitive and Gallai colorings of the complete graph*, European Journal of Combinatorics 130:104225, DOI [10.1016/j.ejc.2025.104225](https://doi.org/10.1016/j.ejc.2025.104225), [author full PDF](https://pages.uoregon.edu/arkadiy/transitive.gallai.complete.graphs.pdf) | Definition 1.1 calls a coloring of the ordered acyclic tournament **transitive** when `c(i,k) ∈ {c(i,j),c(j,k)}` for every `i<j<k`. This is exactly the property needed here. The paper studies maximal color partitions and their enumeration; in particular a transitive coloring uses at most `m−1` colors. | This terminology and the underlying coloring structure are prior. No adaptive quartet-query reconstruction theorem was identified in this paper. |
| Hartmann, Bannach, Middendorf, Stadler, Wieseke & Hellmuth (2020 preprint), *Complete Edge-Colored Permutation Graphs*, [primary preprint PDF, arXiv:2004.07118](https://arxiv.org/pdf/2004.07118) | Lemma 2.7: a primitive complete edge-colored graph with at least three colors has a rainbow triangle. Corollary 4.11: every strong prime-module quotient with at least three vertices of a complete edge-colored permutation graph is two-edge-colored. The paper also supplies a quadratic recognizer for an explicitly supplied colored graph. | Its modules are undirected color modules, which need not be intervals in a fixed base order. The corollary alone cannot be cited as the ordered decomposition proved below. Recognition of an explicit graph does not discover hidden quartet constraints. |

The full texts and theorem passages above were inspected. Retrieval receipts: Gyárfás–Simonyi `turn33view2`, `turn34view3`, `turn41view0`, exact Theorem A `turn45view0`; Adin et al. `turn33view0`, exact Definition 1.1 `turn45view1`; permutation-graph paper `turn33view1`, `turn34view0`, `turn41view1`, exact Corollary 4.11 `turn45view2`. URLs and DOIs, rather than these ephemeral identifiers, are the durable bibliography.

## 3. From independent transitive flips to the coloring condition

**Hand-derived equivalence.** Fix a total base order on a set `Y` of `m` labels. Partition its unordered pairs into colors. A bit for each color reverses all comparisons of that color relative to the base order. Assume every color-bit assignment produces a transitive tournament, hence a total order.

For `x<y<z`, put `a=c(x,y)`, `b=c(y,z)`, `d=c(x,z)`. If `d` differs from both `a` and `b`, flip `d` alone: the comparisons become `x<y<z<x`, a directed triangle. Therefore

`c(x,z) ∈ {c(x,y),c(y,z)}`.                                              (T)

Conversely, (T) prevents every directed triangle under every bit assignment. If `a=b`, then (T) forces `d=a`, so the triple is either the base order or its reverse. If `a≠b`, then `d` is one of them; enumerating the two relevant bit values gives four transitive triple orders. A tournament is transitive exactly when it has no directed triangle, so (T) suffices globally. This is the prior term **transitive coloring** from Definition 1.1 of Adin et al.

Every transitive coloring is Gallai: a rainbow triangle would contradict (T). The converse is not needed and generally false.

## 4. Ordered run-refinement lemma

**Hand-derived lemma using the primary Gallai partition theorem.** Every transitive coloring on at least two totally ordered vertices has a nontrivial partition into consecutive intervals such that every pair of parts is monochromatic and all cross-part edges use at most two colors. Each part is a color module of the whole vertex set.

**Proof.** Apply Gyárfás–Simonyi Theorem A to obtain a nontrivial partition `A_1,…,A_t`, `t≥2`, into ordinary color modules, with cross-part palette `S` of size at most two. Refine each original part into its maximal consecutive runs in the base order. The runs partition the order into intervals; there are at least two runs.

First prove that a run `R⊆A` remains a color module. An outsider `z` in another original part sees one constant color to all of `A`, so to all of `R`. If instead `z∈A\R`, some vertex `b∉A` separates `z` from the entire run `R`: choose a gap between the distinct runs of `A` containing `z` and `R`. The original module property gives `c(z,b)=c(x,b)=s_b` for every `x∈R`. The base order is either `z<b<x` for all such `x`, or `x<b<z`. Applying (T) to this triple forces `c(z,x)=s_b`, independent of `x`. Thus every outsider sees one color to the run. Since `R` is an interval, every outsider also has the same base-order direction to all vertices of `R`.

Two runs from different original parts inherit their original uniform cross color in `S`. For two distinct runs `R,R′` from the same original part `A`, choose a separating `b∉A`; for every `x∈R`, `y∈R′`, the module property gives `c(x,b)=c(y,b)=s_b∈S`, and (T) gives `c(x,y)=s_b`. Their cross color is therefore also uniform and lies in `S`. Consequently the refined interval partition has a quotient with at most two colors, as required. ∎

No finite enumeration is used in this proof. In particular it applies to the valid-tree-family partial-mask counterexample that defeated the containing-tree approach.

## 5. Recursive hierarchy and constructive polynomial route

Restrict the coloring to each interval part and apply the lemma recursively. Restrictions retain (T). A module of an induced part that is itself a global module is also a global module: an outsider within the part is handled by the induced module condition, and an outsider beyond the part sees one color to the entire part. Stop at singletons. The resulting rooted tree has `m` singleton leaves, every internal node has arity `q_v≥2`, every node represents a consecutive color module, and every internal quotient has at most two colors. If `I` is the number of internal nodes, then

`I≤m−1`, and `Σ_v q_v = m+I−1 ≤2m−2`.                              (1)

The equality counts the tree edges. This is a decomposition of the coloring, not a binary phylogenetic tree or a symbolic-ultrametric LCA representation.

For a direct polynomial implementation, enumerate all proper interval modules of each current interval and find a cover of minimum cardinality by dynamic programming along the order. The cover has at least two parts. If its quotient used more than two colors, the ordered run-refinement lemma applied to that quotient would give a nontrivial proper consecutive module containing at least two quotient vertices. Otherwise all refined parts would be singleton and the entire quotient would already have at most two colors, a contradiction. The union of the corresponding consecutive cover parts is itself a proper interval module: outsiders to the union see one color by the quotient module property, and each original part has uniform interaction with every other part. Replacing those parts by their union reduces the cover cardinality, contradicting minimality. Hence every minimum cover has a quotient with at most two colors. Recurse.

This gives a polynomial construction without relying on an unimplemented strong-module algorithm. The minimum-cover claim and algorithm are derived here, not located in the inspected primary sources. Their exact runtime is a separate implementation claim; the query bound below permits polynomial internal computation.

## 6. Module persistence and a conservative color-flip weight

Every node interval stays consecutive under every transitive color-bit assignment. In the base order an outsider is uniformly before or uniformly after the entire interval, and has one color to its vertices. Flipping color bits therefore changes all of those outside comparisons uniformly. In the resulting total order, no outsider can lie between two vertices of the interval.

Let

`w_c = Σ_{v: quotient of v uses c} (q_v+1)`.

This conservative weight includes the two possible exterior boundaries when `q_v` child blocks are permuted. Changing one color bit permutes child blocks at exactly the nodes whose quotient uses that color, preserving each child’s internal order until its own update. Such a permutation introduces at most `q_v−1` new interchild adjacencies and at most two new exterior adjacencies, hence at most `q_v+1` new unordered adjacent leaf pairs. Apply these block permutations sequentially; the final order realizes the color flip. Intermediate orders need not correspond to a globally uniform color-bit assignment, because no oracle certification is performed until the block updates finish. The count does not double-charge every changed endpoint at all ancestors: each local update is charged for its actual exterior boundaries.

There are at most two quotient colors per node. Therefore, writing `W=Σ_c w_c`,

`W≤2Σ_v(q_v+1)=2m+4I−2≤6m−6`.                                    (2)

Every occurring pair color appears on some quotient, so its weight is positive. A tighter weight using `q_v` may be possible if endpoint propagation is handled explicitly; (2) is sufficient for the stated asymptotic query bound and does not assume such a refinement.

**Refinement from the adaptive-construction reviewer.** One may instead use `a_c=Σ_{v: quotient uses c}q_v`. The same sequential block argument gives at most `q_v+1≤2q_v` new adjacencies per local permutation, and hence at most `2Σ_{c flipped}a_c` for a repair. Now `A=Σ_c a_c≤2Σ_vq_v≤4m−4`. Each child update charges its own outside boundaries; a later parent update uses the current child endpoints. This absorbs endpoint propagation into the factor two. Both choices give the same `O(m log m)` amortized adjacency bound. This sharper formulation matches the coordinating theorem; it does not change the conservative proof above.

## 7. Adaptive application and its remaining attribution boundary

This section is a **hand-derived application and coordinating-agent proof sketch**, rather than a located prior theorem. The full oracle algorithm, certificate lemma, source reduction, code, and independent finite controls belong in the coordinating theorem and implementation files.

After the anchored parity system has been reduced until all its assignments are transitive, choose one solution as base order and gauge every pair variable relative to it. Signed components become the colors in Section 3. Additional positive quartet equations identify color bits, possibly with opposite parity. They cannot make the candidate solution space nontransitive: they restrict an already transitive space. A rejecting oracle response forces at least one previously absent independent constraint, hence merges current components.

Repair the current assignment by flipping the lower-weight side of each violated parity merge, where a merged component’s weight is the sum of its original color weights. The flipped side’s containing-component weight at least doubles. Thus each original color weight is charged at most `1+floor(log_2 W)` times. Sections 5–6 give at most

`O(W log W)=O(m log m)`

new adjacent leaf pairs across all repairs, including a linear initial scan. If certifying one adjacent pair uses at most `m−2` anchored quartet measurements, and previously measured quartets are cached, total certificate measurements are `O(m² log m)`. The preliminary directed-cycle witness stage requires at most `binom(m,2)` independent pair constraints, also quadratic. This establishes the combinatorial accounting needed for a candidate `O(n² log n)` adaptive common-order learner, subject to the separately proved adjacent-pair certificate and oracle progress lemmas.

The source-specific sparse split recovery can then follow the common order, if its hypotheses and charged query bound are separately established. This note does not infer the full split union from an anchored table; the inherited anchor collision forbids that inference.

## 8. Prior and novelty boundary

The following components have clear primary prior: quartet GF(2) order encodings and anchored signed constraints (Keijsper–Pendavingh); transitive colorings; Gallai two-color homogeneous partitions; two-color prime quotients of complete edge-colored permutation graphs; and standard weighted union charging. These should be attributed as prior rather than packaged as newly discovered primitives.

The ordered run refinement, minimum interval-module cover argument, and combination with adaptive complete-mask quartet certification were derived during this continuation. A bounded targeted search did not identify a paper already giving this exact `O(n² log n)` oracle learner for arbitrary nonempty binary-tree families with a common circular order. This is an absence of a located theorem, **not** a historical novelty guarantee. In particular, an explicit-graph decomposition theorem does not by itself charge hidden-oracle measurements, and tree-only reconstruction does not establish an arbitrary-family complete-mask result.

Final targeted search receipts, 2026-09-30: second-engine queries `quartet "transitive coloring" reconstruction adaptive`, `"quartet" "Gallai" reconstruction`, and `"quartet" "O(n^2 log n)" circular order`; first-engine verification queries `phylogenetic quartet oracle common circular ordering adaptive queries Gallai`, `quartet union trees circular order adaptive reconstruction quadratic`, and `"Complete Edge-Colored Permutation Graphs" authors`. Results were mostly irrelevant exact-word hits or the already inspected coloring papers. The stronger search also returned Lin's single-tree full-quartet consistency tester ([arXiv:2608.00987](https://arxiv.org/abs/2608.00987)) and Arvanitakis, Chatziafratis, Luo & Makarychev's *Optimal Phylogenetic Reconstruction from Sampled Quartets* ([arXiv:2604.17461](https://arxiv.org/abs/2604.17461)). Primary indexed abstracts were inspected: both assume one ground-truth tree, with respectively property-testing verification or noisy random-sample approximate recovery, and neither abstract supplies the exact multi-tree complete-mask learner sought here. No full proof of either recent lead was inspected in this final scan. Receipts `turn42academia42`, `turn43academia2`, `turn43academia3`, `turn43academia5`. These searches are bounded and can miss relevant prior phrased differently.

The master optimum remains open unless a matching bound is independently proved: a candidate `O(n² log n)` upper bound improves the inherited cubic learner but does not match the inherited `Ω(n log n)` adaptive lower bound. No theorem here promotes the nonadaptive cubic lower bound into an adaptive one.

## 9. Verification and handoff

This contribution is an all-size mathematical proof plus full-text primary audit. It has not executed the new Gallai hierarchy or adaptive repair implementation. Earlier executed tree-family finite controls and the subsequent actual-family containing-tree counterexample are recorded in `PRIMARY-PRIOR.md` and the coordinating agents’ files; they do not establish this lemma. Parent and adaptive-construction agent were sent the exact theorem attribution and the ordered proof.

Required independent audit points are: the parity-to-color gauge; every generated oracle witness yields an actual new merge; the full adjacent-pair certificate characterizes common-order validity; local block permutations realize each color flip; and implementation counters include every initial, witness, repair, and sparse-recovery query. The structural Gallai lemma and its linear weight accounting are fully supplied above.
