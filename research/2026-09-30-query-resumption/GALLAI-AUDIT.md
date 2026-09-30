# Independent all-size audit of adaptive Gallai order recovery

Contributor: Codex algebra-audit subagent, GALLAI-AUDIT-20260930.
Date: 2026-09-30 UTC. Status: independent hand-derived proof review, production-code review, and executed exhaustive color-cube controls. No Lean certificate, historical novelty claim or optimal adaptive closure.

Subsequent review update, 2026-09-30: this remains a reviewed supplementary O(n^2 log n) upper bound. [ASTRA-QUERY-REVIEW.md](ASTRA-QUERY-REVIEW.md) accepts the stronger pinned Astra O(n log n) acquisition accounting, conditional on its separately reviewed structural invariant. The earlier open-master statement below records this packet's original scope; no optimality is claimed for the Gallai learner.

## Verdict

**SOUND under the declared exact common-circle binary-tree-family promise.** The adaptive order learner has O(n^2 log n) exact quartet oracle calls. The minimum interval-module cover, fixed hierarchy, color weights, smaller-weight merges and adjacency certificate provide the stated all-size bound. The argument works for arbitrary finite binary tree families admitting a common circle, so it applies to the whole admitted source class through its inherited common-order theorem. Source level and blob count are not bounded by this proof.

The implementation is polynomial and deliberately unoptimized. The query bound is not its runtime bound. The inherited known-order sparse second stage remains necessary because the anchored support does not determine complete split support. Combining that stage with this order learner improves the whole-source adaptive upper bound, while the optimal adaptive master remains open.

The earlier generic premise that every reversal-closed all-transitive affine space is contained in a binary-tree order space is false. The Gallai construction below handles that failure directly and does not use the false premise. Its four-order prime-P4 example is explicitly included in production controls.

## Pinned code and prior

Reviewed production: [adaptive_recovery.py](adaptive_recovery.py), SHA256 `e9a67187cce906761b95368c8a5c034f9a52ce9a9e051570aed46bb24e426cc5`.

Reviewed verifier: [verify_adaptive_recovery.py](verify_adaptive_recovery.py) and the executed [adaptive-recovery-verification.json](adaptive-recovery-verification.json). Production uses the independently reviewed [order_recovery.py](order_recovery.py) for signed graph primitives and preserves attribution to the existing sparse implementation.

Primary prior inspected:

- Keijsper–Pendavingh, arXiv:1308.5206v1, <https://arxiv.org/html/1308.5206v1>: anchored affine coordinates and signed pair graph are established; see [ALGEBRA-REVIEW.md](ALGEBRA-REVIEW.md).
- Hartmann et al., *Complete Edge-Colored Permutation Graphs*, arXiv:2004.07118v1, <https://arxiv.org/pdf/2004.07118>: Gallai substitution and strong-module quotient framework; Theorem 4.1(iv) and Corollary 4.11 show prime quotients are two-colored. Lemma 2.7 proves a primitive complete coloring with at least three colors has a rainbow triangle. This is governing structural prior, rather than evidence of new fundamentals.
- Hellmuth–Wieseke, arXiv:1509.05069v1, <https://arxiv.org/pdf/1509.05069>, Theorems 1–2: a symbolic ultrametric tree representation additionally needs every color graph to be P4-free. All-transitivity alone does not supply that stronger property. The new hierarchy avoids imposing it.

Historical priority of this particular observation-and-amortization interface has not been established.

## 1. Cycle phase really closes all transitivity obligations

Write m=n-1. The anchored parity graph has V=C(m,2) unordered-pair variables. Its solution space remains nonempty, since any true common order satisfies all exact returned support constraints. It is closed under complementing every comparison, because each equation relates two variables with a prescribed parity.

For any ordered triple x<y<z, a directed tournament cycle has pair bits (v_xy,v_xz,v_yz)=(1,0,1) or its complement (0,1,0). One pattern is extendible to a whole signed-graph solution exactly when the three variables prescribe consistent values to every graph-component seed. The code's `root_values` test checks that condition exactly. Complement closure permits testing only the first pattern.

If a cycle is possible, query its anchored quartet. Every nonempty supported resolution imposes equality of two comparisons from the same quartet vertex. Such equality fails on a directed three-cycle. Therefore the answer excludes the witnessed affine assignment and increases rank. Under the common-circle promise no parity contradiction is introduced. Each queried triple permanently becomes acyclic, and later equations cannot restore a formerly excluded assignment.

Scanning each triple once consequently leaves every assignment acyclic on every triple. A tournament without a directed three-cycle is transitive. There are at most V rank-increasing calls, irrespective of how many triples are inspected computationally. The source family's trees need not be enumerated.

## 2. Component colors admit an interval Gallai hierarchy

Choose one solution and extract its linear order L0. Give pair {x,y} the color c(x,y) of its initial parity component. Flipping a color reverses exactly those pair comparisons, relative to L0. All assignments of these independent flips remain transitive by the preceding phase.

For x<y<z in L0 this implies

    c(x,z) belongs to {c(x,y), c(y,z)}.                 (G)

Otherwise choose the two short-edge orientations forward and the long-edge orientation backward; independent colors would realize a directed three-cycle. Thus no triangle is rainbow, and the classical Gallai partition theorem applies.

An interval module M of an ordered colored complete graph is a consecutive leaf set for which every outside leaf z sees all leaves of M in the same color. At each nonsingleton current block, use a partition into proper interval modules having the minimum possible number q of parts. Singletons provide a feasible partition.

### 2.1 Refining a Gallai partition into interval modules

The classical Gallai theorem gives a nontrivial partition into modules with at most two colors on edges between parts. A part need not initially be consecutive. Split every part into its maximal contiguous runs in the current order.

Each run R is still a module. An outside taxon belonging to a different original part has uniform color to R by the original module property. For a taxon z in the same original part but a different run, choose a separator y from another original part between z and all taxa x in R. Module uniformity gives c(x,y)=c(y,z)=d. Property (G), applied in their order, forces c(x,z)=d. This is uniform over R and belongs to the original interpart palette.

Thus the run refinement is a nontrivial partition into proper interval modules, and edges between its parts still use at most the original two colors. No theorem about binary-tree containment is involved.

### 2.2 A minimum cover has at most two quotient colors

The q child modules have homogeneous interchild edges; their quotient is again a complete coloring satisfying (G), ordered by child position. Suppose its palette had more than two colors. Apply the preceding Gallai run refinement to this quotient. Since the refined quotient partition has at most two interpart colors, at least one of its proper interval modules contains two or more quotient vertices; otherwise its interpart palette would equal the original palette of more than two colors.

The union of that consecutive group of child modules is itself a proper interval module of the original block. Quotient-module uniformity gives uniform colors towards all other children, and the child module properties handle every leaf. Replacing the group by its union reduces the cover's part count, contradicting minimality. Therefore every production quotient has at most two colors.

Recursion terminates because each child is proper. Each internal node has at least two children, hence at most m-1 internal nodes and at most 2m-2 total child incidences. The dynamic program in `interval_hierarchy` enumerates precisely proper interval modules and minimizes their number in a consecutive partition. Its mathematical conclusion matches this argument.

## 3. The fixed hierarchy survives every color assignment

Every hierarchy block is a module and an interval in L0. For any outside taxon z, all its comparisons with leaves in a block have the same initial direction and the same color. Any color-flip assignment consequently changes those comparisons uniformly. Whenever the full assignment is transitive, z is either before all block leaves or after all of them. Thus the block remains consecutive in every assignment in U0.

This also holds recursively: a child module within a module is a module of the full colored graph, because external leaves see the whole parent uniformly. Therefore one fixed hierarchy suffices throughout all subsequent parity repairs. A later constraint may merge initial color variables, but it does not enlarge the set of allowed assignments, so the hierarchy remains valid.

## 4. Weighted color flips bound new adjacencies

For every initial color c define

    w_c = sum over hierarchy nodes whose quotient contains c of their child count q.

Every color occurs at the least common ancestor of some pair having that color, so w_c>0. A quotient has at most two colors, giving

    W = sum_c w_c <= 2 sum_nodes q <= 4m-4.

Flipping one color can change the order of child blocks only at hierarchy nodes whose quotient contains that color. At any such node, rearranging q consecutive child blocks leaves all within-child adjacencies untouched. It creates at most q-1 new interchild adjacencies and at most two new external boundary adjacencies, hence at most q+1<=2q new undirected adjacent leaf pairs.

Process local block rearrangements recursively; simultaneous occurrences can be charged separately. Intermediate rearrangements need not correspond to a full color assignment, because they are used only for the counting argument and do not issue oracle queries. Every full single-color flip is transitive and respects the same hierarchy. Consequently a color flip creates at most 2w_c new pairs, and a set of flipped colors creates at most twice its total weight. This bound applies to a difference between initial and final adjacency sets as well as to the union of all intermediate new pairs.

The production implementation charges actual component flips by their original color weights and asserts the per-repair adjacency inequality. Those assertions are controls; the preceding argument establishes the all-size justification.

## 5. Weighted merging and query budget

Maintain the current bit of each initial color and components of imposed parity relations among colors. Their actual bits represent the fixed within-component relative parities. On a violated new relation, its endpoints must be in different components; otherwise either it already holds or it contradicts the true common-order witness. Merge them, flipping the smaller total-weight component when necessary.

Every time an initial color is flipped, the weight of its component at least doubles. Since all weights are positive integers and total weight is W, total flipped weight F obeys

    F <= W ceil(log2 W).

Every effective relation merges two components, so there are at most d-1 merges for d initial colors. Merges needing no flip add a constraint without changing the candidate order. The code may impose several equations from one quartet in sequence; each component flip preserves all earlier relations, and charging the sum of their flip weights is valid.

The initial order has m-1=n-2 adjacent pairs. Thus the number of distinct unordered adjacent pairs ever encountered is at most

    A <= n-2 + 2W ceil(log2 W).

For each such pair, at most m-2=n-3 anchored quartets arise by choosing a third nonanchor taxon. Cache each exact answer. Including the initial rank phase, the code's proved order-query budget is

    Q_order <= C(n-1,2) + (n-3) [n-2 + 2W ceil(log2 W)]
            = O(n^2 log n), since W<=4n-8.

The implementation uses `(W-1).bit_length()` as exactly ceil(log2 W) for positive integer W. Its counters and budget agree with the proof. Repeated quartet lookups in the cache do not count as new oracle calls. The unrestricted sparse second stage currently does not reuse this cache, so repeated calls there are honestly counted separately.

## 6. Why final certification returns a true common order

On a proposed order L, inspect every anchored quartet formed from an adjacent pair and any third taxon. A true common order satisfies all its support equations.

Conversely, suppose a rooted clade C of some displayed tree is not an interval. Choose a run of C ending at a, the immediately following outsider b, and a later clade member c. That tree displays ac|rb; the adjacency certificate queries it through the adjacent pair {a,b}. Its equation forbids b from appearing between a and c, contradicting L. Every noninterval clade is therefore detected.

The code repeats this certificate after every repair. At the final full pass no relation causes a flip, so the current order is constant throughout the pass and satisfies every queried support constraint. It is consequently common to every displayed tree. Termination follows from the finite bound on merges. The proof concerns exact topology support and does not infer anything about noisy biological estimates by itself.

## 7. Actual independent controls and remaining limits

[gallai_audit_controls.py](gallai_audit_controls.py) and [gallai-audit-controls.json](gallai-audit-controls.json) exhaust **every canonical partition of edge colors** on 3, 4 and 5 ordered leaves after the anchor. Of 116,183 color partitions screened, 163 have an entirely transitive independent color cube. These include spaces unrealizable as binary tree support and the prime-P4 obstruction. Executed controls checked 1,110 assignments, 8,432 fixed-module interval instances and 3,254 single-color adjacency bounds. All passed.

The production verifier's recorded checks additionally passed all 32,774 nonempty four/five-taxon binary tree families, deterministic additional nonminimum-anchor checks, all anchors on the two inherited source-admitted collision fixtures, and common-circle random tree families through n=64. I inspected this verifier and receipt; I did not rerun it under a second name or recertify the source fixtures. The source admission was inherited and labeled, while large arbitrary common-circle families need not be one admitted source network.

The separate [algebra_partial_source_stress.py](algebra_partial_source_stress.py) screen ran 26,000 seeded partial-table cases at n=8,16,32. It found 17,956 all-transitive partial spaces, none with a monochromatic induced P4. It also found 3,093 spaces that were not contained in every displayed tree, showing that arbitrarily choosing a displayed reference tree would be unsafe. These finite screens motivated the stronger review but are not needed by the Gallai proof.

No material mathematical or code defect was found in the reviewed adaptive learner. No optimality claim follows from this upper bound. The inherited lower bound is still Omega(n log n); whether the remaining logarithmic/quadratic gap can be closed is a separate master obligation. The false generic binary-tree shortcut remains preserved as a correction rather than being hidden.

## 11. Process-integrity assessment

The key unsupported premise was challenged and explicitly refuted. The replacement hierarchy was then reviewed independently against classical Gallai structure, checked line by line in the implementation, and tested on all small color spaces rather than only source-friendly tree cases. This is proof review, not a systematic clinical review; AMSTAR-2 and RoB-2 scoring is inapplicable. Historical priority of the complete algorithm is still unresolved, and source-class admission depends on the inherited structural theorem and certificates.

## 12. Inference-robustness assessment

The query upper bound is supported by an all-size counting proof; finite experiments are separate controls. Its main boundaries are exact complete topology support, a nonempty binary tree family with a common circle, and the inherited sparse-stage target correspondence. The arbitrary-level scope follows from those premises rather than from testing a maximum level. Computation is polynomial but slower than the query bound. Biological identifiability, optimal adaptive complexity and journal novelty are not closed by this result.
