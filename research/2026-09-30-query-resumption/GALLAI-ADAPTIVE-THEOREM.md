# An adaptive O(n² log n) learner for common circular orders

ID: QUERY-RESUMPTION-GALLAI-20260930. Contributor: Codex adaptive-construction researcher, with the coordinating root's algorithm and delegated primary-prior/algebra reviews. Date: 2026-09-30 UTC.

Status: all-size hand-derived theorem, implemented research algorithm, independent exact finite graph-cut controls. No Lean certificate, historical-priority claim, or matching optimal-query theorem. This proof supersedes the conditional containing-binary-tree route in [adaptive-construction-parity-checkpoint.md](adaptive-construction-parity-checkpoint.md).

**Dated status update, 2026-09-30 UTC:** Astra subsequently published a stronger O(n log n) whole-common-order learner at pinned commit `836cc5a62648f72e59161d583f882b12ac801495`. This contributor independently reviewed and accepted its hand proof; see [ASTRA-ORDER-REVIEW.md](ASTRA-ORDER-REVIEW.md). With inherited sparse recovery and the conservative source k<=13n-27 bound, the admitted BOTH-output asymptotic optimum is now Theta(n log n). The O(n² log n) theorem below remains valid as a supplementary independently implemented route; its historical open-optimum statements describe the earlier checkpoint and are superseded by this update. Near-linear authorship remains Astra's.

## 0. Result and unchanged master

**Theorem.** Let F be a nonempty family of binary unrooted phylogenetic trees on n>=4 labeled taxa. Suppose its trees admit at least one common circular order. An oracle gives the complete union of DISTINCT resolved quartet topologies on each requested four-taxon subset. Without a supplied order, displayed tree, occurrence tree, or blob decomposition, one common circular order can be found with O(n² log n) adaptive oracle queries and polynomial computation.

The theorem applies to the entire finite binary semi-directed LSA-rootable, outer-labeled planar, galled source class, at arbitrary finite reticulation levels and blob counts: its displayed-tree family satisfies the common-order promise. The proof is broader than that source class and does not rely on a level bound, one-blob model, adjacent-copy representation, or independence of switch choices.

Combining the learned order with inherited known-order sparse recovery gives the complete displayed split union with

    O(n² log n + k log n)

queries, where k is the number of nontrivial displayed splits. The pinned source-count bound k<=13n-27 specializes the whole admitted network class to O(n² log n). Alternatively, the elementary dense boundary recovery adds O(n²) queries, so O(n² log n) full split recovery already holds for ANY common-order binary tree family, without a sparse source-count assumption.

The previous O(n³) universal upper bound is therefore improved. The exact optimal adaptive complexity remains open:

    Omega(n log n) <= Q_opt <= O(n² log n).

The nonadaptive cubic lower bound does not match this adaptive upper bound. Full graph/network reconstruction and recovery from biological observations are different contracts.

## 1. Observation equations and invariant

Fix an arbitrary anchor r, and put Y=X minus {r}, m=n-1. Use an arbitrary fixed naming order on Y. There is one comparison variable b_xy for each unordered pair, with b_xy=1 if x precedes y when x<y in the naming order. For x<y<z, each supported anchored topology contributes the following parity equation:

| Supported topology | Comparison equation |
|---|---|
| rx\|yz | b_xy=b_xz |
| ry\|xz | b_xy XOR b_yz=1 |
| rz\|xy | b_xz=b_yz |

Each equation says that the taxon paired with r cannot lie between the other two after cutting the circle at r. Signed union-find represents the queried equations. Every true common circular order satisfies every queried equation; the maintained affine solution space therefore remains nonempty. Complete support is essential: all supported topologies impose equations, including both topologies in an ambiguous answer.

This anchored GF(2) representation is attributed to Keijsper–Pendavingh, particularly their signed graph construction and tree theorem. Intersection over ordinary trees gives the exact common-order space from FULL anchored support. The adaptive argument below needs only the direct comparison equations, their nonempty invariant, and the clade certificate in Section 5.

## 2. First phase: force all remaining assignments to be transitive

A tournament is transitive exactly when it has no directed three-cycle. For each triple of nonanchor taxa, test whether one of its two cyclic comparison assignments remains feasible in the current signed forest. The two cycles differ by global reversal; all queried equations preserve reversal, so it is enough to test one.

When a cycle is feasible, query its anchored quartet and impose every returned equation. In a directed three-cycle each vertex has opposite comparison directions to the other two. Consequently EVERY possible rooted topology equation excludes that cyclic assignment. At least one independent signed equality is added, hence forest rank increases by at least one.

There are N=binom(m,2) pair variables. The phase uses at most N oracle queries. A single scan of all triples suffices: once a triangle's cyclic assignment is infeasible, subsequent restrictions cannot restore it. At the end every assignment of the remaining component orientations is a transitive tournament, hence a linear order of Y. Choose any such assignment and call its order L0.

This is a feasible polynomial witness search, rather than an enumeration of all affine assignments. It need not read the full anchored table. The phase alone does NOT establish that L0 satisfies unqueried quartet constraints. Section 6 repairs precisely that deficiency.

## 3. Component colors form a transitive coloring

Give each unordered taxon pair the color of its first-phase signed-forest component. Express every component orientation relative to the chosen order L0, so changing a color reverses all comparison directions having that color.

For three taxa x<y<z in L0, transitivity of EVERY component assignment is equivalent to

    c(x,z) in {c(x,y), c(y,z)}.                         (TC)

Indeed, a directed cycle would require xz to reverse relative to BOTH xy and yz. Such an assignment exists exactly when color xz is distinct from both of the others. All pairs of the same color reverse together, so (TC) blocks both cyclic orientations.

Thus no triangle has three colors. More strongly, (TC) is the standard transitive-coloring property in the fixed order. It permits induced monochromatic P4 graphs; it is not a symbolic ultrametric and need not be representable by a containing binary tree. The following interval decomposition handles these P4 cases directly.

## 4. Ordered Gallai decomposition with O(m) total weight

A set D of taxa is a color module if each outsider z has the same pair color to every taxon in D. An interval module is additionally consecutive in L0. All singletons are modules.

### 4.1 Refining a Gallai partition into interval runs

The classical Gallai partition theorem applies to any complete graph with no rainbow triangle: the vertices have a partition into at least two nonempty parts, every pair of parts has one constant cross color, and at most two colors occur between parts.

Apply it to a block with its induced L0 order. Split each Gallai part into its maximal contiguous runs. Each run R is an interval module:

- If outsider z belongs to another Gallai part, its color to every x in R is constant by the Gallai partition.
- If z belongs to the same Gallai part but another run, choose a taxon b in a different part between z and R. For every x in R, the two cross colors c(z,b) and c(x,b) equal one fixed color s. The ordered relation (TC) forces c(z,x)=s. Hence the same outsider sees all of R in one color.

Between runs from different parts, the cross color is inherited. Between two runs from the same part, the preceding argument shows their constant color is also one of the at-most-two original cross colors. Therefore these runs form a proper interval-module partition whose quotient has at most two colors.

The statement also holds on every induced interval block, since (TC) is inherited under restriction. No source-network representation is needed.

### 4.2 A polynomial hierarchy constructor

For an interval block B of size t>=2, enumerate all proper contiguous subintervals and test whether each is a module relative to B. The full block itself is excluded; singletons always qualify. Dynamic programming along the order chooses a cover of B using the MINIMUM number q of proper interval modules. The chosen modules form disjoint consecutive children.

Every pair of children has a constant cross color: the module condition for each child makes it constant over both child sets. If the quotient had more than two colors, apply Section 4.1 to this transitive quotient. Its interval-module partition cannot consist entirely of singletons, since then its cross palette would still have more than two colors. Thus a proper nontrivial consecutive group of quotient children is a module. Their union is a proper interval module of B and could replace several children by one, contradicting the minimum cover. Hence the minimum cover quotient has at most two colors.

Recurse on each child. Every internal node has arity q>=2, and the hierarchy has m leaves. Therefore

    sum over internal nodes q <= 2m-2.

Assign an original comparison color a weight equal to the sum of arities of hierarchy nodes in whose quotient palette it occurs. At each node at most two colors occur, so the total color weight W satisfies

    1<=W<=2 sum q<=4m-4=4n-8.                          (W)

Every color has positive weight because every pair has a lowest hierarchy node separating its two leaves; its color occurs in that quotient. The number of colors is at most m-1: a q=2 quotient has one color, and q>=3 quotients have at most two<=q-1 colors. The total number of distinct colors is thus at most sum(q-1)=m-1.

Enumeration of module candidates, the interval-cover DP, and recursion are polynomial. A deliberately naive implementation has a conservative O(m^5) hierarchy-construction bound; no O(n² log n) runtime is claimed. The improved bound concerns oracle measurements.

### 4.3 The hierarchy persists under all component flips

Every hierarchy interval module remains consecutive under EVERY first-phase component assignment. For an outsider z and module D, all comparison colors c(z,x), x in D, agree. In L0, z lies entirely on one side of D. Flipping that color either preserves this relation for all x or reverses it for all x, so z can never lie between two members of D.

The order of a hierarchy node's children depends only on colors in its quotient palette. If a set A of original colors flips, only nodes whose palette meets A can reorder their child blocks. Each such node of arity q can be changed by one block permutation. This creates at most q+1 new undirected adjacent leaf pairs: q-1 between children and at most two at the external boundaries. Since q>=2, this is at most 2q.

Process affected nodes one at a time, keeping their child blocks intact. Intermediate orders need not satisfy the affine equations; they are used only to count adjacency changes. Every internal adjacency change is charged to its own node's permutation. Thus a flip of A creates at most

    2 sum_{colors c in A} weight(c)                     (ADJ)

new undirected adjacencies. This also bounds the adjacencies in the final order that were absent in the preceding order. The original hierarchy is retained throughout learning; later equations only restrict its component assignments.

## 5. A complete anchored adjacency certificate

For a proposed order L on Y, query {r,a,b,c} for each adjacent unordered pair {a,b} of L and every third taxon c in Y. Accept exactly when every supported rooted topology's forbidden middle is absent from the order of that triple. There are at most (m-1)(m-2) queries for one order, with caching.

Necessity follows because a rooted clade cannot contain two endpoints while excluding a taxon between them in a compatible order.

For sufficiency, root each tree of F at the neighbor of r and omit r. If some rooted clade C is not an interval of L, choose the end a of a left run of C, its immediate successor b outside C, and a later c in C. The rooted tree displays ac\|rb: the least common ancestor clade of a,c lies in C and excludes b. The adjacent pair {a,b} causes this quartet to be queried, and the supported topology forbids b as middle. It is rejected. Hence acceptance implies every clade of every tree is an interval, exactly the true common-circle condition after restoring r.

This proof works for any binary tree family and arbitrary source size. It does not confuse an observed absence with a statistically unobserved event.

## 6. Weighted parity repairs and query bound

After the first phase, use the original color variables as the unknown bits. Every new quartet equation is a parity relation between two original colors, with its sign adjusted for L0. Maintain components of colors connected by measured relations. Each component has weight equal to the sum of its ORIGINAL color weights.

Maintain an assignment satisfying all measured relations and its transitive leaf order. For each adjacent pair of that order, fetch all anchored quartets with every third taxon, caching by taxon set. Process their equations. If a new relation disagrees with the current assignment, its two colors must belong to distinct parity components: a disagreeing relation inside one component would contradict the true common-order invariant.

Merge the two components. If adjustment is needed, flip the entire SMALLER-WEIGHT component. All earlier equations remain satisfied, and all assignments of the first-phase space remain transitive. Restart the adjacency certificate for the resulting order. A consistent relation between different components can merge them without a flip. There are at most m-2 effective color-component merges.

Whenever an original color is flipped on the smaller side, its component's weight at least doubles after merging. Therefore each unit of original color weight is flipped at most ceil(log2 W) times. The total flipped weight satisfies

    F_weight <= W ceil(log2 W).

By (ADJ), the number D of distinct undirected adjacent taxon pairs encountered in the actual candidate orders satisfies

    D <= (m-1)+2W ceil(log2 W).                          (D)

For each such pair there are m-2 third taxa. Cached equations must be reevaluated when the order changes, but their answers need not be remeasured. Including the initial cycle phase gives the explicit bound

    Q_order <= binom(m,2) + (m-2)[(m-1)+2W ceil(log2 W)]
            <= binom(n-1,2)
               +(n-3)[n-2+8(n-2)ceil(log2(4n-8))]
             = O(n² log n).

The process terminates because each failure creates an effective component merge. At termination the complete anchored adjacency certificate accepts, so the returned order is truly common to F. The algorithm does not claim to recover EVERY common order using these measurements.

### 6.1 A sharp boundary of this measurement strategy

Starting with N independent pair variables, an all-transitive signed-equality space has dimension at most m-1 by Section 4.2. Consequently any strategy that first forces EVERY affine assignment to be transitive must acquire rank at least N-(m-1)=(m-1)(m-2)/2. One complete anchored support answer supplies at most two independent parity equations. Such a strategy therefore needs at least

    ceil((m-1)(m-2)/4)=Omega(n²)

queries. On an ordinary binary tree, every answer has one topology and supplies at most one independent equation, strengthening this to (m-1)(m-2)/2 queries. The n=64 tree controls' 1,891 cycle-phase queries attain that strategy-specific rank threshold.

This is NOT an Omega(n²) lower bound for the master adaptive problem: ordinary trees already admit O(n log n) reconstruction by other methods. It shows that optimizing this all-transitive affine completion cannot establish the near-linear optimum. A further O(n log n) upper bound must use a different information invariant, rather than requiring all remaining pair-variable assignments to become orders before learning one candidate.

## 7. Complete split output and all-level specialization

With the common circle C=(x0,...,x_(n-1)), query each pair of disjoint adjacent gaps (a,b),(c,d). The interval split {b,...,c}\|{d,...,a} is displayed exactly when bc\|ad is in the answer. One direction is restriction of a displayed edge. Conversely, in a tree displaying bc\|ad, a central-path edge has a split circular in C. The two adjacent boundary gaps force that full edge split to be exactly the proposed interval split.

This elementary dense second stage uses at most n(n-3)/2 quartet queries and outputs the full nontrivial split union by gap indices; add all n singleton splits. It is valid for arbitrary common-order binary tree families, even if their split count is quadratic. Therefore the new O(n² log n) bound applies to the combined order-and-split output without relying on the inherited source-count proof.

The inherited sparse second stage instead uses at most

    2n-6+4k ceil(log2(n-1))

queries. On the admitted arbitrary-level network class, k<=13n-27 by the pinned conditional source-count theorem. This sparse composition also gives O(n² log n), with lower second-stage cost. The order must be passed by actual taxon relabeling; topology bit positions must be converted accordingly.

Writing every bipartition as n explicit taxon indicators incurs additional output cost O(nk). Gap-index output avoids disguising that expansion cost. No biological sample complexity or hidden graph identifiability is inferred from an exact support oracle.

## 8. Why the failed tree shortcut is unnecessary

The earlier containing-tree premise was false even for partial COMPLETE support unions of two actual common-order binary trees. The explicit seven-taxon family in [adaptive-construction-countercheck.py](adaptive-construction-countercheck.py) has rooted trees

    T1=(((1,2),3),(4,(5,6)))
    T2=(1,(6,((2,3),(4,5))))

and a queried subsystem with exactly four transitive orders: 123456, 142536, and their reversals. None of the 945 labeled binary trees contains all these orders. Its component colors include an induced monochromatic P4. The generic binary-tree repair route therefore cannot be promoted on the basis of small passing tests.

The Gallai hierarchy permits two-color prime quotient nodes, including this P4 pattern. Its O(m) total weight supplies the same adjacency amortization without a containing tree. This is why no source-specific independence or adjacent-copy rescue lemma is needed in the final theorem.

## 9. Implementation and actual checks

The coordinating root implemented [adaptive_recovery.py](adaptive_recovery.py). It explicitly tests feasible cyclic triangles by signed-forest component bits, constructs the hierarchy using proper interval modules and minimum-cover DP, carries weighted components, caches quartet answers, and asserts the adjacency and query bounds. [verify_adaptive_recovery.py](verify_adaptive_recovery.py) uses independently generated graph splits and exact quartet truth; its receipt is [adaptive-recovery-verification.json](adaptive-recovery-verification.json).

The receipt records all 32,774 nonempty binary-tree families on four/five taxa: 303 common-order families recovered correctly and 32,471 incompatible families rejected. Additional anchor checks, admitted level-two collision fixtures, and graph-generated stress cases through n=64 passed. The generic forbidden-tree shortcut is explicitly tested as a two-color prime case. Finite controls corroborate the hand proof and implementation; they do not establish the all-size theorem, a source-network census, a runtime benchmark, or optimality.

This contributor inspected the implementation and its receipt. Actual derivation here includes the run-refinement lemma, minimum-cover correctness, hierarchy persistence, weighted boundary count, and query amortization. No material all-size proof gap was found in those steps. The source count and sparse second-stage obligations remain attributed inherited components; dense recovery does not depend on them.

## 10. Attribution and prior boundary

- Keijsper & Pendavingh (2014), *Reconstructing a phylogenetic level-1 network from quartets*, DOI [10.1007/s11538-014-0022-z](https://doi.org/10.1007/s11538-014-0022-z), supplies the anchored affine and signed-graph construction. Its existing interactive witness loop already forces a cyclic solution space with O(n²) added quartets. The final global-certification and weighted repair phase is what addresses unmeasured support.
- Gyárfás & Simonyi (2004), *Edge Colorings of Complete Graphs Without Tricolored Triangles*, Journal of Graph Theory 46:211–216, DOI [10.1002/jgt.20001](https://doi.org/10.1002/jgt.20001), Theorem A, supplies the classical Gallai two-color substitution theorem, attributed there to Gallai (1967). The primary-prior reviewer inspected the [full university-hosted PDF](https://www.math.u-szeged.hu/~hajnal/seminars/kombszem/cikkek/szemi_gallai_color.pdf). The ordered run refinement is derived explicitly in Section 4.1 rather than assumed to be a binary-tree representation.
- Adin et al. (2025), *Transitive and Gallai colorings*, DOI [10.1016/j.ejc.2025.104225](https://doi.org/10.1016/j.ejc.2025.104225), identifies the exact transitive-coloring condition (TC). Precise bibliographic verification is recorded by the primary-prior reviewer.
- Frohn et al. (2025), DOI [10.1016/j.jcss.2025.103655](https://doi.org/10.1016/j.jcss.2025.103655), supplies relevant O(n log n) level-one quartet reconstruction; its level-one scope is not the arbitrary-level theorem proved here.
- Dense boundary reconstruction and known-order sparse split recovery are inherited Commons components, reused with attribution.

The combined adaptive all-family query theorem is a candidate contribution relative to the inspected literature. No claim of historical priority or publishability follows from this bounded prior audit.

## 11. Process-integrity assessment

The task remained the complete order-and-split output over the declared all-level class. A tempting containing-tree inference was challenged, refuted by an exact executable seven-taxon witness, and removed from the final proof. Primary-source hypotheses were distinguished from derived lemmas. Oracle topology sets, biological observations, order recovery, split recovery, and query optimality remain separate claims. Verification uses independent graph truth rather than tests that repeat the inference algorithm. No PRISMA/AMSTAR systematic-review score is assigned to this targeted mathematical search.

Process verdict: internally reviewed hand proof with reproducible finite corroboration. Required next strengthening is independent adversarial proof review and historical-prior verification, followed by publication-quality algorithm analysis; neither changes the theorem's declared mathematical assumptions.

## 12. Robustness and remaining maximal obligation

The query bound depends on four exact facts: common-order existence preserves a nonempty affine space; the cycle phase makes every assignment transitive; ordered Gallai refinement has O(m) total palette weight; each complete anchored certificate failure creates a parity-component merge. Removing complete existential support invalidates equations and certification. Removing the common-order promise can cause parity inconsistency or rejection. None of the proof relies on a maximum level, maximum blob count, finite enumeration cutoff, or biologically generic parameters.

Robustness verdict: the all-size adaptive upper-bound improvement is supported; the optimal adaptive master remains open. A matching lower bound, or further upper reduction toward O(n log n), would change the final complexity verdict. The supplied exact-support experiment remains separate from determining when a biological observation law identifies that support.
