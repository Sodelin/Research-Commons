# Primary prior audit and a reusable affine common-order construction

Contributor: Codex delegated primary-prior researcher, QUERY-RESUMPTION-PRIMARY-20260930. Date: 2026-09-30 UTC. Parent: root query-resumption researcher. Status: bounded primary-source audit and hand-derived corollary; no historical novelty or optimal-query closure claim. This contributor did not publish or edit navigation.

## 0. Decision

No inspected theorem supplies an `O(n log n)` exact-support common-order learner for the entire admitted arbitrary-level source class. A substantial inherited prior does supply a **simpler implemented target for the existing cubic learner**: the full anchored support determines a signed graph on pair-order variables. Every consistent component orientation gives a true common circle. This extends Keijsper–Pendavingh's tree theorem by intersection; it should be attributed as such, not introduced as a new GF(2) technique.

The same prior exposes the main remaining issue clearly: compact representation and a small basis do not identify where to measure that basis. A low-dimensional solution space does not by itself imply few quartet queries.

## 1. Exact target and search boundaries

Unknown finite binary semi-directed LSA-rootable, outer-labeled planar, galled network, arbitrary finite level and blob count. A query returns all distinct displayed quartet topologies on four specified taxa. Required output is a common circular order and full displayed split union. No order, displayed tree, occurrence tree, or tree of blobs is supplied.

Local sources read: `AGENTS.md`, `START-HERE.md`, research completion standard, existing `2026-09-30-root-exact-query/{README,ORDER-AND-RECOVERY-THEOREM,ORDER-ATTACK,ANCHOR-COLLISION,LOWER-BOUND}.md`.

Search branches: circular quartet query learning; Keijsper–Pendavingh GF(2) order reconstruction; Frohn et al. sparse quarnets; PC/PQ explicit versus implicit input; QNet weighted consistency; Robinsonian seriation; prepyramid transforms; MUL-tree conflict-free inference. Primary full texts were inspected for the pivotal old GF(2), sparse quarnet, PC-tree, and Robinsonian claims. Some other papers were accessible only through primary abstracts. Search failures and scope mismatches are recorded below. This is not a systematic review.

## 2. Governing prior work

| Primary source | Inspected hypothesis and result | What it does / does not discharge |
|---|---|---|
| Keijsper & Pendavingh (2014), *Reconstructing a phylogenetic level-1 network from quartets*, DOI `10.1007/s11538-014-0022-z`; [preprint](https://arxiv.org/html/1308.5206v1), [author-university PDF](https://pure.tue.nl/ws/portalfiles/portal/3904790/581045313964436.pdf) | Theorems 2, 3, 7; Lemma 9; Theorem 8; Sections 4.2, 4.6. All cyclic-order vectors of an **undirected binary level-one** network form an affine GF(2) space. Full one-anchor quartets identify that space. Refined algorithm `O(n^3)` assumes the anchored input is exactly that of such a network. | Existing whole-order-space anchored reconstruction is closer prior than generic PQ references. Intersection across ordinary displayed trees gives the corollary below. It supplies no matching arbitrary-level adaptive query bound. |
| Frohn et al. (2025), *Reconstructing semi-directed level-1 networks using few quarnets*, DOI `10.1016/j.jcss.2025.103655`; [full text](https://arxiv.org/html/2409.06034v2) | Theorem 14(c): most semi-directed **level-one** network reconstructed in `O(n^2)` time from `O(n log n)` displayed quartets. Arbitrary-level theorem reconstructs tree of blobs with cubic quarnet-split queries. Lemma 12 uses central vertex degree at most four or a **single reticulation** cycle's spine. | Best directly relevant sparse prior; its balanced-spine insertion proof is not an all-level theorem. The richer support answer can recover quarnet-splits, but does not make the level-one spine invariant universal. |
| Hsu & McConnell (2003), *PC trees and circular-ones arrangements*, DOI `10.1016/S0304-3975(02)00435-8`; [author PDF](https://www.cs.colostate.edu/~rmm/pctrees.pdf) | Matrix rows are **explicit lists of their one-columns** (intro). Algorithm 4.3 processes one explicit row at a time, colors leaves and identifies a terminal path. | Linear time means linear in supplied incidences. It does not discover hidden rows or emulate a row membership oracle using constant quartet support queries. |
| Fink & Peters (2025), *Incremental and Interactive PQ- and PC-Trees*, DOI `10.4230/LIPIcs.SoCG.2025.84`; [primary proceedings](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.SoCG.2025.84) | Interactive application accepts a 0/1 matrix / full consecutivity sets. Update operation takes **the set** as input. | “Interactive” here does not mean active learning of hidden constraints. No latent-row query theorem. |
| Laurent & Seminaroti (2017), *Similarity-First Search: a new algorithm with application to Robinsonian matrix recognition*, DOI `10.1137/16M1056791`; [full preprint PDF](https://arxiv.org/pdf/1601.03521) | Given symmetric matrix / weighted adjacency lists with `m` nonzero entries. At most `n-1` sweeps; `O(n^2+nm log n)` time. Intro also cites an explicit-matrix optimal quadratic recognizer. | No support-oracle extraction or sparse ordinal-query guarantee. Using it requires deriving actual pairwise weights first, with an independently charged measurement cost. |
| Grünewald, Moulton & Spillner (2009), *Consistency of the QNet algorithm for generating planar split networks from weighted quartets*, DOI `10.1016/j.dam.2008.06.038`; [university abstract](https://ueaeprints.uea.ac.uk/id/eprint/22265/) | Input weighted quartets must arise from a circular **split weight function**. Return exactly that function. Only primary abstract inspected; journal full text retrieval failed. | Supports consistency with an additive weight experiment, not with Boolean existential topology indicators. The latter are generally not additive (Section 5). |
| Kleinman, Harel & Pachter (2013), *Affine and projective tree metric theorems*, DOI `10.1007/s00026-012-0173-2`; [author university record](https://authors.library.caltech.edu/records/h7bt6-gaq50), [preprint](https://arxiv.org/abs/1103.2384) | Prepyramid/PQ/PC correspondence, transformations of explicit families and metrics. Current search inspected primary abstract; local inherited audit had inspected Definitions 10 and Propositions 6/10. | Relevant pair-hull and closure prior; no newly inspected adaptive query theorem. Do not conflate affine/projective geometry here with the GF(2) affine encoding above. |
| Chaudhary et al. (2013), *Extracting conflict-free information from multi-labeled trees*; [primary open article](https://pmc.ncbi.nlm.nih.gov/articles/PMC3716922/) | Defines information as **conflict-free** implied quartet topologies and preserves it under reduction of a supplied MUL-tree. Primary abstract inspected. | The observation is not the full conflicting existential support, and the repeated-leaf occurrence tree is supplied. Does not learn hidden adjacent duplicates from quartet queries. |

Recent lead: Chuang-Chieh Lin, *Testing Full Quartet Consistency: Adaptive Reconstruction, Random Verification, and Constant-Query Testability*, [arXiv:2608.00987](https://arxiv.org/abs/2608.00987), submitted August 2026. Indexed primary abstract reports adaptive `O(n log n + epsilon^-1 log(1/delta))` tree reconstruct-or-reject and a nonadaptive cubic bound. This is an input with **one resolved quartet topology on every four-set**, and positive instances induced by **one tree**. Direct primary full-text retrieval repeatedly failed. Therefore this is a verified bibliographic lead plus abstract-level scope observation, not an inspected proof or a new master closure. It reinforces that tree-only near-linear adaptive reconstruction is established prior.

## 3. Corollary: the entire common-order space is GF(2)-affine

**Hand-derived argument from existing theorems.** Let `F` be any nonempty family of unrooted binary trees on `X`, and fix anchor `r`. Let `Q_r(T)` denote the displayed quartets of `T` containing `r`, and `Q_r(F)` their union. Use precisely Keijsper–Pendavingh's affine ambient space `U^X` and quartet equations

`u(a,b,c) + u(a,b,d) = 0` for each positive quartet `ab|cd`.

Their Theorem 7 applies to every ordinary binary tree because a tree is an undirected level-one network with no cycles. Thus

`U(Q_r(F)) = intersection_{T in F} U(Q_r(T)) = intersection_{T in F} U(T)`.

Each `U(T)` consists exactly of cyclic-order vectors of circles compatible with `T`, and is affine (Theorem 2). Their intersection is affine or empty and contains only cyclic vectors. It follows that the anchored equation system encodes **exactly all common circular orders**, for every tree family, with no galledness or network-level premise. Nonempty common-order promise makes the intersection nonempty.

If the intersection is nonempty, its dimension `d` is at most `n-2` by inclusion in any one tree's affine space (Lemma 9), or by Theorem 8. Hence it has `2^d` oriented cyclic-order vectors. The all-one reversal direction is retained, so circles identified up to reversal have `2^(d-1)` possibilities for `n>=4`.

This is an immediate tree-family extension of the prior, not a claimed historically novel GF(2) theorem. It is independent of the new `I_xy` interval characterization and can independently construct/check its output.

## 4. Explicit signed-graph construction; no PQ implementation required

For an arbitrary initial naming order `x<y<z` on `Y=X\{r}`, set `b_xy=1` iff `x` precedes `y` after cutting the true circle at `r`. There is one variable per unordered pair of nonanchor labels. Every positive anchored quartet gives a **two-variable** parity equation:

| Positive topology | Equation | Signed edge |
|---|---|---|
| `rx|yz` | `b_xy = b_xz` | even between `xy,xz` |
| `ry|xz` | `b_xy XOR b_yz = 1` | odd between `xy,yz` |
| `rz|xy` | `b_xz = b_yz` | even between `xz,yz` |

The equations are precisely the elementary statement that the leaf paired with `r` cannot lie between the other two after cutting at `r`. They are also exactly the signed graph `H(Q,r)` of prior Section 4.6.

Query every anchored triple and insert all its positive topology equations. A signed graph traversal assigns all variables in a connected component relative to one arbitrary seed. Under a common-circle promise, no odd-parity cycle can arise. Choose any seed bit in every component. The corollary proves the resulting pairwise comparison relation is transitive and total: every solution is already a cyclic vector. Sort `Y` with it, then prepend `r`.

With the explicit signed graph, time and storage are `O(n^3)` after `binom(n-1,3)` queries; sorting costs `O(n log n)`. A parity disjoint-set structure can process edges online in `O(n^3 alpha(n))` time and `O(n^2)` storage. Retaining only a spanning signed forest supplies an `O(n^2)`-edge proof certificate. This note has not executed that implementation or its finite controls; parent was sent the concrete construction for implementation/review.

There are `binom(n-1,2)-d` independent pair constraints. This is **quadratic**, even though solution dimension is at most linear. Merely knowing `d<=n-2` therefore does not show that `O(n)` quartet constraints suffice, much less that they can be found cheaply.

Keijsper Section 4's interactive witness loop is different: it starts with a partial `Q`, and in at most `O(n^2)` added quartets forces a cyclic solution space or contradiction. Its output displays only the measured `Q`. An arbitrary cyclic solution can fail additional unknown quartet constraints. To use this loop for the master, one needs an efficient separation/certification procedure for **the full unknown support**, and must charge its oracle queries. Partial consistency is not global recovery.

## 5. Why Boolean support is not automatically a QNet weight function

**Hand-derived obstruction to an observation substitution.** Take a five-leaf ordinary binary tree with the two nontrivial splits `12|345` and `34|125`. A putative additive nonnegative split weight function yielding quartet indicator weight one on every displayed quartet and zero otherwise must put weight one on split `12|345`, because that is the only nontrivial split inducing `12|35`. It must likewise put weight one on `34|125`, by `34|15`. But on `12|34`, both splits contribute, so its additive induced quartet weight is two, contradicting the indicator value one.

One may justify restriction to these two splits: any positive weight on an additional nontrivial split induces some quartet absent from the tree, violating its zero indicator. Trivial split weights induce no resolved quartet and cannot repair the contradiction. Thus the Boolean existential indicator already fails additive circular split weighting in a tree. QNet consistency cannot be invoked by simply assigning one to present quartet topologies. A different numerical measurement or a proved representation conversion is necessary.

## 6. What is still open

The full adaptive optimum remains bounded by inherited `Omega(n log n)` and `O(n^3)`. None of these source comparisons proves a stronger lower bound or a faster entire-class learner.

The affine construction reduces uncertainty about production implementation, and gives a precise alternate attack: learn enough of the structured signed pair graph to obtain a globally valid cyclic vector without examining all triples. It does **not** solve the measurement-selection problem. An all-level extension theorem, a cheap global separating query, or an admitted larger adaptive transcript adversary is still required.

## 11. Process integrity

Precise observation/output hypotheses were checked before transfer. The decisive GF(2) theorem and signed-edge construction were read in primary full text, not inferred from a title. No proof was inspected for the recent Lin paper or the QNet article, and those limits are explicit. Search is targeted, reproducible by the listed source IDs/URLs, and bounded; no systematic-review completeness score or absence-of-prior guarantee is claimed. No new code was run by this contributor.

## 12. Robustness

The common-order corollary is an exact intersection identity and does not depend on finite enumeration, a generic parameter set, maximum level, or a chosen blob decomposition. It assumes binary displayed trees and complete existential support. It does not recover the split union from the anchor table, in agreement with the admitted collision proof. The nonlinear task of finding informative queries remains unresolved; compact answer entropy and a small signed forest cannot be treated as an executable low-query strategy.

## 13. Source retrieval identifiers for the coordinating agent

Primary full text refs: Keijsper university PDF `turn7view0` / detailed Section 4 `turn11view0`; complete preprint HTML `turn11view1`, Theorems 2/3/7 `turn13view1`, Theorem 8 `turn13view2`. Frohn full text `turn5view0` / precise scope `turn6view4`, balanced spine lemma `turn13view3`. Hsu–McConnell `turn10view2`. Laurent–Seminaroti `turn4view3`. Fink–Peters `turn14view2`. QNet university primary abstract `turn10view3`. Lin indexed primary abstract `turn2academia27` / `turn5academia35` (full retrieval failed). These ref IDs are retrieval receipts, not enduring bibliography identifiers; retain URLs/DOIs in published notes.

## 14. Handoff

Parent has been sent the decisive prior, the all-family affine corollary, and the signed-pair algorithm. Next action: implement the parity graph alongside independent graph-derived quartet truth, then attack adaptive learning using a global extension invariant. Preserve the distinction between proving an order-representation theorem, implementing it, and closing the master query optimum.
