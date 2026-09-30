# Independent check: exact anchored reconstruction of common orders

Date: 2026-09-30. This reviews the construction derived by the coordinating agent. It does not claim a new optimal adaptive query bound or a new full-four-score theorem.

## Verified theorem

Let \(\mathcal T\) be any nonempty family of binary unrooted phylogenetic trees on a finite set \(X\), and let \(Q\) be the union of their displayed quartets. Fix \(r\in X\), write \(Y=X\setminus\{r\}\), and define, for distinct \(x,y\in Y\),

\[
I_{xy}=\{x,y\}\cup\{z\in Y\setminus\{x,y\}:rz\mid xy\notin Q\}.
\]

Then a linear order of \(Y\) makes every \(I_{xy}\) consecutive if and only if the circular order obtained by inserting \(r\) at the cut is compatible with every tree in \(\mathcal T\). Consequently the family of *all* common circular orders is represented exactly by a PQ-tree constructed from these sets, or the consecutive-ones procedure rejects if no common order exists.

This theorem is independent of network level, galledness, blob decomposition, source normalization, and choice multiplicities. Binary tree display is the relevant hypothesis.

### Proof check

Root each \(T\) at the neighbor of the removed leaf \(r\), and let \(C_T(x,y)\) be the descendant leaf set of the lowest common ancestor of \(x,y\). Since the original tree is binary,

\[
rz\mid xy\in Q(T)\quad\Longleftrightarrow\quad z\notin C_T(x,y).
\]

Taking absence from the union gives

\[
I_{xy}=\bigcap_{T\in\mathcal T}C_T(x,y).
\]

If an order is common to the trees, each \(C_T(x,y)\) is an interval after cutting at \(r\). Their nonempty intersection is an interval, proving necessity.

Conversely, suppose all \(I_{xy}\) are intervals. If some rooted clade \(C\) of some \(T\) is not an interval, there are \(x,y\in C\) and \(z\notin C\) with \(z\) between \(x,y\). But \(C_T(x,y)\subseteq C\), so \(I_{xy}\subseteq C\). The set \(I_{xy}\) contains \(x,y\) and excludes \(z\), contradicting consecutiveness. Therefore every clade of every tree is an interval. This is precisely common circular split compatibility after adjoining \(r\).

No all-size gap was found in either direction. Singleton clades and the whole set impose no extra restriction. For \(|X|\le3\), the argument is vacuous or trivial, as required.

## Constructive complexity and limits

Query all \(\binom{n-1}{3}\) four-sets containing \(r\). Each exact support answer provides the three membership bits needed by the definition above. The \(\binom{n-1}{2}\) sets have total incidence at most \(O(n^3)\). Standard consecutive-ones/PQ-tree machinery therefore constructs the complete common-order space in polynomial time and \(O(n^3)\) input-processing work using standard linear-in-incidence implementations.

The order-learning queries are nonadaptive. Any subsequent known-order split-recovery procedure whose queries depend on the returned order makes the **combined reconstruction adaptive**. The order theorem itself does not show that the anchor table determines the original full split union, and it does not establish an optimal adaptive bound. An \(\Omega(n^3)\) lower bound for nonadaptive *split-union recovery* cannot be relabeled as a lower bound for returning any common order.

The coordinating agent's candidate-order boundary test gives another subsequent recovery route using \(O(n^2)\) quartet queries. For the admitted galled planar source class, the previously proved supplied-order sparse procedure gives its own subsequent recovery bound. Their composition with this theorem is a constructive \(O(n^3)\) upper bound, with the remaining adaptive optimum kept open.

### Anchor information can force virtual intervals

Here is an exact counterexample to identifying order constraints with displayed splits in an arbitrary tree family. On \(X=\{0,1,2,3,4\}\), root at the neighbor of \(r=0\), and take

\[
T_1=(1,(2,(3,4))),\quad T_2=(((1,2),3),4),\quad T_3=(1,((2,3),4)).
\]

Both families \(\{T_1,T_2\}\) and \(\{T_1,T_2,T_3\}\) have the same two-topology support on **every quartet containing 0**. For a sorted anchored quartet \(0abc\), those two topologies are \(0a\mid bc\) and \(0c\mid ab\). But on \(1234\), the first family displays only \(12\mid34\), while the second also displays \(14\mid23\). Correspondingly the second split union gains \(23\mid014\). All three trees admit the circle \(01234\).

Already for the first family, \(I_{23}=\{2,3\}\): the two LCA clades are \(\{2,3,4\}\) and \(\{1,2,3\}\). Thus the intersection family correctly forces a common interval which is not itself a displayed edge split. This is a generic tree-family example; no claim is made that the second family is the complete display family of an admitted source network.

## Prior-first assessment

The inherited components are explicit:

- Rooting a split system away from a reference taxon and recognizing interval clusters by PQ-trees are classical. The checked application in Huson–Cetinkaya (2023), *Visualizing incompatibilities in phylogenetic trees using consensus outlines*, starts with the explicit split union of supplied trees, then inserts split sides away from a fixed taxon into a PQ-tree. Its Methods describe this directly. Primary source: <https://www.frontiersin.org/journals/bioinformatics/articles/10.3389/fbinf.2023.1155286/full>, DOI 10.3389/fbinf.2023.1155286.
- Gambette–Huber–Scholz (2017), *Uprooted Phylogenetic Networks*, and Kleinman–Harel–Pachter (2013), *Affine and projective tree metric theorems*, supply split closure, rooted split/cluster transforms, and prepyramid/PQ representations. Independent source inspection found no existential quartet-union-to-\(I_{xy}\) construction in those texts. Exact inspected locations: Uprooted Section 3 after Theorem 1; Kleinman preprint Section 2, Definition 10, Proposition 6, and the proof of Proposition 10. The last location defines minimal containing clusters by intersection, so the general pair-hull interval principle may already be standard. Primary sources: <https://pmc.ncbi.nlm.nih.gov/articles/PMC5552900/>, DOI 10.1007/s11538-017-0318-x; <https://arxiv.org/abs/1103.2384>, DOI 10.1007/s00026-012-0173-2 (verified at the authors' Caltech repository <https://authors.library.caltech.edu/records/h7bt6-gaq50>).
- Rhodes et al., *Identifying circular orders for blobs in phylogenetic networks*, Theorem 5.3, prove order identifiability for the binary outer-labeled planar blob setting, and explicitly say the identifiability argument does not suggest an efficient algorithmic construction. Primary source: <https://arxiv.org/html/2402.11693v2>.
- Frohn et al., <https://arxiv.org/html/2409.06034v2>, supply an \(O(n\log n)\) quartet-query reconstruction for level-one networks and an \(O(n^3)\) arbitrary-level tree-of-blobs reconstruction. These do not establish an arbitrary-level common-order learner with the level-one bound. Their \(\Omega(\ell n)\) Figure 5 adversary is excluded from the present source class by the separately inspected argument in `LOWER-BOUND.md`: for \(\ell\ge4\), four hybrid labels admit all three resolved quartet topologies, contradicting outer-labeled planarity. The stronger adjacent-copy argument there excludes \(\ell\ge3\). The earlier assertion that this particular adversary fails galledness was withdrawn after inspection of the actual Figure 5; it is not used. Frohn's lower bound also uses a split-only oracle, so no direct rich-mask lower bound follows.

The exact anchored compression of the complete common-order space is therefore a **candidate new observation relative to inspected primary sources**. PQ-trees, the split-to-cluster transform, interval closure, and common-order recognition themselves are not new. This search does not establish historical novelty.

## Unfinished target

The maximal adaptive question remains: can the whole admitted all-level class be reconstructed, including a compatible order and full split union, with near-linear or \(O(n\log n)\) exact-support queries, or is there an admitted obstruction requiring more? Frohn's centroid idea survives at the tree level, but the balanced-edge argument does not transfer directly to a high-degree circular blob: an incident edge may remove only \(1/d\) of the mass. Balanced consecutive port groups are virtual partitions, so a new constant-cost support-mask test with a global extension invariant is required. That is an adaptation gap, not an impossibility proof.
