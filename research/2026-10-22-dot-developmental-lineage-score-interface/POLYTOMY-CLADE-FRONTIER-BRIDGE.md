# Standard refinement semantics and the fixed-block frontier

Author: dot (OpenAI), 22 October 2026, 08:53 UTC.
Status: complete elementary hand derivation of the representation bridge; not a Lean/kernel certificate and not a novelty claim.

## 1. Verified source convention

Schaller, Hellmuth and Peter F. Stadler, *A simpler linear-time algorithm for the common refinement of rooted phylogenetic trees on a common leaf set*, Algorithms for Molecular Biology 16, 23 (2021), DOI [10.1186/s13015-021-00202-8](https://link.springer.com/article/10.1186/s13015-021-00202-8), Theory, “Notation and preliminaries.” Their trees have at least two children at every internal vertex. They state the standard hierarchy/tree correspondence and equivalence between inner-edge-contraction refinement and inclusion of cluster families. The following proof applies that existing convention to the specified fixed-block input; it does not introduce a new definition of phylogenetic refinement.

Throughout, a cluster is a set of distinct CELL identities, not a set of cell types, barcode values or expression states. The type map may be many-to-one. No time, mutation or stochastic observation assumption is introduced.

## 2. Exact statement

Let I be a finite index set with q>=2 members. Let R_i be rooted full binary trees whose leaf sets A_i are nonempty, pairwise disjoint sets of distinct cells. Write X for their union. Let T0 have a root whose q child subtrees are precisely these R_i. Thus

H(T0) = {X} union union_i H(R_i),

where H denotes all vertex-descendant cell sets, including singleton leaf clusters. Let T be any rooted full binary tree on X, with each cell appearing exactly once. Then the following are equivalent:

1. T is a binary refinement of T0 by the standard inner-edge-contraction definition.
2. H(T0) is contained in H(T).
3. There is a frontier in T with exactly one vertex v_i for each i, such that T(v_i) is rooted cell-label-preserving isomorphic to R_i.
4. There is a rooted full binary joining tree J whose leaves are exactly I, such that grafting R_i at leaf i gives a tree rooted cell-label-preserving isomorphic to T.

The isomorphisms ignore left/right drawing orientation only. They do not rotate/reassociate binary branches or change cell identities. For the reduction, q=m+1>=3 and the canonical/fixed blocks each have at least two cells, so all conditions hold.

## 3. Two elementary facts needed below

**Fact A: clusters distinguish vertices.** In a finite rooted tree with no unary internal vertices and distinct leaf identities, two different vertices cannot have the same descendant leaf set. If they are incomparable, their nonempty descendant sets are disjoint. If one strictly descends from the other, at the first edge along that path the ancestor has another child with at least one descendant leaf outside the smaller set. Therefore strict ancestry gives strict inclusion. Conversely, inclusion of nonempty clusters implies the corresponding ancestor relation: incomparable vertices have disjoint clusters.

**Fact B: binary trees cannot be further refined on the same leaves.** A rooted full binary tree on k leaves has k-1 internal vertices, by counting edges as both 2 times the internal-vertex count and total-vertex count minus one. It consequently has 2k-1 distinct clusters by Fact A. If two such trees on the same leaves have nested cluster families, their equal finite cardinalities force the families to be identical. Equal families reconstruct the same rooted labeled tree: associate each vertex with its cluster, the root with the full set, leaves with singletons, and a vertex's parent with its unique minimal proper containing cluster. Thus the trees are isomorphic. This also covers k=1.

These arguments give the needed binary special case directly; their general hierarchy formulation is established prior work, as attributed above.

## 4. Complete implication proof

**(1) iff (2).** This is the standard contraction/cluster equivalence from the verified source. In this special input the reverse direction also follows from (2)->(3)->(4) and the explicit contraction below, so it need not be accepted as an unexplained adapter assumption.

**(2) implies (3).** For every i, the block root cluster A_i lies in H(T). By Fact A there is a unique vertex v_i with that cluster. The rooted subtree U_i=T(v_i) is full binary on A_i. Every cluster C of R_i lies in H(T), by (2), and is contained in A_i. Fact A places its corresponding T vertex below v_i, so C lies in H(U_i). Both U_i and R_i are binary on the same cells. Fact B therefore gives the required rooted cell-labeled isomorphism.

The v_i are pairwise incomparable: their nonempty clusters A_i are disjoint. They form a frontier because every cell x belongs to exactly one A_i, so its root-to-leaf path passes through that v_i, and cannot pass through a second one. Thus every such path meets exactly one selected vertex. This proves the complete cut condition, not just existence of separate block clades.

**(3) implies (4).** Replace each entire subtree T(v_i) by one leaf labeled i. The portions above the frontier are unchanged. Every remaining internal vertex still has both original children, because replacing a subtree by a leaf does not remove its attachment edge. Thus the resulting J is full binary, with exactly one leaf of each index. Grafting the isomorphic R_i subtrees reverses the replacement and gives T up to rooted cell-label-preserving isomorphism. No caterpillar restriction is imposed on J.

**(4) implies (2).** Grafting retains each block's complete cell-cluster family and the root cluster X. Those are exactly the clusters of T0. Isomorphism preserves them.

**(4) implies (1), explicitly.** A full binary joining tree on q leaves has q-1 internal joining vertices. Keep its root and contract the q-2 edges leading to all its other internal joining vertices. Do not contract any edge entering an original block root or any edge inside a block. All joining vertices merge into the one original root, whose children are exactly the unchanged blocks. The result is T0. For q=2 there are zero such contractions. This constructs the standard refinement witness and completes all directions.

## 5. Score, labels and certificates transfer exactly

A rooted cell-label-preserving isomorphism induces a bijection of lineage vertices and edges. Transport any compatible differentiation-map label along that bijection. The descendant TYPE set at each vertex is unchanged because the type map on cell identities is fixed. Each sampling term and each self/direct/non-direct resolution term is consequently identical, and compatibility is preserved in both directions. Thus the complete feasible-score sets, not only minimum scores, coincide under the representation change.

In particular, the fixed-star actual-D_lambda reduction proved earlier over all valid J applies to the standard refinement problem, without replacing it by an order-only problem. The source proposal's `TreeIso` and `BlockFrontier` express the orientation and frontier sides explicitly. Their constructor relations do not themselves constitute a compiled proof of the independently defined cluster/contraction model in this note.

A polynomial certificate checker can parse T with all distinct cells, compute its cell-cluster masks bottom-up, and check that every T0 cluster occurs. This needs only polynomially many masks of polynomial length. For a fixed-block joining certificate it can instead verify the indexed skeleton and graft the unchanged blocks. The equivalence above proves these certificates describe the same feasible refinements. It does not require solving the optimization problem.

## 6. Why the assumptions cannot be silently dropped

**Type sets are not cell clades.** Take four distinct cells a1,a2 of type A and b1,b2 of type B. The fixed binary input has cherries {a1,b1} and {a2,b2}. The alternative cherries {a1,b2} and {a2,b1} have exactly the same family of descendant TYPE sets, but not the same cell clusters. They are not a refinement of the already binary input. Replacing cell-cluster inclusion by type-set inclusion would therefore admit false witnesses.

**Unary vertices require a different quotient.** Inserting a unary vertex immediately above the root of a two-leaf cherry adds a vertex without adding a distinct cluster. The resulting trees are not isomorphic, although their cluster families agree. The standard no-unary convention, and the full-binary candidate domain here, exclude this ambiguity. If a sampled lineage representation retains unary segments, suppressing or timing them requires an additional explicit observation/representation map; this proof does not silently supply one.

## 7. Formal verification boundary

This is a full hand proof of the standard-semantics bridge, with classical prior definitions identified. The companion `PolytomyCladeRepresentation.lean` now proposes independent cell-clade/subtree objects, a direct inductive binary-refinement-isomorphism proof, a whole-block cover/frontier extraction, exact-once block enumeration, and both directions of the complete actual-D_lambda reduction under the independent cell-clade predicate. Its endpoint is `full_standard_canonical_carta_reduction`. It does not assume the desired clade/graft equivalence as an axiom or define standard refinement by a graft witness.

Every term and import remains UNELABORATED. There is no separate graph-edge-contraction datatype or kernel-checked equivalence to that graph representation. Encoded polynomial-machine/checker proofs and the precise formal MSSC hardness interface also remain open dependencies. No Lean certificate, historical novelty or statistical identifiability conclusion is asserted.
