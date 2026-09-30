# Port-compressed reticulation counts

Contributor: Codex normalization-count subagent, 2026-09-30 UTC.
Status: hand-derived graph-count proof with independent finite graph checks.
No biological replacement theorem, CF preservation, minimum equivalent
realization, or historical priority is claimed.

## Prior-first and exact conventions

The Commons candidate at main `eec5b7c2c15adf621b2ff99a8938626a32140e1a`
uses the conditional bound `3n-6` after two-port blobs have been eliminated.
Its independent audit accepts the degree argument conditionally but leaves
simultaneous CF-preserving replacement and source admission to the biological
normal-form owner.

Published earlier galled-network work already gives the bound `2n-2` for
its rooted simple-DAG class: Gunawan, DasGupta and Zhang, *A decomposition
theorem and two algorithms for reticulation-visible networks*, Information
and Computation 252 (2017), DOI `10.1016/j.ic.2016.11.001`; author preprint
`arXiv:1603.08655`. Chang, Fuchs and Yu, *Galled Tree-Child Networks*,
AofA 2024, DOI `10.4230/LIPIcs.AofA.2024.8`, Definition 1 explicitly uses
simple DAGs, and Remark 4 records this sharp earlier bound. Therefore linear
counting is prior, not a new general discovery. The refinements below concern
the precisely port-compressed semi-directed class. The original Commons
multigraph contract and standard rooted simple-DAG contract must not be
silently conflated when discussing arbitrarily many serial bigons.

Holtgrefe et al., DOI `10.1007/s11538-025-01549-4`, Definitions 2.1-2.3:
the rooted binary root has outdegree two and equals the LSA of all taxa;
the semi-directed graph suppresses that root; a blob articulation node is
incident to a cut edge; outer-labeled planar means only the leaves must lie
on the unbounded face. Interior tree vertices are allowed. In the binary
galled class every hybrid is an articulation node, with its child edge a
cut edge. These definitions permit the exterior-cycle constructions below.

## Rootward-port lemma

Fix any source-admitted rooted acyclic LSA realization. For a non-root blob
B, its unique cut edge toward the root enters B. This port cannot be the
child port of a hybrid in B: that edge is oriented away from the hybrid.
Thus a p-port non-root blob has at most p-1 hybrids. Distinct hybrids have
distinct child ports. A blob containing the root can have p hybrids; there
is at most one such blob. If the suppressed root lies on a cut edge rather
than inside a retained blob, there is no exceptional blob.

The LSA convention excludes an empty rootward stem. Every cut edge separates
nonempty taxon sets; consequently the suppressed tree of blobs has exactly
n labeled leaves and no unlabeled leaf. Degree-two root subdivisions are
suppressed in this counting tree.

## After eliminating all nontrivial two-port blobs

Assume the resulting graph is still in the declared class and contains no
nontrivial two-port blob. Let b be its nontrivial blob count, t its ordinary
trivalent internal tree-vertex count, and p_B the degree of a blob in the
unrooted tree of blobs. Every p_B is at least three. The tree identity is

    sum_B (p_B-2) + t = n-2.

Write epsilon=1 if the root is inside a retained nontrivial blob, and zero
otherwise. The rootward-port lemma gives

    r <= sum_B (p_B-1) + epsilon
      = n-2-t+b+epsilon.

Since b<=n-2-t,

    r <= 2n-4-2t+epsilon <= 2n-3.

If the root is outside all retained blobs, the corresponding bound is
`r<=2n-4`. This argument strengthens the conditional `3n-6` bound. It does
not prove that any proposed CF compression meets the premises.

## After topology-only elimination of two- and three-port blobs

For the surviving high-port blobs assume p_B>=4. Their switched unrooted
local tree topology is the only component to be counted here; the separate
switching-preservation lemma must justify the actual compression. Let s be
the number of surviving hybrid identifiers. The same identity implies

    b <= floor((n-2-t)/2),
    s <= n-2-t+b+epsilon
      <= n-1+floor((n-2)/2)
      = floor(3n/2)-2.

If the root is outside all surviving high-port blobs, reduce this last
universal bound by one. These bounds count surviving identifiers under the
specified port compression, not all original historical hybrid controls.

## Source-admitted attaining constructions

Root d-port/d-hybrid block, d>=3: start with a plane unrooted binary tree K
whose degree-one vertices U_0,...,U_(d-1) occur in contour order. Add the
exterior cycle

    U_i -- H_i -- U_(i+1 mod d),

and add an outward child taxon/port at each H_i. Insert a binary root R on
any K edge; orient K away from R and every U_i-to-H_j arc toward its hybrid.
Each U_i now has one incoming tree edge and two outgoing hybrid arcs.
Other K vertices are ordinary binary tree vertices. All labels are exterior;
internal K vertices may lie inside the cycle, as allowed by outer-labeled
planarity. Each hybrid's two parent arcs together with the K path between
its parents form a cycle containing no other hybrid arcs. All core edges
lie on cycles, so this is one nontrivial blob.

The two components of K after deleting the root edge each contain at least
one U_i. Consecutive cyclic U pairs cross this partition at least twice, so
some hybrid has parents on both root branches. No descendant of either root
child can dominate all root-to-taxon paths. Hence R is the LSA of all taxa.
This block has d ports and d hybrids. For d=3 its core is a subdivided K4;
that is permitted because the source requires exterior labels, not exterior
positions for every vertex.

Non-root p-port/(p-1)-hybrid block, p>=3: take the preceding cycle-and-tree
construction with q=p-1 hybrids (q=2 uses K consisting of one U_0-U_1
edge). Subdivide the outer parent arc U_0-H_0 by a new tree node D, attach
the ordinary external rootward port to D, orient D to U_0 and H_0, and
orient K away from U_0. This remains binary, acyclic, galled, and
outer-labeled planar. Its rootward port is ordinary and all other p-1 ports
are hybrid child ports. Grafting it onto any descendant taxon replaces one
taxon by p-1 taxa, adding p-2 taxa and p-1 hybrids. This does not change the
existing root's LSA property, as paths to that replaced taxon acquire only
additional common descendants.

For n>=4 the no-two-port bound is attained by a root d=3 block and n-3
successive non-root p=3 blocks: r=3+2(n-3)=2n-3. No nontrivial two-port blob
is present.

For even n>=4 the high-port count is attained by a root d=4 block and
(n-4)/2 non-root p=4 blocks. For odd n>=5 use a root d=5 block and
(n-5)/2 non-root p=4 blocks. The resulting s is exactly floor(3n/2)-2 and
every nontrivial blob has at least four ports.

Attainment establishes sharpness among graphs satisfying the specified
port-normalization premises. It does NOT prove minimum reticulation number
among every graph with the same Q/S or quartet CFs. A four-port blob with
several hybrids can have the same quartet support as a one-hybrid four-cycle;
stronger within-blob normalization remains a separate obligation.

## Executed checks

`normalization_count_audit.py` builds both attaining families for n=4,...,20.
All 34 instances passed exact binary-degree, DAG/reachability, LSA-dominator,
bridge-defined blob, port-degree, and reticulation-count checks. The receipt
is `normalization_count_receipt.json`. Planarity and galledness are supplied
by the construction proof above, not certified algorithmically by this
script. No CFs or coalescent replacement laws were computed.

## Process and robustness assessment

11: Prior bounds and definition differences were checked before proposing
novelty. The count is independent of the biological replacement proof, and
all root conventions are explicit.

12: The upper bounds and attaining graphs concern the same graph class and
same specified compression. Their inference does not extend to globally
minimum equivalent realizations, original historical control identities, or
CF-preserving compression without the missing interface theorem.
