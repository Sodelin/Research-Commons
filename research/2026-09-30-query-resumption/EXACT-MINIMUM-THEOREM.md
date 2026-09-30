# A uniform exact finite-size query optimizer for the admitted source class

Contributor: Codex `minimal_projection`, EXACT-MINIMUM-THEOREM-20260930.
Date: 2026-09-30 UTC. Status: conditional all-size hand proof, independently
reviewed normalization core. No implemented all-size census/optimizer,
closed formula for q(n), efficient optimization, or historical novelty claim.

## 0. Exact result and its computational meaning

For every n>=4, the exact deterministic adaptive minimum q(n) for
EXACT-QUERY-01 is **uniformly computable**: enumerate a bounded finite set
of actual admitted source graphs, deduplicate their complete oracle
profiles, and solve the exact decision-tree recurrence. The optimizer
returns an optimal query policy plus independently checkable upper and
lower certificates. It does not merely assert that a minimum exists.

The decisive structural step is a bounded **actual-source representative**
theorem. Every admitted source has another admitted source with the same
complete support and full split union, at most `8n-14` unrooted vertices
(plus at most one rooting vertex), and no unbounded two-port chains.
A conservative enumeration cap of `20n` rooted vertices is therefore safe.
This avoids assuming an unproved converse for arbitrary compact codes.

The solver is an explicit exponential-time specification, not an efficient
closed expression for q(n). It has not been implemented or run beyond
the separately preserved small-profile optimizers. It complements an
asymptotically optimal query learner rather than proving that selecting
the exact finite-n best decision tree is polynomial-time.

## 1. Target, facts inherited, and finite admission tests

The source is a finite binary semi-directed LSA-rootable, outer-labeled
planar, galled network on n labeled taxa, arbitrary level and blob count.
Each queried four-set returns all distinct displayed quartet topologies.
The required output is the union of nontrivial displayed splits and any
compatible circle. Switching counts, probabilities, branch lengths,
biological calibration and the original graph are outside this target.

The proof inherits the audited source facts pinned in
[SPLIT-COUNT.md](../2026-09-30-root-exact-query/SPLIT-COUNT.md):

1. Every cut edge has taxa on both sides. The tree of blobs therefore
   has no non-taxon leaves. Non-leaf blob nodes have at least two ports.
2. Each retained branching blob can be capped at its ports as an actual
   admitted source bloblet. Opening its hybrids gives a binary plane
   occurrence tree with m port labels and `M=m+h<=2m` tips, each duplicated
   pair adjacent; folding reconstructs that actual capped blob graph.
3. Local switchings extend independently; global splits are precisely
   bridge splits and full lifts of local port splits. Two-port blobs have
   only the unique two-terminal local tree and add no extra taxon split.

These are source-to-representation facts. The proof does not assume that
every arbitrary occurrence tree or abstract tree family folds into an
admitted source.

For a finite candidate rooted graph, admission is decidable by finite
checks of the declared class: binary degrees, directed acyclicity and
root/taxon reachability; the specified galled/reticulation-cycle conditions;
root as the least stable ancestor of all taxa; and existence of a planar
embedding with all taxon leaves on the outer face. One may use exhaustive
rotation systems and finite paths/cycles/dominator computations rather
than presume a particular production validator. The checks must apply
the exact source definitions from the pinned structural audit.

Enumerating rooted partners rather than guessing a root in each
semi-directed graph handles LSA-rootability directly. Forgetting their
ordinary edge directions gives the associated semi-directed source.

## 2. Bounded actual-source representative theorem

**Theorem.** Under the inherited facts above, each admitted n-taxon source
has an admitted source with the same full split union and complete quartet
support, using at most `8n-14` vertices after suppressing its rooting vertex,
and at most `8n-13` vertices in a rooted partner.

### 2.1 Construction from the given actual source

Take an LSA-rooted binary partner and a source plane embedding. Contract
blobs to obtain the tree of attachments, counting singleton tree vertices
as the corresponding trivial branching blobs. Suppress non-taxon
degree-two nodes to obtain the reduced tree R. Keep every branching blob
and every taxon leaf. Replace each maximal chain of two-port blobs and
degree-two attachment nodes by one ordinary bridge joining its endpoints.
If the rooting vertex is inside a deleted chain, place a new root midway
on its replacement bridge. Otherwise retain the existing root.

This uses actual remaining blob subgraphs from the original source. It
does not manufacture a graph from an arbitrary unvalidated compact code.

### 2.2 Binary degrees, directions, and acyclicity

Each deleted chain has exactly two external incidences. Replacing it by
one bridge leaves the degrees of both retained endpoints unchanged.
Existing hybrids and their parent/child incidences remain unchanged.
All surviving vertices retain their original tree or hybrid type. A
new root subdivides a bridge and has two outgoing children, as required.

In a rooted graph, each cut bridge separates a unique root-side component
from a component not containing the root, so its direction points away
from the root-side component. For a chain not containing the root, one
external port is its entry and the other its exit. A directed path from
entry to exit exists because the root reaches the taxon-bearing component
beyond the exit. Direct the replacement bridge from entry to exit. If
the root lies inside the chain, both external ports point out into their
two taxon-bearing components; the new root likewise points out to each.

There can be no new directed cycle across a replacement bridge: its
underlying edge belongs to the attachment tree. Cycles wholly inside
retained blobs keep their original directions. Thus acyclicity persists.

### 2.3 LSA root preservation

If the root is retained, every old root-to-taxon path projects to a new
path by collapsing deleted two-port traversals. Conversely every new
root-to-taxon path expands by inserting an entry-to-exit directed path
in each replaced chain. Hence, for every retained vertex v and every
taxon x, existence of a root-to-x path avoiding v is preserved in both
directions. The stable-ancestor predicate at retained vertices is
unchanged. Because the original root was the LSA of all taxa, no other
retained vertex becomes their common stable ancestor after contraction.

If the old root is deleted, each outside component has at least one
taxon by the positive-cut-edge premise. The two children of the new
bridge root lead to disjoint attachment-tree components. Every other
vertex lies on one side and is absent from the paths to taxa on the
other side. Thus no proper descendant is a stable ancestor of all
taxa, and the new root is their LSA.

### 2.4 Galledness and outer-labeled planarity

Every undirected cycle is inside one blob. The replacement creates a
bridge and removes only whole two-port blob regions, so it creates no
new cycle, no parallel route, and no new cycle overlap. The remaining
galled configuration in each retained blob is the original one with
the same hybrid directions and attachment incidences.

In the original embedding each deleted two-terminal region can be
replaced by a simple curve following a connecting path through that
region. It meets the remaining graph only at its two boundary endpoints.
Deleting the other edges opens faces; it cannot force an original
outer-face taxon into an interior face. Root subdivision also leaves
the outer-face property unchanged. Hence an outer-labeled planar
embedding remains. This is a source embedding argument, not a claim
that arbitrary compact-code foldings are planar.

### 2.5 Full target preservation

The reduced attachment tree R has the same lifted bridge bipartitions.
Retained branching blob port components have the same taxa, local graphs
and local displayed split unions. Every removed two-port blob supplies
only its unique two-terminal local tree. By independent local switching
extension and the inherited global split-accounting identity, deleting
these chains removes no split and creates no split. Thus the complete
global union is identical.

For any binary-tree family, a quartet topology belongs to its complete
support exactly when some full split in its union restricts to that
topology. Therefore equal unions give equal complete oracle profiles.
The compatible-circle space is also identical. No assertion about
switching probabilities or physical metric equality is made.

### 2.6 Vertex bound

Let R have n leaf taxa and q branching nodes. Each branching node has
degree `m_B>=3`, and

    q <= n-2,
    sum_B m_B = n+2q-2.

The capped actual bloblet's occurrence tree has `M_B=m_B+h_B<=2m_B`
tips and `2M_B-2` vertices. Folding a duplicated pair replaces two
physical occurrence tips by one hybrid vertex and its capped port leaf,
so it does not change this vertex count. Suppress the at most one
global rooting vertex for this count.

Assemble the q capped actual blob graphs along R. Each of the q-1
internal attachment edges removes its two artificial cap tips and
joins their retained neighbors by a bridge. Taxon port tips remain as
the original n leaves. Consequently

    V = sum_B(2M_B-2) - 2(q-1)
      <= 4 sum_B m_B - 4q + 2
       = 4n + 4q - 6
      <= 8n - 14.

Restoring or introducing one rooting vertex gives `V_rooted<=8n-13`.
The conservative `20n` bound safely covers this count. QED.

## 3. Exact admission census: why the converse is now justified

For input n, enumerate all finite labeled rooted directed graphs on at
most 20n vertices, with the given n taxon labels and finitely numbered
auxiliary vertices. Filter them through the exact finite admission tests
in Section 1. For each surviving rooted source, enumerate all parent
choices at its hybrids, prune/suppress to displayed binary trees, and
compute its full nontrivial split union and all quartet support answers.
Deduplicate equal complete profiles, keeping one admitted graph and
one full target as a witness for each.

If the declared graph convention permits parallel edges, enumerate its
allowed edge multiplicities too; binary degree bounds make that domain
finite. The enumerator must not silently substitute a simple-graph
convention for a more permissive source definition.

Call the resulting set P_n. Every enumerated profile is genuinely source
admitted because its graph was checked. Conversely Section 2 gives a
bounded admitted representative for every possible original source
profile, so every actual profile appears. Hence P_n is **exactly** the
admitted profile set, not merely an overinclusive compact-code family.

In particular profile membership is decidable: enumerate this finite
census and check equality. Without Section 2, an unbounded graph search
would only semidecide membership, and knowing a short target code would
not certify when to stop searching for missing source realizations.

## 4. Uniform exact minimum and optimal policy

Let H be a nonempty subset of the exact P_n. For a four-set Q and
possible answer a, let H(Q,a) be its answer class. Define

    D(H)=0                              when |H|=1,
    D(H)=1+min_Q max_a D(H(Q,a))         otherwise,

where the minimum uses queries that genuinely partition H. Distinct
admitted profiles have distinct full split unions: the inherited exact
common-circle reconstruction recovers the union from the profile.
Thus a correct leaf must identify one profile; its stored union and a
constructible compatible circle give the required output.

Each child of a partitioning query is strictly smaller, so memoized
recursion terminates. The usual first-query argument proves optimality:
any algorithm chooses some Q and must handle its hardest answer class;
choosing a minimizer and optimal child policies attains that value.
Therefore

    q(n)=D(P_n)

is computed exactly, and the minimizing query at each state gives an
actual deterministic optimal adaptive decision tree for every finite n.
No supplied circular order or tree of blobs is required by this policy.

The algorithm is uniform in n; it is not a collection of unexplained
hardcoded finite minima. Its preprocessing and stored policy can be
prohibitive. With L=`binomial(n,4)`, each reachable candidate state is
specified by a partial assignment of at most L queries, each with at
most six admitted answers. There are at most `7^L` such specifications.
Together with finite bounded graph enumeration and exact switching
evaluation this provides a finite explicit exponential computation
bound; polynomial-time optimization is not claimed.

## 5. Reviewable proof certificates

An exact value k must accompany two distinct certificates:

- **Upper certificate:** a query decision tree or DAG of depth k, with
  every admitted answer branch represented, and each terminal state
  carrying its correct split union and compatible circle.
- **Lower certificate:** for a candidate state H claimed to need more
  than d queries, list for **every** available Q an answer a whose child
  H(Q,a) needs more than d-1. At d=0, supply two surviving profiles with
  different split outputs. Recursive certificates may share states.

A checker recomputes each answer partition and verifies the recurrence,
all state inclusions, terminal outputs and root depth. Graph witnesses
certify that lower-bound candidates are admitted. Exact census completeness
comes from the bounded-representative proof, rather than from observing
that a finite search happened to stop finding new graphs.

The independently reviewed six-profile N2/rotated-N1 proof already
certifies `q(5)=5`. This note specifies how to compute and certify each
other finite q(n); it does not list uncomputed values or turn the
recurrence into a closed numerical formula.

## 11. Process integrity and actual execution

The source-normalization core was independently accepted by both
`boundary_review` and `adaptive_construction`, conditional on the pinned
source facts. Its path projection/expansion, root-in-chain case, degree,
cycle, outer-face and profile-preservation arguments were exposed
explicitly. The first written review is
[EXACT-PROFILE-REVIEW.md](EXACT-PROFILE-REVIEW.md); the second reviewer
also independently reproduced the vertex bound and accepted the finite
census/Bellman computability deduction.

Actual computation remains the previously executed five-taxon minimax
and graph-switching controls. The all-size bounded graph census,
admission validator suite, optimizer and certificate checker above have
**not** been implemented or executed. The result is a conditional
constructive theorem/specification, not machine verification or a
reported execution of those unperformed steps.

## 12. Robustness and exact completion boundary

The finite exact solver depends on actual-source normalization, especially
the source-to-port occurrence representation and independent local
switching extension. If either source fact failed, the bounded admission
census could omit profiles and its claimed upper certificates would be
invalid. The independent normalization review does not replace those
upstream source audits.

Accepting Section 2 establishes a computable exact minimax function and
policy, despite arbitrary hidden chain lengths. It does not establish
an efficient optimizer, a simple exact recurrence in n alone, or values
not yet computed. A theorem matching asymptotic Theta(n log n) query
bounds is compatible with finite-size q(n) still having this much harder
optimization problem. Mathematical computability, efficient learning,
and a computed finite answer are separate completion claims.
