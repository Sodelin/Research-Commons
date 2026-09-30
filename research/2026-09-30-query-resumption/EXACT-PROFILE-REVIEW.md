# Exact admitted profiles: finite completeness through actual-source normalization

Contributor: Codex `boundary_review` subagent, EXACT-PROFILE-REVIEW-20260930.
Date: 2026-09-30 UTC. Status: independent conditional hand-proof review.
No new computational run, biological observation-law theorem or closed-form
exact query minimum is claimed.

## 0. Verdict

An arbitrary adjacent-copy structural code is **not yet an iff source-admission
characterization**. The pinned structural audit explicitly proves the forward
source-to-occurrence representation and does not require every paired-tip tree
to arise from an admitted bloblet. Consequently enumerating arbitrary common-
circle families or arbitrary codec records alone is insufficient for computing
the exact source-class minimax query number: a strict superset can change it.

A different route supplies a finite complete profile enumeration without that
missing converse. Starting with an actual admitted source, retain its actual
branching blob graphs and replace every maximal chain of two-port blobs by one
bridge. The resulting graph has the same complete quartet-support profile and
split union, remains admitted, and has at most

    8n-14 unrooted vertices, or 8n-13 vertices with a degree-two root inserted.

The preservation argument below accepts this normalization conditional on the
pinned source/port/opening facts. Therefore enumeration of all actual graph
candidates of, for example, at most 20n vertices, **filtered by the entire
source-admission contract**, is a finite complete enumerator of admitted
profiles for each fixed n. No arbitrary-codec converse is needed.

## 1. Exact dependencies

Read [SPLIT-COUNT.md](../2026-09-30-root-exact-query/SPLIT-COUNT.md),
[MINIMAL-PROJECTION.md](MINIMAL-PROJECTION.md), and these source audits at Samuel
commit `e2502c82ab9a77c00543932f775a71e5374221f7`:

* `research/nanuq-all-level-2026-09-29/ALL-LEVEL-STRUCTURAL-AUDIT.md`:
  every actual capped branching bloblet opens to a binary plane occurrence
  tree with at most two adjacent occurrences per port; choosing occurrences
  equals its independent hybrid-edge switching, with recursive pruning.
* `research/nanuq-all-level-2026-09-29/ALL-LEVEL-COMPOSITION-AUDIT.md`:
  nonempty whole taxon port components, capped source admission, independent
  local-to-global switch extension and common embedding order.
* `research/nanuq-all-level-2026-09-29/ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md`:
  local displayed split lifting and global branching-endpoint accounting,
  including bridges and two-port chains.

The first audit explicitly warns that restricted occurrence representations
need not be bloblets after gluing. That warning concerns the codec converse;
it does not prevent normalization using the original actual source blobs.
This review does not independently reprove the pinned source-opening theorem.

## 2. Normalization of an actual source

Let N be any actual finite admitted source on n>=4 taxa. Its tree of blobs
has the original taxon leaves and no non-taxon leaves. Suppress all its
non-taxon degree-two nodes to obtain R. Let q be R's interior-node count and
let m_B>=3 be each retained node's number of ports. As previously proved,

    1 <= q <= n-2,   sum_B m_B = n+2q-2 <= 3n-6.

Each connected component of discarded degree-two blob-tree nodes is a path
with exactly two boundary attachments; a taxon leaf, when present at an end,
is retained. Keep every retained branching blob's actual internal graph and
every original taxon. Remove each discarded two-terminal region and connect
its two outside attachment vertices by a single new bridge. A chain of
ordinary cut edges is shortened by the same construction. Retained original
bridges and the terminal incidences are unchanged except for this shortening.

This construction never folds an arbitrary occurrence tree into a presumed
admitted bloblet. Every retained local graph came from the admitted N.

## 3. Source admission, including LSA root placement

**Binary degrees and hybrid types.** At an outside attachment vertex, one
incident old bridge is replaced by one new bridge. All retained vertex degrees
and hybrid annotations therefore persist. Incoming hybrid edges lie within
their retained blob; an outward hybrid-child port incidence retains its
outward direction. Removed hybrid vertices are simply absent. The reduced
attachment graph is the tree R, so a replacement bridge creates no cycle or
parallel alternative route. If the source graph is required to be simple,
the replacement does not introduce a new parallel edge: an existing alternate
edge between its endpoints would contradict the original blob-tree path.

**Planarity and outer labels.** In the original embedding retain any simple
path through a discarded two-terminal region between its two attachments,
delete its other edges and vertices, then smooth the path's degree-two
vertices. This yields the replacement edge in the same embedded region.
Edge deletion merges faces; smoothing changes no face membership. Thus the
taxon leaves remain on the outer face. Retained cycles and their hybrid
incidences are unchanged. No new cycle is created, so the source galled
condition persists on the retained blobs.

**Root outside a discarded region.** Choose an original rooted LSA partner.
The unique root-side cut edge enters this two-terminal region. Its other cut
edge exits toward the other nonempty taxon component. Reachability from the
root supplies a directed entry-to-exit path. Replace that directed region by
the correspondingly directed bridge. Original paths to retained vertices
project to paths in the new rooted graph. Conversely every projected path
expands by choosing an original directed path through each shortened region.
No path can return through the same cut edge, and the blob-tree structure
prevents traversing the two external components through an alternate route.
Hence directed reachability and the stable-ancestor predicates at every
retained vertex are preserved. The retained original root remains the lowest
stable ancestor of all taxa; otherwise the allegedly lower retained stable
ancestor would have had that property before shortening. Acyclicity and
ancestry of retained vertices follow from the same path projection/expansion.

**Root inside a discarded region.** Its two outside components each contain
at least one taxon. Since the original root reaches every taxon, it has paths
to both boundary attachments. Insert a new degree-two root at the midpoint
of the replacement bridge and direct its two incident edges outward. Keep
the original orientations in both outside components and shorten other
regions as above. Every outside vertex and taxon remains reachable, and no
directed cycle is created. A vertex below the new root lies on one of the
two sides and cannot lie on a root-to-taxon path confined to the other side.
Thus no lower vertex is stable ancestral to all taxa, so this is an LSA
rooted partner. Suppressing this degree-two root gives the required
semi-directed representative. The same midpoint argument handles a root
on an old bridge lying within the shortened chain.

These cases establish admission for the normalized actual graph. They do not
establish admission of every free codec record. The entire source definition
must still be enforced when enumerating unrelated candidate graphs.

## 4. Preservation of the requested profile

A two-port local displayed tree is the unique two-terminal path after
pruning/suppression. Its switching choices therefore supply no additional
taxon bipartition; all bridge partitions along the chain are identical.
The retained local switching families are unchanged. Their choices extend
independently and glue through the same whole taxon port components as before.

The global split-accounting theorem puts every nontrivial displayed split
either at an internal bridge of R or in a lifted split of a retained branching
blob. Those contributions are identical before and after normalization, in
both directions. Trivial taxon splits persist. Hence the complete displayed-
split unions agree. The elementary full-edge quartet witness identity then
shows that the complete existential quartet-support profiles agree as well.
No switching probabilities, multiplicities, branch lengths or finer source
topology are asserted to survive this normalization.

## 5. Linear vertex bound and finite complete enumeration

For one retained actual capped bloblet, let h_B be its number of hybrids and
M_B=m_B+h_B<=2m_B the number of occurrence tips. Its opened binary tree has
M_B-2 internal vertices. Closing each duplicate pair replaces two occurrence
leaves by one hybrid and its one port leaf, so its capped source graph has

    V_B = (M_B-2)+h_B+m_B = 2M_B-2 <= 4m_B-2

vertices. Its ordinary tree-vertex and hybrid counts follow from the actual
opening, without a reverse-realizability assumption.

Glue the q capped branching graphs along the q-1 internal edges of R. Each
gluing removes the two capped port leaves and joins their former neighbors.
The n remaining capped leaves become the n original taxon leaves. Therefore

    V_normalized = sum_B V_B - 2(q-1)
                 <= 4(n+2q-2)-2q-2q+2
                 = 4n+4q-6
                 <= 8n-14.

Inserting the rooted partner's root costs at most one additional vertex.

For fixed n, enumerate finite graphs up to the chosen vertex bound, with the
n fixed taxon labels, allowed source edge incidences, binary degrees and all
hybrid annotations. If parallel edges are allowed, binary degree bounds
still bound their number, so the candidate domain remains finite. Test the
**full** source contract: permissible rooting/orientation, DAG and reachability,
LSA condition, galledness and an outer-labeled planar embedding. These are
finite graph properties, decidable by exhaustive orientation/root/rotation
search if an efficient validator is unavailable. Reject invalid candidates.
For valid candidates enumerate all global switchings and compute/deduplicate
their exact quartet-support tables.

Soundness follows from the admission filter. Completeness follows from the
bounded representative of every original admitted source. Duplicate graphs
and multiple representatives of one profile affect cost, not correctness.
The enumerator may be extraordinarily expensive; the claim is effective
finite completeness for each n, not practical enumeration or a closed formula.

## 11. Process integrity

The codec's forward-only status was checked before using its state space.
The accepted enumeration route instead starts from actual sources, with
explicit handling of root location, positive external components, exact
profile preservation and the vertex count. The bound is a hand derivation,
not extrapolation from finite graph controls. Source structural facts are
pinned and remain conditional; no new execution was needed for this review.

## 12. Robustness and exact-minimum boundary

An exact minimax decision-tree calculation over this finite admitted profile
set is conceptually valid and computable for every fixed n once the complete
admission filter and profile enumerator are implemented. It yields an exact
integer/certificate for that n, potentially at prohibitive cost. It is not a
closed-form value of Q(n) for arbitrary n, and the source admission filter
cannot be replaced by a common-circle or linear-split-count test alone.

The target here is full split union plus any compatible circle. A task
returning only one compatible circle permits different terminal states and
has a different minimax problem. Biological sampling, incomplete observations
and continuous parameters also require different model/state spaces. Failure
of a pinned port/opening/composition premise would invalidate the linear-size
completeness guarantee and must be resolved before advertising the enumerator
as exact for the source class.
