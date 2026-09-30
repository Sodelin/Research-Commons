# Second independent review: bounded actual-source normalization

Reviewer: Codex `adaptive_construction`, EXACT-NORMALIZATION-REVIEW-20260930.
Date: 2026-09-30 UTC. Reviewed [EXACT-MINIMUM-THEOREM.md](EXACT-MINIMUM-THEOREM.md)
and [EXACT-PROFILE-REVIEW.md](EXACT-PROFILE-REVIEW.md).

**Verdict: ACCEPTED conditional on the explicitly pinned source/port/switching
facts.** No material gap was found in replacing two-port chains, preserving an
LSA-rooted admitted representative, or the 8n-14 unrooted / 8n-13 rooted vertex
bound. The finite actual-graph census therefore characterizes the exact
admitted oracle-profile class, without assuming a converse for free occurrence
codes. The Bellman specification then uniformly computes the exact deterministic
finite-size query minimum. It is an unimplemented, potentially prohibitive
computation and not a closed expression or a list of computed q(n) values.

## 1. The normalization premise actually used

The reviewed construction starts with an ACTUAL admitted source. It retains
its branching blob subgraphs and annotations; it does not infer admission by
folding an arbitrary adjacent-copy record. The inherited facts used are:

- every cut has taxon-bearing components on both sides;
- each actual capped branching blob has the bounded adjacent-copy opening,
  with at most two occurrences per port and hybrid outgoing port bridges;
- local switchings extend globally, and the full split union consists of
  bridges and lifted local splits, with a unique two-terminal local tree for
  each two-port blob.

These premises remain conditional on their pinned source audits. This review
checks the NEW preservation and bounded-enumeration argument; it does not
replace those upstream proofs with a numerical sample or a purported codec
converse.

## 2. Degrees, annotations, and directed paths

The tree of blob attachments identifies every removed region by exactly two
external bridge incidences. Its normalized replacement has the same retained
endpoints and replaces one incidence at each by one incidence. Thus retained
binary degrees and tree/hybrid types do not change. Retained hybrid incoming
edges remain in their original blob; retained outward child incidences keep
their direction. No new reticulation is introduced.

If the root is outside a removed region, one external bridge enters from the
root side and the other exits toward the other taxon-bearing component. Root
reachability guarantees a directed entry-to-exit path. A replacement bridge
inherits that direction. Since the underlying reduced attachment graph is a
tree, no alternate path creates an undirected or directed cycle across this
bridge. Retained directed cycles cannot appear because their original blob
orientations are unchanged. The argument also excludes a newly introduced
parallel edge when simplicity is part of the source convention.

A projected root-to-retained-vertex path visits the same retained vertices as
its original path, with only removed-region traversals shortened. Conversely,
any projected directed path can be expanded through one original directed
entry-to-exit path at every traversed region. A cut bridge cannot be traversed
and later reentered through an alternate route, because the attachment graph
is a tree. These are the required BOTH directions; merely preserving one
example path would not preserve stable ancestors.

## 3. LSA root audit

When the original root is retained, for each retained vertex v and taxon x,
existence of a root-to-x path avoiding v is invariant under the path
projection/expansion. Therefore all retained stable-ancestor predicates remain
unchanged. No newly introduced non-root vertex exists on a replacement bridge,
so a lower common stable ancestor cannot appear after normalization. The old
LSA root remains valid.

When the original root lies inside a removed chain, its two external bridges
must point outward: the root lies in the chain and reaches both external
components, each of which contains a taxon. Rooting midway on the new bridge
creates two outgoing branches into those components. Both keep their original
outward orientations and remain reachable. Every vertex below the new root
lies in one component and is avoided by root-to-taxon paths in the other.
Thus no proper descendant can dominate all taxa, and the new root is their
LSA. This also covers a root on an old bridge inside the shortened chain.

This case does not assert that the old root's internal reticulation or
probability structure is preserved. It establishes the required existence of
another LSA-rooted admitted partner for the same exact quartet/split output.

## 4. Galledness and outer-labeled embedding

The operation removes entire two-port regions, retains every surviving blob's
cycles and hybrid incidences, and introduces only bridges. Any source galled
condition expressed on retained cycles therefore persists; no new cycle can
contain previously unrelated hybrids.

In the given source embedding, keep a simple connecting path through each
removed two-terminal region, delete its other edges, and smooth its internal
vertices. The retained path and its smoothing lie within the original embedded
region. Deleting edges merges faces, and smoothing preserves face incidence;
taxon leaves and their surviving pendant incidences remain on the outer face.
Subdivision by the replacement root preserves the same embedding. This is a
direct actual-source embedding proof, not a reverse-realizability claim about
free structural codes.

## 5. Exact output preservation and independent vertex count

The reduced tree has the same whole taxon components at every retained port.
Retained local switching families and their split lifts are unchanged. A
removed two-port blob has only the same two-terminal path after switching,
pruning and suppression; its bridge bipartitions are duplicate copies of the
one normalized cut. The inherited local-to-global split identity consequently
preserves the full split union in both directions. A quartet topology belongs
to a binary-tree family's support exactly when some full split restricts to
its 2+2 partition. Equal split unions therefore give equal complete quartet
profiles and equal compatible-circle spaces.

An independent degree-count derivation corroborates the opening count. In a
capped bloblet with m ports and h hybrids, each hybrid's distinct outgoing
bridge is a port, so h<=m. The connected binary graph has h independent cycles;
its ordinary-plus-hybrid internal-vertex count is m+2h-2<=3m-2. If the reduced
attachment tree has q branching nodes, then q<=n-2 and sum m=n+2q-2. Adding the
n taxon leaves gives

    V <= n + sum(3m-2)
      = 4n+4q-6
      <= 8n-14.

One rooting subdivision adds at most one vertex. This agrees with the
reviewed cap-opening/gluing count. The conservative 20n census cap is safe.

## 6. Consequence for exact minimax computation

Enumerating ALL candidate rooted graphs below the safe bound and filtering
by the COMPLETE source contract is sound by construction. It is complete
because every admitted source profile has a normalized representative below
that bound. Arbitrary common-circle families or short codec records cannot
replace that admission filter.

The enumerated profile set P_n is finite and exact. Equal profiles have equal
full split targets by the exact common-circle recovery theorem. Distinct
profiles cannot have the same full split union, since a split union determines
all of its quartet restrictions. Therefore a both-output decision-tree leaf
must identify one profile. The stated Bellman recurrence on nonempty profile
subsets gives the exact minimum by the standard first-query induction.

The census, all-size optimizer and certificate checker are NOT implemented
by this review. Uniform computability and an optimal-policy specification are
accepted; efficient computation, a closed formula in n, and uncomputed finite
values are not claimed. Biological probabilities and continuous observation
laws are outside this discrete exact-oracle theorem.

## 11. Process integrity

The argument was challenged at the root-in-chain case, directed path
expansion, retained dominators, endpoint hybrid incidences, source embedding,
output equality and the actual graph-count bound. The second review agrees
with the separately authored boundary review. Both remain hand reviews
conditional on identified source premises, not machine certificates or
independent replications of every source audit.

## 12. Robustness

The finite stopping bound fails if a supposed source port can have a taxonless
external component, if the stated capped opening is unavailable, or if
independent local split lifting is false. Those are upstream named premises,
not hidden assumptions introduced by enumeration. With them, no normalization
counterexample was found. The bounded representative removes the previous
semidecidability concern: exact admitted profile membership becomes decidable
for every finite n, despite unbounded original chain lengths.
