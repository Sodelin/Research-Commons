# A cubic nonadaptive lower bound applies to finding any common order

Contributor: Codex adaptive-adversary subagent. Session: ADAPTIVE-ADVERSARY-20260930.
Date: 2026-09-30 UTC. Status: all-size hand-derived proof; independent graph controls
executed. No historical novelty, Lean verification, or adaptive-optimality claim.

This strengthens [the inherited lower-bound packet](../2026-09-30-root-exact-query/LOWER-BOUND.md):
its two-tree pendant witness forces different split outputs, but two different
binary trees can share an acceptable order. Three pendant resolutions remove
that ambiguity and lower-bound the order stage itself.

## 0. Decision and exact scope

For the full finite binary semi-directed LSA-rootable, outer-labeled planar,
galled network class, a deterministic always-correct **nonadaptive** algorithm
that returns just one compatible circular order needs Omega(n^3) complete
displayed-quartet-support queries. The result already holds on binary trees.
Combined with the inherited fixed-anchor consecutive-ones construction, the
nonadaptive query complexity of finding one common order is Theta(n^3).

This does not establish an adaptive cubic lower bound. The adaptive split-plus-
order master remains open unless a separate result closes it.

## 1. The theorem

Let n >= 4. A fixed family Q of four-taxon queries that always suffices to return
one common circular order must contain a queried quartet covering every
three-taxon subset A. Consequently

    |Q| >= ceil(binomial(n,3)/4) = Omega(n^3).

More sharply, Q must be a 3-covering by 4-subsets, so its cardinality is at least
the covering-design number C(n,4,3). No sufficiency claim is made for arbitrary
3-coverings.

The oracle returns the complete set of distinct displayed quartet topologies.
On the witness subclass each answer is a singleton. The requested order need
only be valid for the input actually supplied; the algorithm need not reconstruct
the entire order space or the tree.

## 2. Source-admitted witnesses for every triple

Fix A={a,b,c}. Keep the remainder of the tree unchanged. Attach a three-leaf
pendant subtree at one edge, and let T_ab, T_ac, T_bc have the respective pair
as its cherry. If only one outside taxon z exists (n=4), the pendant subtree
attaches directly to z. If n >= 5, attach to the root of any binary rooted tree
on the n-3 outside taxa. Every resulting unrooted graph has degree-one taxa and
degree-three internal vertices.

These are admitted binary networks: every tree is planar and outer-labeled
planar; galledness is vacuous. Subdivide any pendant edge to obtain a rooted
binary partner. Its two root branches contain respectively the pendant taxon
and all remaining taxa, so the root is the least stable ancestor of all taxa.
There are no reticulations, and hence no finite-level or blob-count exclusion.

For a queried quartet q not containing all of A, the answers in the three trees
agree. With two A taxa and two outsiders, the pendant attachment separates the
two pairs. With at most one A taxon, the pendant subtree collapses to its common
attachment terminal and its internal resolution disappears. A quartet
containing A and an outsider z has respectively

    T_ab: ab|cz;  T_ac: ac|bz;  T_bc: bc|az.

Thus the only queries that distinguish the three witnesses are those covering A.

## 3. Why no single returned circle works for all three witnesses

Every circular order of four distinct taxa allows precisely two resolved
quartet topologies. The third topology separates the two alternating pairs and
crosses that circle. Restrict any proposed output circle C on all n taxa to
{a,b,c,z}. Exactly one of ab|cz, ac|bz, bc|az crosses the restricted order.
The corresponding witness tree cannot be compatible with C: restricting a
compatible circle to an induced quartet preserves compatibility.

If Q does not cover A, the three witnesses have identical complete query
transcripts. A deterministic algorithm therefore returns the same C on all
three. Section 3 proves that C fails on at least one. This contradicts universal
correctness. Hence Q covers every triple. Each quartet contains four triples,
which proves the displayed bound. QED.

This is a full negative result for fixed measurement schedules on the admitted
class, rather than a claim that pairwise tree distinguishability alone forces
different acceptable order outputs.

## 4. A bounded-error randomized extension

Suppose a randomized nonadaptive algorithm issues at most q queries on each run
and succeeds with probability at least 1-delta on every input, with delta < 1/3.
For each A fix the same arbitrary outside-tree scaffold for its three witnesses.
Choose A uniformly among the binomial(n,3) triples and its pendant resolution
uniformly among the three possibilities. Fix the algorithm's random seed.

At most 4q triples are covered by its schedule. Conditional on an uncovered A,
all three witnesses give the same transcript and therefore the same output.
That output is compatible with at most two witnesses, so its conditional error
is at least 1/3. Averaging over triples, resolutions, and random seeds gives

    delta >= (1/3) * (1 - 4q/binomial(n,3)),

and therefore

    q >= (1 - 3delta) * binomial(n,3)/4.

For any fixed delta < 1/3 the order-only randomized nonadaptive lower bound is
still Omega(n^3). This argument uses no adaptive schedule assumption: permitting
answer-dependent queries would invalidate the counting step.

## 5. Adaptive order-only recovery still needs Omega(n log n)

There is also a sharper output-aware form of the inherited adaptive information
bound. It applies even when the algorithm may return any valid order and need
not identify the tree or split union.

There are (2n-5)!! labeled unrooted binary phylogenetic trees. Fix any circular
order C. Rooting at a fixed taxon and deleting it turns a tree compatible with
C into an ordered rooted binary tree on the remaining n-1 labels, whose order
is fixed. Conversely every such ordered rooted binary shape gives exactly one
labeled tree compatible with C. There are Catalan_(n-2) such shapes.

On this subclass each oracle answer has three possibilities, so a deterministic
query decision tree of depth q has at most 3^q terminal outputs. One output
circle can be valid for at most Catalan_(n-2) inputs. Universal correctness
therefore requires

    3^q * Catalan_(n-2) >= (2n-5)!!,

which simplifies to

    q >= ceil(log_3((n-1)! / 2^(n-2))) = Omega(n log n).

Unlike counting one distinct terminal per input tree, this argument explicitly
permits all trees sharing a compatible circle to receive the same output.

For an adaptive randomized algorithm with at most q queries per run and success
probability at least 1-delta on every input, fix its random seed. Among uniformly
distributed binary input trees it can succeed on at most 3^q Catalan_(n-2)
inputs. Averaging over its seed and using the pointwise success guarantee gives

    3^q * Catalan_(n-2) >= (1-delta) * (2n-5)!!.

Thus the same Omega(n log n) order-only bound holds for any fixed delta < 1.
These are lower bounds, not matching whole-source adaptive algorithms.

## 6. Executed controls

Run `python adaptive-adversary-controls.py` in this directory. The independent
implementation constructs ordinary graph trees, validates connectedness and
binary degrees, derives quartet resolutions from integer path distances, and
derives complete splits from graph edge cuts. It does not invoke inherited
network or quartet code.

Receipt [adaptive-adversary-controls.json](adaptive-adversary-controls.json):

| Check | Executed result |
|---|---:|
| Three-resolution witnesses, all triples at n=4,...,9 | 209 |
| Quartet-set comparisons across the three trees | 16,083 |
| Quartet sets giving three different answers | 1,008 |
| Exhaustive canonical circles at n=4,...,7, across witnesses | 13,932 |
| Circles compatible with all three witness trees | 0 |

All differences occurred exactly when the query contained the designated triple.
All other query answers agreed across all three trees. These finite controls
corroborate Sections 2-3; the all-size theorem follows from their arguments,
not from enumeration. Circles for n=8,9 were not enumerated.

`adaptive-adversary-order-count-controls.py` separately checks the Catalan
count in Section 5 against all graph-generated trees at n=4,...,8. Its receipt
is [adaptive-adversary-order-count-controls.json](adaptive-adversary-order-count-controls.json).
For n=4,...,7 it also checks every canonical circle against every binary tree,
verifying that each tree accepts exactly 2^(n-3) circles and each circle accepts
exactly Catalan_(n-2) trees. For n=8 only the fixed-circle Catalan count is checked.

## 11. Process integrity

The exact required output was checked before strengthening the inherited proof.
The difference between distinguishing trees and excluding a shared acceptable
circle is the substantive repair. The construction is source-admitted for every
n >= 4, and the executed graph controls use a representation independent of
the inherited source validator. There is no claim of a systematic prior search.

## 12. Robustness and master obligation

The theorem survives arbitrary allowed finite levels and blob counts because
their class contains the entire tree subclass. It uses singleton exact oracle
answers and therefore does not depend on inference about absent low-probability
events. Its vulnerable premise is specifically nonadaptivity: a later query
may target the pendant triple after learning the scaffold. Consequently the
proof supplies a sharp measurement-strategy boundary but does not close the
registered optimal adaptive split-plus-order question.
