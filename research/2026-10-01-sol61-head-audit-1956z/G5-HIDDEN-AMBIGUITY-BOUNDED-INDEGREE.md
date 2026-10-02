# HG review: bounded routing ambiguity and local exact-block support

Contributor: Sol6.1 independent HG audit, 2026-10-01, coordinated by dot.
Status: independently accepted all-size hand proof; dot/root and head reviewed the classical subsumption, source route argument and complete calendar theorem integration. Public research publication was subsequently authorized; historical novelty is unestablished. Original G5 chronology/source
attribution is retained. The abstract combinatorics is explicitly classical.

## 1. Outcome and exact classical subsumption

The proposed abstract lemma is correct, including singleton and full blocks.
It is an elementary corollary of classical bounded-domain/set-intersection
arguments, rather than a new Helly theorem. The indegree-k source position
bound is also correct: use components after deleting all actual original
bridges, not the binary degree-three biconnected-blob argument. Combined with
the accepted safe chronology, this yields the proposed sufficient observation
family M_(k+1) for the full rooted-cluster union and S on the extended source
class. Neither k+1 optimality for calendar laws nor historical novelty of the
source/observation integration is asserted.

Primary classical references inspected before further computation:

1. Yuanlin Zhang and Roland H. C. Yap, [Consistency and Set Intersection,
   AAAI/IAAI 2002, pp. 971–972](https://cdn.aaai.org/AAAI/2002/AAAI02-153.pdf),
   Lemma 2 (Small Set Intersection). For finite sets of cardinality at most m,
   nonempty intersection of every m+1 sets suffices for nonempty total
   intersection. The authors relate this cardinality mechanism to van Beek
   and Dechter (1997). A longer [IJCAI 2003 paper](https://www.ijcai.org/Proceedings/03/Papers/039.pdf)
   gives a set-intersection-to-consistency proof schema. The 2002 paper's
   explicit lemma is the cleanest citation for the small-set component.
2. Rina Dechter and Peter van Beek, [Local and Global Relational Consistency](https://ics.uci.edu/~dechter/publications/r41-local-global-rel-consistency.pdf),
   Theorem 31, PDF pp. 21–22: k-valued relationally k-consistent networks are
   globally consistent. Its proof selects one blocking relation per possible
   value of a k-element domain. That is exactly the certificate mechanism
   below after adding the original-label anchor.
3. Rina Dechter, [From local to global consistency, Artificial Intelligence
   55(1), 87–107 (1992)](https://doi.org/10.1016/0004-3702(92)90043-W),
   gives the broader domain-size/constraint-arity/local-consistency boundary.

Precise theorem-to-HG subsumption: fix c0 in C and A=S_c0. For each inside
label i set E_i=A intersect S_i. For each outside label o set
E_o={a in A: some b in S_o differs from a}. The full exact C block exists iff
the intersection of all these subsets of A is nonempty. If it is empty, one
failed unary constraint per element of A gives at most |A|<=k blocking labels.
Add c0, so the *actual restricted exact-block event* has the same anchor
domain A. This yields at most k+1 original labels. This direct bounded-domain
corollary fully subsumes the abstract HG; a generic CSP theorem is not needed
as an assumption of the biological result.

## 2. Exact abstract statement and independent proof

Let B be finite, let C be a nonempty subset, and let each S_i be a nonempty
set of possible positions. Assume feasible assignments are exactly the
Cartesian product of the S_i. Suppose |S_i|<=k for inside labels i in C;
in fact it is enough that **one chosen anchor** c0 in C has |S_c0|<=k.
Outside position sets need not have the same bound.

Write J_C(U) for existence of an assignment on U whose occupancy partition
contains C intersect U as one **exact block**, only when C intersect U is
nonempty. Then

    C is an exact block in some feasible assignment on B
      iff every J_C(U) holds for U subset B with |U|<=k+1.

Necessity is ordinary restriction. For sufficiency, prove the contrapositive.
Let A=S_c0. An exact C block at position a exists precisely when

    a belongs to every inside S_i, and every outside S_o has a value !=a.

If the full block fails, for every a in A choose one obstruction:

- an inside label i with a not in S_i; or
- an outside label o for which S_o={a}.

The second alternative follows because S_o is nonempty and no position in it
differs from a. Let U contain c0 and these at most |A| selected labels. Then
|U|<=1+|A|<=k+1 and C intersect U is nonempty. In any putative restricted
exact-block assignment its block position lies in A, by c0; the selected
obstructor for that value forbids it. Thus J_C(U) fails.

This proof allows repeated obstructors and arbitrary universe size. It also
handles k=1, B=C, and singleton C directly. It is about support feasibility;
conditioning on no merger may induce dependent *weights*.

The parent's more refined I=intersection_(i in C)S_i proof is valid too.
Choose c0, A=S_c0, then one inside label excluding each a in A minus I. Their
union D with c0 has intersection exactly I and |D|<=1+k-|I|. If I is empty,
D is already an obstruction. Otherwise failure forces every a in I by one
outside singleton {a}; their union O has |O|<=|I|, so |D union O|<=k+1.

Sharpness has only the following abstract meaning: take C={c}, S_c={1,...,k},
and outside labels o_a with S_o_a={a}. The full exact C block fails, but
every restriction including c on at most k labels succeeds. Hence the k+1
**local exact-block certificate threshold** cannot be lowered in arbitrary
Cartesian position families. This is not a pair of equal genealogy laws and
does not establish an optimal calendar observation sample size.

## 3. Source extension: original-ID bridge-component proof

Retain the accepted finite rooted temporal DAG multigraph source, but permit
hybrid indegree d with 2<=d<=k, unique outdegree one, and its actual child arc
an undirected bridge. Ordinary tree vertices have indegree one/outdegree two,
the root has indegree zero/outdegree two, and tips have indegree one/outdegree
zero. Parallel arcs are separate original edge occurrences. Strict ages,
positive finite population rates, positive durations, and positive categorical
parent-routing weights are retained. The root-LSA assumption may be retained
from the source contract, though the route-count argument does not use it.

**Claim.** At every age t, every original tip has at most k feasible active
original population edge occurrences (with the ancestral tail counted as one).

1. All root-reachable vertices make the underlying undirected multigraph
   connected. Delete every actual bridge and form its connected components.
   Contracting each component yields a tree: a quotient cycle would put one
   of its alleged bridge occurrences on an undirected cycle. This uses
   bridge occurrences, so parallel arcs are never silently merged.
2. Every bridge is oriented away from the root component. Indeed a directed
   root-to-source path avoids its target-to-source return through that edge
   by acyclicity. Since it is a bridge, its source is on the root side. Every
   root-to-tip route consequently follows the same quotient-tree path.
3. A nonroot component K has exactly one rootward entry bridge. For every
   vertex of K, a directed root route enters by that bridge and reaches the
   vertex without leaving K and returning, which the quotient tree forbids.
   Thus the entry vertex reaches every vertex of K by an internal directed
   path. The root is the analogous entry of its own component.
4. Every hybrid's outgoing child arc is absent from K. Hence a hybrid has
   no outgoing internal arc and cannot be an internal vertex of an internal
   directed route. In a nontrivial component its entry cannot be a hybrid,
   since it would then reach no other vertex internally. With d>=2 a hybrid
   also cannot form an entry singleton component: all incoming boundary
   bridges would need to be rootward, but there is exactly one such bridge.
   Therefore every hybrid's incoming parent arcs lie in its component.
5. Fix the tip's unique quotient-tree path and one component on it. Its
   descendant exit bridge and exit-tail vertex w are fixed; in the last
   component use the fixed terminal tip as w. If w is ordinary, every
   rootward predecessor on an internal route has a unique parent, so there
   is at most one internal route from w to the component entry. If w is a
   hybrid, choose one of its d<=k distinct incoming original arc occurrences,
   then follow only ordinary unique-parent vertices to the entry. An
   additional hybrid cannot occur internally because its outgoing arc would
   have to be internal. Thus there are at most d<=k internal routes.
6. The component entry and fixed exit-tail ages are independent of all
   switching choices. Every tip route occupies this same component on the
   half-open interval between those fixed ages. On any intervening bridge
   interval it occupies the one fixed bridge. Strict ages give one active
   original edge per internal route at t. At the older-side endpoints
   instantaneous movements place all routes into the next fixed component
   or bridge, with the same bound. Above the root all occupy one ancestral
   population. Earlier choices have already pooled at fixed component
   entries and cannot multiply the present position count.

The degree-three argument about vertex-disjoint biconnected blobs is therefore
unnecessary. Degree four or more at hybrids creates no counterexample: in the
bridge-deleted directed component every hybrid is a sink. The proof even
shows the deterministic route bound needs ordinary indegree one, not binary
ordinary outdegree, but no extra source expansion is claimed here.

## 4. Sufficient (k+1)-tip calendar-law family for the full target

Let r=k+1 and |X|>=r. Let M_r be all exact rooted original-label r-tip
calendar genealogy laws in common units from one shared source/parameter
assignment, with hidden population/routing IDs. Smaller laws are their
ordinary restrictions. If |X|<r, the relevant input is the full X law and its
ordinary marginals; an empty r-tip family would supply no information.

Every observation panel is promised to come from ONE admitted original source and ONE shared demographic/inheritance assignment. The theorem assembles target information on that promised class; it does not recognize arbitrary independently fitted panel laws as globally source-realizable.

The accepted selected-law intertwining and finite frozen-germ argument extend
from binary to categorical parental pulses: marginalizing discarded choices
sums their probabilities to one, and a common site still uses one shared
original categorical choice. Finite state spaces and positive pair rates are
unchanged. Thus all supports H_U(t), |U|<=r, are identified from the exact
calendar laws by the accepted argument. Original edges are not contracted or
given zero duration in the biological process.

At each chronology stage, sure full representative blocks are recovered using
only pair supports. Its first attained sure nonsingleton time tau exists by
finite source support steps and the ancestral root state. The actual child
bridge protects every hybrid descendant set for its positive calendar
interval, independent of its indegree. Therefore any hybrid reached by tau
has at most one current representative below it, as in the accepted induction.
Every encountered original site is consequently used by at most one current
representative. Its categorical choice may be combined independently with
all other representatives' choices, and all combinations have positive
no-merger survival. This proves Cartesian *support* and equality of common
and live-ancestor independent routing supports on each safe stage.

Section 3 bounds each current representative's possible positions by k.
Section 2 therefore recovers every possible full representative exact block
from H_U(t) on |U|<=k+1. Lift blocks to their original-tip groups, merge sure
blocks at tau, retain original-tip representatives, and recompute ordinary
selected marginals. Common-path persistence and the safe-past invariant are
the same as the accepted chronology. There are at most |X|-1 deletions.

Consequently the generalized safe chronology recovers exactly the union of
rooted clusters over complete original categorical switchings. Each retained
parent occurrence produces a rooted tree after pruning/suppressing, and each
nontrivial cluster is present on a positive-duration original edge path.
Reading splits {C,X minus C} with both sides of size at least two gives the
full displayed unrooted S by the retained binary-root correspondence.

**Proposed HG theorem.** On the source class of Section 3, equality of M_(k+1)
across any two all-positive source/parameter assignments, possibly with
different common-versus-independent routing mechanisms, implies equality of
the full displayed rooted-cluster union and full displayed unrooted S.

This is a sufficient exact-law theorem, not finite-DNA estimation, a supplied
hidden-population oracle, polynomial-time reconstruction, or a matched-law
lower bound. The source lemma/abstract proof are independently checked here;
the complete calendar theorem remains a hand extension of the accepted G5
stochastic and chronological components, not a full Lean certificate.

## 5. Nearest source-identification prior boundary

Allman, Baños, Mitchell and Rhodes, [The tree of blobs of a species network:
identifiability under the coalescent](https://par.nsf.gov/servlets/purl/10420145),
J. Math. Biol. 86:10 (2023), Theorem 4, identifies the **reduced unrooted tree
of blobs** from gene quartet *topologies* at generic numerical parameters on
rooted binary networks. Its bridge-contracted tree is the classical object
used in Section 3. It does not by its stated conclusion identify the full
displayed cluster/split union inside blobs or the all-positive bounded-indegree
calendar target here. This is a direct scope comparison, not proof of priority.

Allman, Ané, Baños and Rhodes, [Beyond level-1: Identifiability of a class of
galled tree-child networks](https://link.springer.com/article/10.1007/s11538-025-01545-8)
(2025), Lemma 3.2 explicitly restricts every C_j hybrid to indegree two.
Theorem 5.7 gives generic semidirected topology and internal tree-edge length
identification from quartet CFs on binary C_4 with two samples per taxon, or
C_5 with one sample. Thus k>2 violates its explicit source condition. Even
for k=2 the present class permits ordinary nodes with two hybrid children and
parallel/small cycles, unlike these classes. Its generic CF conclusion does
not subsume the proposed all-positive categorical indegree-k rooted-calendar
statement. Its Section 2.3 also makes explicit that a blob is a 2-edge-connected
component, precisely the classical bridge-contracted object used here. This
is a bounded primary-theorem comparison, not a historical originality claim.

## 6. Exact local verification receipts and remaining gap

The primary classical subsumption and focused source theorem comparison were
completed and reviewed by dot/root before resuming new computation, in accord
with the user's latest direction. Initial invocations had no successful proof:
default Python lacked NetworkX, and a broad Lean tactic import exceeded its
2 GiB cap. The existing NetworkX path and focused Lean imports solved these
environment issues without installing anything or changing the theorem scope.

`g7/bounded_indegree_support_checks.py --source-only` subsequently PASSED
under Python 3.12.14 and NetworkX 3.5:

- 16 actual original-ID sources with maximum hybrid indegrees k=2,3,4,5;
  eight retain a nonplanar K3,3-minor backbone, eight include distinct parallel
  parent arcs, and half in each group have a protected cherry below a hybrid
- every source satisfies the exact degree/reachability/LSA/child-bridge and
  positive-original-calendar conditions; the checker also verifies the bridge
  quotient is an arborescence, each nonroot component has exactly one rootward
  entry, all hybrid parents remain in its component, and each child exits
- 1,504 original-tip/time position checks, using event ages and interval
  midpoints; every fixture actually attains k active original edge positions
- 368 safe-stage Cartesian **assignment** support checks, stronger than only
  equality of erased population partitions on these fixtures
- 32 complete original-X chronological recoveries across common categorical
  and live-ancestor independent routing, with a hard maximum of k+1 labels in
  the observed-support interface

The decoder sees erased partition support only; actual original edges and
full assignments are used by independent fixture truth and premise checks.
For |X|<k+1 these controls use its full-X law-sized support, as required by
Section 4. Rates may be chosen one and weights 1/d, which make every enumerated
finite route have positive probability and positive finite no-merger survival.
The source controls do not numerically reconstruct a calendar law germ.

`g7/G5BoundedExactBlock.lean` also compiled with official Lean 4.33.1 and
pinned mathlib, under focused imports and the 2 GiB cap. It proves:

1. `bounded_unary_obstruction`: an empty feasible candidate set on a finite
   anchor domain A has at most |A| blocking unary constraints
2. `exact_block_small_obstruction`: add one original inside anchor to obtain a
   failed restricted exact-block event on at most k+1 original labels
3. `exact_block_iff_local`: the full iff using all at-most-k+1 restrictions

All three axiom reports contain exactly propext, Classical.choice, Quot.sound,
and no sorryAx. The source-to-position bound and stochastic calendar theorem
are **not** encoded as hypotheses or conclusions of that abstract file. Its
verified predicates express feasibility under Cartesian positions, not a
proof of biological support observability. This is formal verification of a
classical corollary, with classical attribution kept explicit.

Receipts: `g7/G5BoundedExactBlock-receipt.json`,
`g7/G5BoundedExactBlock.log`, `g7/bounded-indegree-source-results.json`, and
`g7/bounded-indegree-source-check.log`. Reproduce source controls with
`PYTHONPATH=/workspace/shared/g6-review-2005z/deps python
sol61-head-audit/g7/bounded_indegree_support_checks.py --source-only`.

Next useful step after head review: formalize the original-edge
bridge-component route bound and connect it to the retained chronological
invariant. The empirical optimum remains a separate question.
