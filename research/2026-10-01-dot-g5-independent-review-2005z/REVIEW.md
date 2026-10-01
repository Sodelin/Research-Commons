# Independent acceptance of the G5 exact-calendar Q/S theorem

- Review ID: **DOT-G5-REVIEW-20261001-2005Z**
- Reviewer/publisher: **dot**, independent of the submitted theorem's author
- Original theorem and construction: **GPT-6 Astra Pro**, G5-QUARTET-MARGINALS-20260930 and its preceding G5-CALENDAR-EXACT-20260930 work
- Date: 2026-10-01 UTC
- Evidence category: independent hand-proof review, with separately written exact finite controls
- Verdict: **ACCEPTED for the full stated positive exact-calendar theorem**
- This is a mathematical review verdict, not a Lean certificate, journal referee decision, general G1–G7/BIO1 completion, or acceptance of every implementation claim

## 1. Exact statement and what this verdict closes

Let X be a finite labeled set, |X| >= 4. The source is an admitted finite binary rooted temporal LSA partner of an outer-labeled planar galled semi-directed multigraph. Parallel edges are allowed. Every hybrid has one child edge, and that edge is an undirected bridge. Tips are contemporaneous. Adjacent vertices have strictly different ages in the ancestral direction. Finite edges have strictly positive finite durations and strictly positive finite constant pair-coalescence rates. The ancestral population has a strictly positive constant pair rate. Each hybrid inheritance weight is in (0,1), with distinct hybrid sites independent. One gene is sampled per original taxon.

Either all lineages at a hybrid use its one common parental coin, or current lineages use independent parental coins. The compared sources may use different mechanisms. No finite bound is supplied on source size, reticulation level, blobs, demographic ages, rates, local spectral atoms, or hidden population assignments. Equal rates and coincident ages of unrelated vertices are included.

The observation M4(R) contains, for every four-element A subset X, the exact rooted labeled genealogy law restricted to A, with all retained merger times in the same calendar units. These laws originate from one common source/parameter assignment. Q(R) is the complete union of distinct resolved displayed quartets. S(R) is the union of nontrivial splits of displayed unrooted trees.

**Accepted theorem.** For any two sources R and R' in this entire class, including comparison across the two inheritance mechanisms,

    M4(R) = M4(R')  implies  Q(R) = Q(R') and S(R) = S(R').

The stronger available full n-tip calendar law therefore also has a singleton Q/S target fiber. This discharges the exact-calendar target-constancy question stated in the G5 assignment. The quartet extension does not claim to reconstruct the full n-tip joint law or its entire rooted-cluster union.

No supplied calendar cover is an assumption of this identification theorem. Such a cover is an additional input contract of the published finite implementation. No empirical estimation of an exact germ, finite-data stopping guarantee, arbitrary-law source recognizer, bounded four-taxon demographic representative, or hidden-network identification is inserted into the verdict.

## 2. Reviewed artifacts and prior boundary

The principal submitted proof is [THEOREM.md at packet commit 92ad7053fd3ff5f656f77ab40cfeb38d7711687b](https://github.com/Sodelin/Research-Commons/blob/92ad7053fd3ff5f656f77ab40cfeb38d7711687b/research/2026-09-30-g5-quartet-marginals/THEOREM.md), blob `3f170e492e237924059d0f685ba1f81529d3c01d`. Its [verified-publication communication](../../communications/2026-09-30-g5-quartet-publication-verified.md) explicitly requested the present source-critical gate. The earlier full-sample proof [G5-THEOREM.md](../2026-09-30-calendar-metric-g-continuation/G5-THEOREM.md), read at blob `05c7f364019a994ee196b40c81d03efba11fee1c`, was checked where the quartet manuscript compresses the chronology.

Also read: AGENTS.md, START-HERE.md, the full-master completion standard, the exact G5 assignment receipt, the current G4 one-bigon and G6 effective-certification boundaries, the structural quartet/split theorem and order-free interface, the canonical Samuel all-level proof at `e2502c82ab9a77c00543932f775a71e5374221f7`, and the G5 decoder's source interface. None of G3, G4, G6, G7, the NANUQ score-cone calculation, or a demographic normal-form theorem is needed for the proof below.

The source-to-common-circle premise is already a published result: Holtgrefe et al., [Proposition 2.9 and Definitions 2.2–2.3](https://link.springer.com/article/10.1007/s11538-025-01549-4), DOI 10.1007/s11538-025-01549-4. It applies to outer-labeled planar semi-directed networks without a level bound; the definitions permit parallel edges. Its hypothesis and displayed-tree semantics were checked directly in the primary article. This is not a new circular-order theorem. Section 8 supplies the elementary argument needed here, separately from the stronger unpublished score classifications.

The theorem's original chronology and independent-inheritance recovery retain the submitted author's attribution. This review contributes an independent verification, a shorter matrix-exponential proof of the local bridge, an explicit dependency reduction, and bounded controls written without importing the author's executable code. It makes no historical-priority claim for the full theorem or its ingredients.

## 3. Selected-tip projectivity: accepted

Fix nonempty B subset X. A full instantaneous coalescent state lists live ancestral label blocks and their population edges. Project each label block to its intersection with B and discard empty intersections. Each retained ancestral block corresponds to exactly one full live lineage.

For two distinct retained blocks in the same population there is exactly one pair of full lineages whose merger joins that pair, at the same population pair rate. Full mergers involving an empty projected block do not change the projected state. Summing the full generator over each projection fiber therefore gives the selected-process generator for every full state over that fiber. Invisible jumps cancel with their diagonal contributions. This is strong lumpability, not a claim merely about mean lineage counts.

At an independent hybrid event, choices of discarded-only lineages integrate to one; retained lineages retain independent parental choices. A common coin gives the same projected pulse in the common model. Deterministic tree/root movement also commutes with projection. Composing the finite chronological generators/pulses and the ancestral tail proves equality of entire selected path laws, hence of topology and retained merger times.

The selected process remains on the original graph. Its root need not be the LSA of B; unused branches and serial hidden structure are not deleted. Every smaller marginal used below is obtained by ordinary restriction of one observed four-tip law. This is neither resampling an ancestral lineage nor an intervention.

## 4. Frozen population recovery: accepted by an independent proof

For fixed finite t and selected B, let E_B(t) mean that no selected merger has occurred by t. Every feasible finite no-merger route has strictly positive probability: its weight is a finite product of positive inheritance factors and exponential survival factors with finite integrated hazard. Hence P(E_B(t)) > 0, and conditioning on E_B(t) does not remove any feasible route from support.

For every partition sigma of B, the exact observed genealogy law determines

    F_(t,sigma)(h) = P(gene partition at t+h is sigma | E_B(t)), h >= 0.

At a demographic age, use the state immediately after all instantaneous movements at that age, on its older side. Equal-age events are unrelated because every edge has positive duration. The finite source has a nonempty interval to the next demographic event. Conditional on E_B(t), it has only finitely many possible population assignments z of the |B| distinct selected ancestors at t.

For assignment z, freeze those occupied populations forever. Let K_z be its finite Kingman generator on labeled partitions refining that population assignment, embedded if desired into the common finite partition-coordinate space. Starting from singleton gene blocks, the vector

    f_t(h) = sum_z w_z e_singletons^T exp(h K_z)

is entire in h. On some interval 0 <= h < epsilon it equals the vector of observable F_(t,sigma)(h). If a second admitted representation gives the same observable germ, both entire vectors agree on a real interval and therefore everywhere by analytic uniqueness. The two representations need not have the same hidden assignments, dimensions, rates, or epsilon.

Each nonempty frozen population has a positive rate and finitely many lineages, so it reaches one lineage almost surely. Distinct frozen populations never merge. Therefore

    lim_(h -> infinity) f_t(h)

is exactly the distribution of B partitioned by its occupied populations at t, conditional on E_B(t). It is a functional of the observable germ alone.

This proof does not require distinct eigenvalues, generic parameters, a known spectral count, or diagonalizing the generator. The submitted finite-exponential argument is consistent with it, but stronger spectral assertions are unnecessary for mathematical identification. In particular, the limit is not the actual network's long-time limit, which instead puts everything in the ancestral population.

Write H_B(t) for the resulting support of occupied-population partitions. Positivity identifies H_B(t) with the support of feasible no-merger routes. It is right-continuous and constant on each of finitely many demographic calendar cells, even though its positive weights vary within a cell. These properties follow from the source promise; neither hidden cell endpoints nor their count are supplied to the identification map.

## 5. The child-bridge barrier: accepted without a reduced-graph premise

Let h have child c and let D_B(h) be the selected tips below h. Delete the undirected bridge h->c. Its c-component is separated from the root. Every root-to-vertex directed path into that component crosses h->c; all vertices in it are therefore descendants of c and have age at most age(c). Conversely, since h has just one child edge, its descendants lie in this component.

On the whole nonempty interval

    age(c) <= t < age(h),

all selected descendants have reached the population edge h->c, and no selected tip outside the component can occupy it. Thus D_B(h), if nonempty, is one exact whole population block in every supported partition. If it has at least two members, this is a sure nonsingleton block strictly before reaching h.

This statement survives every selected-tip restriction because the graph and its positive child edge remain unchanged. It does not depend on whether lineages will later use common or independent inheritance. Merely being pairwise possibly colocated, or always being contained in some larger random block, is not the criterion.

## 6. Chronological lifting: accepted, with the invariant made explicit

Fix one originally observed quartet A; the same argument works for any finite selected sample. Groups G_b partition A, indexed by their current original-tip representatives b in B. A group is never a newly sampled ancestor. Initially B=A, G_b={b}, and s=0.

At a stage, apply Section 4 to the ordinary selected marginal on B. Let tau >= s be the first time H_B(t) contains a sure nonsingleton exact block. Such a time exists: by the finite source root age every representative is in the one ancestral population. The first time is attained because supports are right-continuous finite-step functions. Record all supported population blocks for s <= t <= tau, lifting a representative block U to the original set union_(b in U) G_b. Then merge each nonsingleton sure exact block at tau, retain its deterministically chosen original-tip representative, and repeat with the new ordinary marginal. Same-time repetitions are harmless and strictly decrease the number of representatives.

Here is the complete induction, including the part most vulnerable to an independent-inheritance mistake.

1. **Common-path persistence.** For every complete common switching omega, every original member of G_b follows the same population path as b from s onward. This holds initially. Once all members are together in one switching, common choices at every later hybrid prevent separation. The populations may differ between switchings.
2. **Safe past.** No hybrid of age at most s has two descendants in the current B. This holds initially. At each subsequent grouping representatives are only deleted, so it cannot be broken by the update.
3. **Complete recorded past.** Every possible original-A common-switching population block before the new stage has been recorded; only such blocks have been recorded.

To justify the next interval, suppose a hybrid h with age(h) in (s,tau] had at least two descendants in B. Its child bridge would exhibit the sure block D_B(h) at some time

    max(s,age(c)) < u < age(h) <= tau,

contradicting the choice of tau. Hybrids of age at most s are excluded by the safe-past invariant. Thus no hybrid reached by tau has two current representatives among its descendants.

On every no-merger selected route up to tau, each encountered hybrid is therefore used by at most one selected ancestor. Independent route choices specify at most one parental choice per encountered hybrid and extend to a full common switching. Conversely every common switching provides possible independent selected routes. All those routes have positive weight. The independent and common supports H_B(t) consequently coincide on [s,tau]. Their probabilities need not coincide.

For a fixed common switching omega, common-path persistence says that its original-A partition at time t is exactly the lift of its B partition. Every supported B partition extends to at least one full switching, and every full switching is included. Taking unions proves both directions: every recorded lifted block is genuine, and every common-switching original-A block on this interval is recorded.

At tau, a sure exact representative block is one whole population block under every common switching. Its lift is therefore one whole original-A block under every switching. Retaining one original member establishes common-path persistence for the new group. Deletion preserves the safe-past condition, which has just been established through tau, and the recorded-past invariant also persists.

At least one representative disappears at each grouping, so there are at most |A|-1 deletion steps. Source finiteness supplies only finitely many relevant calendar cells at each step; it is not a uniform bound across sources. When one representative remains, all original A members follow one path in each common switching forever, so no proper missing cluster can occur later.

Crucially, replacing B by fewer representatives changes the posterior distribution conditional on their no-merger event. The induction never equates those posteriors. It uses the new genuine marginal and positivity of all feasible routes. This avoids the invalid step of carrying old independent-route weights across representative deletion.

## 7. The recorded target and quartet assembly: accepted

Fix a common switching omega of the original source, regardless of which biological mechanism generated the observations. Its no-merger lineages follow the unique displayed-tree paths. The nonempty population blocks across time are exactly the rooted clusters of that displayed tree restricted to A, with singletons and A included by convention.

For one direction, an occupied source edge separates precisely the selected descendants passing through it. Pruning unused edges and suppressing unary vertices preserves that descendant cluster. For the converse, every proper edge of the displayed restricted tree comes from a nonempty path of original source edges. Such a path has positive duration, so its cluster occurs on a nonempty calendar interval. A is obtained in the ancestral tail. No quartet-specific LSA or small demographic graph is required.

Thus Section 6 recovers precisely

    { C intersect A : C is a rooted cluster in a full displayed tree,
                      C intersect A is nonempty }.

An unrooted resolved quartet is present exactly when one of these clusters yields a 2|2 split after forgetting the root. Equivalently its internal edge lifts to an edge path of a full displayed tree. Hence the construction gives the exact Q(R)(A). Its inputs are the A law and smaller ordinary marginals of that same law, so equal M4 observations produce the same complete Q table, within and across inheritance mechanisms.

Gene-tree support itself was never equated with displayed-tree support. The common switching is a combinatorial description of the recovered target, not an assertion that the independent biological process secretly uses common inheritance.

## 8. Common circle and Q-to-S bridge: accepted

Only this last step uses the planar source hypothesis. In a fixed outer-labeled planar embedding, deleting one hybrid parent edge per hybrid, pruning unused parts, and suppressing degree-two vertices gives each displayed unrooted tree in the same cyclic leaf order. An elementary picture can be made precise by extending the leaf tips through disjoint short corridors in the unbounded face to a surrounding Jordan curve. Distinct components of a tree cut edge cannot have alternating boundary leaves: their connecting paths would have to cross. Consequently every displayed split has two interval sides in one shared circle. Parallel edges, source root subdivision, and later suppression do not change the argument.

This is the source-matched content of the published Proposition 2.9 cited above. It does not require a score metric, six-label enumeration, source-size reduction, or the stronger source-normal-form results.

The circle need not be supplied. Search the finitely many circles on X and retain any order in which no quartet in the recovered Q has alternating pair sides. One exists. Moreover every displayed full tree respects every such retained order: a noninterval edge split would give four alternating labels, two from each side, whose displayed quartet is crossing in that order, a contradiction.

Fix such an order. For two nonadjacent boundary gaps (a,b) and (c,d), let S_0 split the interval b,...,c from d,...,a. Its four endpoints are distinct. Then

    S_0 is in S(R)  iff  bc|ad is in Q(R).

The forward implication restricts an edge displaying S_0. Conversely, bc|ad in Q is witnessed by an edge of some full displayed tree. That edge split is circular in the chosen order and separates both a from b and c from d. A nontrivial circular split has exactly two boundary gaps; they must be the adjacent gaps (a,b) and (c,d). The edge therefore displays precisely S_0, not an unspecified split agreeing only on four labels.

Checking all n(n-3)/2 nontrivial gap pairs recovers S. The result is independent of which compatible circle was found. This is a finite mathematical decoder; the naive circle search can take factorial time and no optimality is claimed.

Combining Sections 3–8 proves the accepted theorem for the unchanged entire source class. No inherited unresolved biological lemma remains in this assembly.

## 9. Adversarial controls, actual executions, and their limits

The independently written [independent_checks.py](independent_checks.py) imports only the Python standard library. It neither imports the author's inverse nor replays an author-provided expected-output file. It was executed under Python 3.12.14; the complete [checks.json](checks.json) includes its SHA-256. All assertions passed:

- 94 exact frozen-population generator projectors on four labels, including 24 assignments with repeated nonzero diagonal rates
- 195 separately built plane binary tree graphs on four through eight labels, with physical-edge deletion used to compute split truth
- 20 tree-family union cases and 108 compatible-order cases checking that boundary recovery yields the same split union
- 30 selected-subset/mechanism chronology cases for the positive child-bridge diamond
- Two independent false-partition controls that defeat the unpruned population-block-union shortcut

The diamond source has edges r->u,v; u->c,h; v->d,h; h->k; k->a,b, with ages r=12,u=9,v=8,h=5,k=2 and tips at zero. All rates can be one and the hybrid weight one half. Degrees are binary; all edges have positive duration; h->k is a bridge; the two original root branches reach distinct c and d tips, making r the LSA; and the cycle r-u-h-v-r with pendant c,d and the k-cherry has an outer-labeled planar embedding. It is admitted.

Both common switchings have the same nontrivial unrooted split ab|cd. At age 9 the independent no-merger supports include ac|bd and ad|bc, which would be false displayed targets. The sure block ab at age 2 precedes the hybrid at age 5. The independent implementation correctly contracts representatives at that barrier and recovers exactly the common displayed-cluster union for every selected subset.

These checks target fragile claims, not a hidden-size census. They do not prove the all-size result; Sections 3–8 do. No full author suite replay, external local archive recovery, empirical experiment, symbolic arbitrary-law parser, or formal verification was performed. A preliminary environment probe found NetworkX absent; the independent checks need no package installation and use no NetworkX. That environment fact is not a mathematical blocker.

## 10. Obligation register and completion boundary

| Obligation | Review evidence | Verdict / remaining boundary |
|---|---|---|
| Exact full source and observation statement | Sections 1–2; pinned author proof | Accepted unchanged |
| Selected-tip consistency on original graph | Section 3 generator/pulse proof | Accepted |
| Observable frozen-population recovery | Section 4 entire matrix-exponential argument | Accepted, including equal rates and arbitrary finite hidden sizes |
| Child-bridge warning interval | Section 5 graph/time proof | Accepted; strict positive duration is essential here |
| Chronological soundness and completeness | Section 6 switching-indexed invariant | Accepted for common, independent, and cross-mechanism comparison |
| Restricted-cluster to quartet target | Section 7 edge-path argument | Accepted |
| Source-to-common-circle and Q-to-S | Section 8; primary Proposition 2.9 | Accepted independently of larger NANUQ score proofs |
| Arbitrary finite all-level quantifiers | Every preceding proof is per finite source without a supplied cap | Accepted |
| Exact-germ/cover implementation | Source interface inspected; independent bounded controls run | Not a full software certification; author implementation has stated narrower arithmetic/input contracts |
| Exact G5 calendar Q/S target fibers | Sections 3–8 | Component complete; this independent acceptance gate is discharged |
| Other observation menus, source recognition, inference, hidden-source recovery | Outside this theorem; separated in author packet and current G3/G4/G6 work | Not relabeled closed |
| Formal proof and historical novelty | No proof-assistant run or exhaustive prior review | Not established here |

Zero inheritance, zero-duration protective edges, arbitrary time-varying edge rates, or removal of the child-bridge/planarity hypotheses are not admitted. The proof does not by itself classify any such extension. Tiny positive inheritance and arbitrarily short positive bridge intervals remain included: exact identification can coexist with arbitrarily poor finite-data separation.

**Final checkpoint.** No residual mathematical gap was found in the reviewed theorem under its exact contract. The local bridge has an independent analytic proof and the structural dependency is directly source matched. The next action is to integrate this precise accepted statement into the head auditor's G5 register and any G7 use, retaining the distinction between exact-law identification and an effective input/finite-data observation experiment. A useful later formalization target is the safe-interval/lifting invariant, but that is not a newly assumed prerequisite for this hand-proof acceptance. The wider master remains governed by its other expressly open obligations.

This completed review supersedes the provisional status of [the first checkpoint](../../communications/2026-10-01-dot-g5-independent-review-2005z-checkpoint.md). It preserves the original author's files and does not claim automatic peer receipt or continuing background activity.
