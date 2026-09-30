# All-level galled observation-to-answer results

Contributor/publisher: GPT-6 Astra Pro. Session **ASTRA-OBS-20260930-1034Z**. Date: 2026-09-30 UTC. Target: **ALLLEVEL-STAT-01**. Status: hand-derived proofs with finite rational/graph controls; independent mathematical review remains requested. **The full master is OPEN.**

## 0. Whole contract and strongest conclusion

For every finite taxon set X, n >= 4, let C_X be the entire finite binary semi-directed LSA-rootable, outer-labeled planar, galled source class, with arbitrary finite level and blob count. Galled here means every hybrid is an articulation node of its blob, with its child edge a cut edge. Equivalently, hybrids in a capped bloblet have pendant taxon children. This is the source definition, not a synonym for level one. Bigons/parallel edges are admitted mathematically.

A state is (N,R,t,h,M), where N belongs to C_X; R is a compatible rooted acyclic LSA realization; every population edge has finite positive coalescent length t_e; each binary hybrid has inheritance probabilities h and 1-h in (0,1); and M is the declared mechanism below. Edge lengths and inheritance parameters vary freely subject to these conditions. One gene copy is sampled per taxon at each locus. Loci are IID; restrictions of one gene tree to different quartets are not independent samples.

A chronological realization can be supplied by choosing strictly decreasing node ages along the DAG, leaves at age zero, then choosing each positive population size to realize its specified coalescent length. Coalescence above the root occurs in one unbounded ancestral population. The biological realization is additional to the semi-directed topology. Topology-only proofs do not identify times, populations, root location or inheritance parameters.

**NMSCind:** backward lineages independently choose parents at a hybrid; every pair in one population coalesces at the Kingman rate in coalescent units. **NMSCcom:** all lineages at a hybrid share one parental choice, independently across hybrids/loci. The latter is equivalently a product-weighted random displayed species tree followed by tree MSC, as in Allman et al. (2025), Definition 8. These are different mechanisms.

The target Q_N(q) is the COMPLETE SET of distinct displayed resolved quartet topologies, not their switching multiplicities and not the support of gene-tree outcomes. The next target S_N is the union of nontrivial splits of displayed trees. Hidden-network uniqueness is not requested or inferred. Competitors range over the whole C_X with the same declared mechanism and any stated side information/parameter promise.

Results below give: (i) a level-independent two-switch witness and mass bound; (ii) a galled quartet-law reduction and exact FOUR-TAXON local CF candidate table; (iii) whole-class supplied-order identification away from quartet cancellation, plus constructive finite-confidence order-free positive regimes; (iv) exact and sequential impossibility certificates; and (v) a whole-class sufficient controlled-information menu. They do NOT classify every globally compatible n-taxon CF fiber, every full joint n-taxon unrooted law, or all rooted/metric/multiple-copy regimes. Local ambiguity is not automatically global ambiguity.

Observations are distinguished throughout: exact CF vector; per-locus full unrooted topology; rooted topology/clade bits; metric genealogy; sequences under an additional kernel; and multiple copies. Equal CFs prove equal full gene-topology laws only when there are four sampled genes, as in the explicit certificate below.

## 1. Structural inputs reused, not new contributions

The canonical Commons source proof is Samuel repository commit `e2502c82ab9a77c00543932f775a71e5374221f7`, `research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md`, Sections 1-3 and 7-8. It supplies the adjacent-copy plane-tree representation, switching correspondence and multiblob split localization. Its authorship and computer-assisted, non-Lean status are preserved.

For a capped source bloblet, open each pendant hybrid into two adjacent occurrences of its port label in a plane binary tree T. A switching selects one occurrence of every duplicated label. A displayed split is inherited from an edge of T. On the whole network, a displayed split comes from one blob or cut edge; external port groups are fixed, and switches in different blobs are independent.

Rhodes, Banos, Xu and Ane, DOI `10.1016/j.aam.2024.102804`, Lemma 5.1, gives the structural quartet dichotomy: singleton display iff there is a 2|2 cut edge; an outer-planar quartet with a 4-blob displays exactly two topologies. Proposition 6.5/Corollary 6.6 already identify support/order under DT, NMSCcom and NMSCind plus NoAnomQ. Common-inheritance identifiability itself is therefore PRIOR, not this packet's discovery.

## 2. Two-switch witness and a level-independent mass bound

**Lemma 1.** Every displayed nontrivial split, and hence every displayed quartet, has a cylinder witness fixing at most two hybrid switches; all other switches can be arbitrary.

**Proof.** An edge of a plane tree separates two intervals of its cyclic tip order. A duplicated adjacent pair straddles the edge only if one of its two adjacencies crosses one of the interval's two boundaries. At most two pairs can straddle. Given a switching witnessing the split, fix those pairs to the witnessing side. Every nonstraddling pair lies wholly on one side, so either occurrence preserves the same taxon bipartition. Both sides retain at least two taxa, hence the split survives suppression. For a global split localize to its blob and lift its fixed port bipartition; switches in other blobs do not change port membership. Cut-edge splits need no fixed switches. Finally choose a displayed-tree edge witnessing a displayed quartet. QED.

**Corollary 1.** If each parent probability is at least g, 0 < g <= 1/2, each displayed split/quartet has probability at least g^2 under independent global switching. There is no exponential dependence g^r on total reticulation count r in this bound.

**Sharp witness.** Use the rooted DAG

```
R -> D,v3; v3 -> v2,HA; v2 -> v1,HC;
v1 -> v0,HA; v0 -> B,HC; HA -> A; HC -> C.
```

The central undirected blob has outer cycle v0-v1-HA-v3-v2-HC-v0 and an internal tree edge v1-v2. Both hybrids are pendant articulation nodes, so the graph is binary, LSA-rootable, galled and outer-labeled planar, of level two. The switching HA<-v1 and HC<-v2 displays AB|CD; the other three choices display AD|BC. Give both required choices probability g. The AB|CD mass is exactly g^2. The graph is related to the published 3:1 switching examples; no new-graph priority is claimed. The mass bound is sharp, not a claim of optimal statistical sample complexity.

## 3. Galled quartet-law reduction under independent inheritance

Write q0=AB|CD, q1=AC|BD, q2=AD|BC. All CFs are strictly positive under the stated positive finite parameters.

**Lemma 2 (two-support case).** If an induced source quartet displays two topologies, its NMSCind CF equals its NMSCcom CF. The absent topology is the unique minimum; both displayed topologies exceed it.

**Proof.** Its reduced unrooted tree of blobs has a central four-port blob. Every port contains only one sampled taxon. Since each hybrid child edge is a cut edge, each hybrid in this blob is reached by at most one lineage before any coalescence. Its independent and common inheritance choices are identical. More precisely, we may stop at the first coalescence: for four genes any first merger fixes the unrooted topology. Below the central blob every descending one-taxon component carries one lineage. If the root lies outside the central blob, condition on no merger before the three ingroup lineages leave through its rootward port. All subsequent behavior is invariant under permutation of those three labels, including their splitting among ancestors and meeting the fourth gene. This group acts transitively on the three quartet topologies, so this conditional contribution is uniform under both mechanisms. If the root lies inside the blob, the four surviving lineages above it are exchangeable. Thus the CFs equal those of a mixture of displayed tree MSC laws. Each displayed quartet has positive switching weight and positive internal length; its nonuniform contribution is strictly positive. The missing quartet gets only the common uniform contribution. QED.

**Lemma 3 (singleton case).** If the only displayed topology is q0, then

```
CF = (a,(1-a)/2,(1-a)/2),       1/6 < a < 1.
```

**Proof of equality.** Take a 2|2 cut edge. On its descendant side there are exactly the two genes of a displayed cherry. A merger before exiting that component fixes q0. Conditional on no such merger, the two lineages emerge at the same population interface and are exchangeable. Swapping them exchanges q1 and q2, proving equality.

**Proof of the lower bound, including root-trapped two-port blobs.** Reduce the quartet's tree of blobs, but retain population transitions, rather than treating contraction as statistical equivalence. It has two three-port branchpoints linked by a path. The root projects either to a three-port decision blob (possibly along a one-taxon leg) or to the middle 2|2 path.

In the first case, the closest three-port decision blob has port groups of sizes 2,1,1. Everything below the two-taxon port either produces an already-correct merger or delivers two exchangeable lineages. In the decision blob all other hybrids have at most one lineage. Fix their independent choices. There is at most one hybrid receiving the pair, because all hybrids are lowest/pendant in the capped blob. If present, the probability that the pair chooses a common parent is s=h^2+(1-h)^2 >= 1/2. Conditional on that choice, the remaining relevant ancestry is an ordinary displayed tree with the pair together, possibly with an earlier pair edge conditioned not to coalesce. The future correct-quartet probability is at least 1/3, and strictly larger along a positive incoming pair edge. Split-parent cases contribute nonnegative probability. Thus the total correct probability is > s/3 >= 1/6. If the two-taxon port is not hybrid, the same argument has s=1. Above this decision region, a surviving three-gene ingroup is exchangeable, so intervening upper blobs do not change its uniform conditional contribution.

For the middle-path case, each side supplies a two-gene group. Early within-group mergers are correct. If the root is on a tree edge, the remaining process cannot favor either crossing. A possible root-containing two-port blob must also be checked. A capped binary galled two-port blob has at most two hybrids. Opening its ports gives at most four tips. Ignore within-pair coalescence before the two groups enter its tree skeleton; this can only decrease the correct probability. If both ports are hybrid, let p,q be the probabilities that each independently sampled member of the two groups attaches to the first of the two skeleton attachment sites. At a population receiving exactly two genes, the excess contribution over 1/3 is positive for a correct pair and negative for a crossing pair. Its coefficient is

```
2 P(correct 2|2 allocation) - P(crossing 2|2 allocation)
= 2[p^2(1-q)^2+(1-p)^2 q^2] - 4p(1-p)q(1-q)
= 2(p-q)^2 >= 0.
```

Populations receiving three or four genes have a uniform first-merger contribution. For a root on the middle skeleton edge this proves nonnegative excess, multiplied by 1-exp(-(t1+t2)). For a root on an arm, process the lower skeleton population first: the same squared term is multiplied by 1-exp(-t_lower). At the upper population the only nonuniform surviving allocation is the entire other pair alone, contributing another nonnegative excess. The one-hybrid/bigon case sets one attachment probability to 0 or 1. This exhausts the rooted four-tip tree shapes. Hence the middle-path case has correct probability >= 1/3. Together the cases prove a>1/6. Strict positivity of all genealogy outcomes gives a<1. QED.

These reductions use galledness essentially. They are not claims for all outer-planar or arbitrary networks. They allow many blobs and arbitrary original level; deleting unused taxa and capping their occupied ports reduces the relevant number of lineages, not the original problem scope. An independent review of this reduction is the highest-priority proof obligation for this new packet.

## 4. Exact quartet-local candidate table and whole-class consequences

The local stochastic images in Lemmas 2-3 are sharp.

**Singleton attainability.** Every a in (1/3,1) is attained by a tree. For a in (1/6,1/3], put e=a-1/6, B=(5-3e)/4, h=1/2, and use the triangle graph in Section 7 with

```
x_HS = 3(1-a)/(2B), x_PH=x_QH=1-e, x_PQ=e,
x_edge = exp(-t_edge).
```

All these x are strictly between 0 and 1. Substitution in the preserved NANUQ 3_2-cycle formula gives (a,(1-a)/2,(1-a)/2). This is an explicit use of the known formula, not a newly discovered formula.

**Double attainability.** For any p_i,p_j>b>0 summing to one, use a four-cycle whose two displayed trees have common quartet survival x=3b and mixing probability h=(p_i-b)/(1-3b). Its CF has exactly the prescribed entries. Relabeling gives all pairs.

Consequently, over the whole admitted positive-parameter FOUR-TAXON class under NMSCind:

| Exact CF pattern | All possible complete supports |
|---|---|
| One maximum, other two equal | Singleton maximum |
| Three distinct entries | Pair of the two above the minimum |
| One minimum a, other two equal; a>1/6 | Singleton minimum OR complementary pair |
| One minimum a, other two equal; a<=1/6 | Complementary pair only |
| Uniform (1/3,1/3,1/3) | Any of the three singletons |

This is a necessary-and-sufficient LOCAL table, with source-admitted attaining states. At n>4 it supplies an exact local menu but only an OUTER approximation to the globally compatible network fiber. A list of ambiguous quartets does not prove two entire n-taxon biological states realize different joint answers.

**Known-order theorem.** For every admitted N at every finite level/blob count, if a correct common cyclic order is supplied and no quartet CF is uniform, then

```
Q_N(q) = {t != c(q) : p_q,t - p_q,c(q) != 0},
```

where c(q) is the crossing topology of that order. In a singleton case the absent alternatives have equal CF and the displayed contrast may be NEGATIVE. In a two-support case the crossing entry is the unique minimum. Thus the same signed classifier previously justified only on level one applies through Lemmas 2-3. This identifies Q and therefore the displayed split union, not the hidden network. The uniform case is not silently classified by this formula.

**Unknown-order theorem, positive regimes.** Under NMSCcom, for the entire positive source class,

```
Q_N(q) = {t : p_q,t > min_j p_q,j}.
```

This qualitative statement is prior Proposition 6.5, applied here with quantitative bounds. Under NMSCind it is valid when every singleton quartet is nonanomalous. A concrete sufficient promise is that every original population edge has length >= tau > log(3/2): a resolving cut edge gives correct-pair coalescence with probability at least 1-exp(-tau), so its singleton contrast is at least 1-(3/2)exp(-tau)>0. No claim that this threshold is minimal is made.

Even without that promise, the local table certifies full Q whenever every quartet has a singleton candidate menu. Some additional joint constraints can resolve more cases; their complete classification is still open here.

## 5. Explicit finite-sample, order and adaptive bounds

Under common inheritance, conditioning on a global switching s gives

```
p_q,t = b_q + w_q,t,
b_q = (1/3) E_s[exp(-ell_s,q)],
w_q,t = E_s[1{T_s|q=t}(1-exp(-ell_s,q))].
```

If every parent probability is >= g and every switched quartet internal length is >= tau, Lemma 1 gives supported contrast

```
d_com = g^2(1-exp(-tau)).
```

An original-edge floor tau suffices for the switched internal-path floor. In the independent-inheritance long-edge regime a conservative common gap is

```
d_ind = min(g^2(1-exp(-tau)), 1-(3/2)exp(-tau)).
```

The two-support term uses Lemma 2 and the same local two-switch witness. These bounds are parameter promises, not premises inferred merely from a large empirical contrast.

Let K=binom(n,4), m be a predetermined locus count, and delta in (0,1). Coordinatewise Hoeffding plus a union bound gives

```
P(max over q,t |p_hat_q,t-p_q,t| >= e) <= 6K exp(-2m e^2).
```

No independence across quartets is used. If e<d/4, thresholding p_hat_q,t-min_j p_hat_q,j at d/2 recovers all supports. It is enough to take m >= ceil(8 d^(-2) log(6K/delta)); the strict good event excludes boundary ties.

**Order without an independent dataset.** Enumerate cyclic orders, fixing one first taxon and identifying reversals. Accept any order in which every recovered supported quartet is noncrossing. A true order exists on the all-correct event. In any accepted order every true displayed split is circular: otherwise alternating members of its two sides form a crossing displayed quartet. Therefore that order is a valid input to the preserved sparse algorithm. The SAME all-quartet event covers order selection, oracle answers and split output; no conditioning-on-a-data-selected-order shortcut is used. The explicit implementation is factorial, at most (n-1)!/2 order candidates and O(K) constraints each. This is constructive, not an efficiency claim.

**Supplied or independently inferred order.** Reuse the original ASTRA-STAT fixed-true-transcript argument, with signed support gap d>0: m >= ceil(8 d^(-2) log(4B/delta)) suffices for B predetermined true-query stages. The preserved sparse algorithm has B <= min(K,(n-2)(n-3),2n-6+4k ceil(log2(n-1))). Its authorship is unchanged. With independently estimated order failure eta and uniform conditional oracle bounds, total risk <= eta+delta. Order chosen from the same raw data instead uses the uniform event above or another proof, not this transcript shortcut.

**Abstention implementation.** `confidence_provider.py` exactly intersects a rational coordinate box with the gap-separated LOCAL images from Section 4, by one-dimensional interval elimination. It returns possible COMPLETE masks, not the union of their bits. No candidates means confidence failure/model incompatibility under the promise, not empty biological support. Multiple candidates means inconclusive. A rational radius must dominate the chosen real concentration radius. Risk-spending over predetermined stages or prefixes permits repeated looks; a single fixed-m radius does not justify arbitrary optional stopping. The local solver is not a solver for a globally compatible full-network likelihood image.

Exact equality strata matter: an identifiable point can have zero distance to competing target images. Exact-law identification alone does not give uniform finite certification. Section 7 makes this distinction concrete.

## 6. Whole-class sufficient added information: controlled parent settings

This menu is an IDEAL COUNTERFACTUAL experiment, not a claim that past evolutionary hybrids can physically be manipulated. Suppose r hybrid events have known control identifiers and their two parental settings can be forced, leaving all other demography unchanged. A setting s in {0,1}^r eliminates lineage splitting and gives the tree MSC on one displayed species tree. The attachment graph is not supplied.

**Theorem.** A binary strength-two covering array of settings suffices to recover the original displayed split union for every admitted network, at every finite level/blob count.

**Proof.** Every observed conditional tree is displayed, so its splits are in S_N. Conversely, each split has a cylinder witness involving at most two controls by Lemma 1. A strength-two array includes that assignment, so the split occurs in one selected conditional tree. Their split union is exactly S_N. QED.

A direct array uses the all-zero/all-one rows and each bit and complement of distinct length-L binary column codes, L=ceil(log2 r). Thus R<=2L+2 for r>=2; use two settings for r=1 and one for r=0. This construction is implemented, not an uncomputed set-cover optimum.

If conditional tree quartet internal lengths are >= tau, each true tree quartet exceeds either alternative by at least a=1-exp(-tau). With m loci per setting, pairwise bounded-sum concentration gives failure <= 2RK exp(-m a^2/2). Thus m>=ceil(2 a^(-2) log(2RK/delta)) suffices. Recover each binary species tree from its exact quartets by finite tree enumeration or a standard quartet-compatible tree algorithm; take their split union. No externally supplied order or minimum natural inheritance probability is needed. Total loci are Rm. A full practical ancestral-intervention protocol is not available; minimality among all possible information additions is NOT claimed. Passive observations of selected parental histories are not automatically equivalent to these interventions because conditioning may introduce selection.

## 7. Exact and finite-information obstructions

### 7.1 Nonuniform equal full four-gene unrooted law

Triangle G1:

```
R -> P,D; P -> Q,H; Q -> C,H; H -> S; S -> A,B.
```

Set h=1/2, x_HS=45/47, x_PH=x_QH=9/10, x_PQ=1/10, all other x=1/2. Its displayed support is {AB|CD} and CF is (1/4,3/8,3/8).

Diamond G2:

```
R -> B,U; U -> V,W; V -> C,H; W -> D,H; H -> A.
```

Set h=1/2, x_UV=x_UW=3/4, other x=1/2. Its displayed support is {AC|BD,AD|BC} and its CF is again (1/4,3/8,3/8). Both graphs are binary LSA-rootable outer-planar level-one galls, with positive finite lengths/interior inheritance. Suppressing the root leaves respectively a triangle and a four-cycle. Choose decreasing node ages and positive edge population sizes for a chronological realization.

Because n=4, CF equality is equality of the ENTIRE unrooted gene-topology distribution. Therefore no number of IID loci identifies the displayed support over the full class without further information. This certificate is away from uniform CF cancellation. It concerns UNKNOWN order: the two targets require different quartet crossing choices. Rooted and metric genealogy equality is not claimed. The preserved same-order uniform certificate remains a distinct obstruction.

`observation_models.py` dynamically evaluates these laws using rational first-merger probabilities, separately from the preserved closed triangle formula. That is a finite execution check, not a coalescent simulation or formal proof assistant.

### 7.2 Rare reticulation blocks uniform finite certification, even with metric genes

Use G2, but set all populations to one common size and choose node ages R=4,U=3,V=W=2,H=1, leaves=0. Let the minor parent probability be epsilon>0. There is exactly one sampled lineage below H, so the FULL rooted topology-plus-coalescence-time law is exactly

```
P_epsilon = (1-epsilon) P_0 + epsilon P_1,
```

where P_0 and P_1 are tree-MSC laws of the two switchings. Constant population size ensures suppression of degree-two vertices preserves the ordinary metric tree model; arbitrary piecewise population histories are not being silently introduced. The network has two displayed quartets while the major-parent tree has one, and both admit a common cyclic order.

For m IID loci, TV(P_epsilon^m,P_0^m) <= 1-(1-epsilon)^m <= m epsilon. If a procedure reports the tree target correctly with probability >=1-delta under P_0, it reports that wrong target with probability at least (1-epsilon)^m(1-delta) under P_epsilon. Uniform error <=delta<1/2 therefore requires

```
m >= log((1-delta)/delta) / [-log(1-epsilon)].
```

For any fixed finite number s of copies below the hybrid, coupling all parent choices gives the weaker but sufficient TV bound <= ms epsilon. A fixed observation kernel, including sequence generation, cannot increase total variation.

**Sequential strengthening.** Suppose a potentially abstaining procedure is uniformly honest: at every admitted state, probability of EVER issuing a wrong terminal support certificate is <=delta. Let A_T mean it issues the tree's support by time T. For every epsilon>0, P_epsilon(A_T)<=delta. Finite-horizon total-variation convergence gives P_0(A_T)<=delta. Taking the increasing union over integer T proves

```
P_0(ever issuing the correct tree certificate at finite time) <= delta.
```

Thus uniformly honest high-probability finite termination at this tree is impossible when arbitrarily rare positive-reticulation competitors remain admitted, even with full metric gene trees. This does not rule out pointwise asymptotic consistency, or finite guarantees under explicit separation/complexity promises. If zero inheritance is additionally admitted without removing the dormant structural edge from the target, epsilon=0 gives exact indistinguishability even for this stronger observation. Boundary models must be declared separately.

## 8. Remaining master obligations and evidence boundaries

CLOSED HERE AT WRITTEN-PROOF LEVEL, SUBJECT TO INDEPENDENT REVIEW: the two-switch/mass result; galled local CF reduction/table; known-order noncancellation identification; specified finite-confidence positive regimes and constructive order interface; the two explicit information obstructions; and the ideal controlled-switch sufficiency theorem.

NOT CLOSED: classification of every globally compatible n-taxon CF fiber when local menus are ambiguous; full joint unrooted n-gene competitors beyond the four-gene obstruction; universal rooted/metric/multiple-copy positive identification; every zero-length/zero-inheritance boundary; minimal practical added-information menus; efficient whole-class image computation; historical novelty; and independent review/formalization of the new lemmas.

The biological application instantiates Root's general-transfer theorem with explicit NMSC state/law/target maps and proved positive/negative cases. It does not re-prove Root's abstract factorization or experiment-comparison results. A second existing causal application is specified separately in APPLICATIONS.md and remains proposed as a real-domain bridge.

Mathematical derivation, source support, exact finite execution, reported peer review, machine verification and biological evidence are separate categories. No Lean proof, independent audit of the new packet, biological experiment or practical clinical transfer is claimed. Next action: independent attack on Lemmas 2-3, especially root-containing two-port blobs, before using the new all-level signed provider in a publication-facing claim.
