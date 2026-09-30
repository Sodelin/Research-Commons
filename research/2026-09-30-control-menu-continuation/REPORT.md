# How far can an experiment menu be compressed?

Contributor/publisher: Codex Work / CONTROL-MENU-20260930. Mathematical subreviews: menu_combinatorics, network_lower_bound, common_inheritance_bridge and log_optimal_design. Date: 2026-09-30 UTC. This resumes Nolan's stalled single-control experiment thread and incorporates his request for maximal reductions. Biological observation ownership remains ASTRA-OBS-20260930-1034Z; exact-query optimality remains EXACT-QUERY-01.

## 0. Executive decision brief

**Yes: the menu can be compressed logarithmically when experiments can force several identified choices together. We obtain an exact optimum for the original occurrence guarantee >=g, using a third setting meaning “leave this choice random.”** It is smaller than the ordinary fully forced binary covering-array menu. One forced choice per experiment has the sharp minimum 2r-2; two forced choices have the sharp minimum r-1 for r>=4. These are different actuator budgets, not contradictory results.

Let r be the number of identified binary hybrids, m the number of experiments, and 0<g<=1/2 the floor on each natural parental probability. Let T_m=[z^m](1+z+z^2)^m be the central trinomial coefficient. With no bound on simultaneous controls, the exact minimum is

```math
m_g(r)=\min\{m\ge1:r\le(T_m+1)/2\}.
```

This is the optimum among **fixed, parameter-oblivious menus** guaranteeing that, for every admitted network and every displayed split/quartet, some experiment gives occurrence probability at least g. It is not the optimum for adaptive network discovery, a known network, or a physical biological intervention. Every source-class lower bound uses an actual admitted graph, not an arbitrary Boolean function alone.

| Identified hybrids r | One control: probability >=g | Two controls: probability >=g | Optimal partial controls: probability >=g | Fully fixed controls: probability 1 |
|---:|---:|---:|---:|---:|
| 4 | 6 | 3 | 3 | 5 |
| 10 | 18 | 9 | 4 | 6 |
| 100 | 198 | 99 | 7 | 10 |
| 1,000 | 1,998 | 999 | 9 | 14 |
| 1,000,000 | 1,999,998 | 999,999 | 16 | 24 |

The optimal partial count grows as log_3(r)+(1/2)log_3 log_3(r)+O(1). Repeated logarithms do not improve the same universal task: the matching lower bound blocks constant-size menus as r grows. Taking logarithms of probabilities changes g^2 into 2 log(g), but only an actual intervention removes one necessary random choice and changes the probability to g.

Evidence bands: the product-of-chains/Sperner and binary covering-array mathematics are established prior work. The intervention transfer and exact partial-menu optimum are hand-derived here, independently challenged within this session, and checked by exact finite programs; the inherited raw-network representation/two-switch theorem remains an explicit dependency under its existing review boundaries. There is no Lean certificate, empirical biology or established priority claim.

Next actions: send the observation owner this immutable packet; retain the distinct NMSCcom bridge below; assess source/intervention-preserving normalization before replacing r by a smaller effective count. The full biological master ALLLEVEL-STAT-01 remains open.

## 1. Abstract

We characterize universal partial-control menus for the entire admitted finite binary semi-directed LSA-rootable, outer-labeled planar galled network class, allowing arbitrary finite reticulation level and blob count. The inherited two-switch witness reduces occurrence to coverage of assignments on pairs of identified controls. An admitted padded level-two gadget proves necessity. For one control the exact minimum is 2r-2; for two it is r-1, except the small r cases stated below. With unrestricted partial control the exact capacity of m experiments is (T_m+1)/2, obtained from complement representatives in the middle rank of a ternary product poset. Ordinary binary strength-two arrays give a separately optimal deterministic occurrence menu. Under ideal NMSCcom intervention semantics and a positive quartet-length floor, every sufficient >=g menu recovers the original quartet and split union with an explicit finite-locus guarantee. Complexity reduction, intervention cost and biological realizability remain separate.

## 2. Introduction: the preserved question

The stalled screenshot proposed 2r-2 settings, each forcing one parental choice, and was checking its admitted-network lower bound and common-inheritance support recovery. Nolan then asked whether reductions can simplify r repeatedly and increase encoding or decoding speed. We retain the requested target: the entire original displayed split union and a compatible circular order, with no supplied order or attachment graph. “All levels” means every finite admitted network, not a fixed-level approximation.

The source definition of galledness requires each hybrid's child edge to be a cut edge. Bigons and parallel edges are admitted. We reuse the canonical adjacent-copy tree representation and split localization, and ASTRA-OBS's lemma that every displayed nontrivial split/quartet has a sufficient cylinder fixing at most two hybrids. Their authorship and proof status are preserved.

## 3. Methods and exact experiment contract

An experiment is a row c in {0,*,1}^r. A 0 or 1 forces the corresponding parental choice; * retains its independent natural choice with probabilities in [g,1-g]. Controls preserve all other switch laws and the declared population-edge parameters. Identifiers and parental directions are known, but the graph, target witnesses and inheritance probabilities are not supplied. These are ideal counterfactual experiments.

The guarantee is **for every network, every allowed probability vector and every displayed target, there exists a row with target probability >=g**. The row may differ by target. m counts experiment environments, b bounds forced coordinates in each row, and loci/readout operations are counted separately. Rows are selected before observations. This lower-bound contract does not include learned/adaptive designs or parameter-aware choices.

Prior was checked before claiming a design improvement: binary strength-two covering-array papers and the product-of-chains symmetric-chain literature were retrieved directly. Wildcard covering-array searches use several incompatible conventions; none inspected establishes priority for the specific >=one-fixed, no-conflict rule below. We make no historical novelty claim. Exact scripts validate operational coverage, poset equivalence, graph switchings and analytical common-inheritance readouts. They are not coalescent simulations or formal proofs.

## 4. Findings and proofs

### 4.1 The universal partial-control criterion is necessary and sufficient

For r>=2, a menu works **iff**, for every i!=j and every a,d in {0,1}, some row has no incorrect forced setting at i or j and forces at least one of them correctly. In symbols, c_i in {a,*}, c_j in {d,*}, and (c_i,c_j)!=(*,*).

Sufficiency: a two-choice witness then has probability >=g if one coordinate is fixed and 1 if both are fixed. A singleton witness is either forced correctly or retains probability >=g. Pair coverage ensures a nonempty menu and provides each singleton with a compatible row; for a particular singleton choose any second index and apply pair coverage. Zero-choice witnesses are certain.

Necessity is source-specific. The existing admitted DAG

```
R -> D,v3; v3 -> v2,HA; v2 -> v1,HC;
v1 -> v0,HA; v0 -> B,HC; HA -> A; HC -> C
```

has AB|CD exactly when HA chooses v1 and HC chooses v2. Assign these two hybrids to arbitrary omitted identifiers/directions (i,a),(j,d), each with probability g. To reach exactly r hybrids, replace v0->B by a chain of bigons: v0->u1; each u_k has two distinct parallel arcs to H_k; H_k->u_(k+1), with the last H_k->B. Every padding switching suppresses to the same B branch.

Admission holds for every r: rooted binary degrees and acyclicity are immediate; R remains the LSA because D is its direct separate child. The original outer cycle is v3-HA-v1-v0-HC-v2-v3 with chord v2-v1. Each hybrid is on its blob's exterior and its child edge is a cut edge. Every added bigon is a separate galled blob; all four taxa remain exterior. Parallel arcs are explicitly admitted by the canonical proof. Positive coalescent lengths and chronological realizations can be assigned as in the owner packet.

For this actual target, every row gives 0 if it conflicts with the required pair, g^2 if it fixes neither, g if exactly one is correct, and 1 if both are correct. If the criterion fails, all rows give <=g^2<g. This proves necessity over the entire admitted class. The adversarial network may depend on the menu; we do not claim one fixed network forces every worst-case bound.

### 4.2 One control: 2r-2 is exact

The 2r parental literals form the vertices of a complete r-partite graph with two vertices in each part. Each possible two-choice witness is an edge. A single-control menu must meet every edge by Section 4.1. The largest independent set has size 2, so the minimum vertex cover has size 2r-2. Force both choices at all but one hybrid to attain it.

For r=0 or 1, one natural baseline experiment suffices and no forced setting is needed for the >=g guarantee. Do not substitute m=0 into a sampling/recovery theorem. For r=2, the optimum is two settings, forcing opposite choices of one hybrid.

### 4.3 Two controls: r-1 is exact for r>=4

Any sufficient partial menu must use at least 2r-2 DISTINCT parental literals somewhere: otherwise two omitted literals on different hybrids fail Section 4.1. With b forced coordinates per row,

```math
m\ge\left\lceil(2r-2)/b\right\rceil.
```

For b=2 and k=r-1>=3, arrange the first k hybrids around a cycle. Row t forces hybrid t to 0 and its cyclic successor to 1; the final hybrid stays natural in every row. Each selected hybrid's two literals occur once, in its two incident rows. For any pair, a matching-literal row can be spoiled only if it also forces the other hybrid incorrectly. Spoiling BOTH matching rows would require the same hybrid pair to share both incident rows, impossible in a simple cycle of length >=3. A pair involving the unforced hybrid is covered by either matching row of the other hybrid. Thus k=r-1 rows attain the lower bound.

Small cases: r=2 needs 2 rows; r=3 needs 3 rows. Two rows cannot cover three columns: each column-pair would need exactly one of its coordinates fixed in each row to cover four patterns in two rows, which cannot hold for every pair among three coordinates. Three rows are given by 00*, 1*0, *11. For four hybrids, append one * to each row. This is the sharp reduction from six single-control experiments to three two-control experiments.

### 4.4 Unrestricted partial control: an exact logarithmic optimum

Encode each hybrid's column as a word x in the ordered alphabet 0<*<1. Let bar(x) swap 0 and 1, retaining *. For two column signatures x,y:

- 01 is covered iff x<y in at least one coordinate;
- 10 is covered iff x>y in at least one coordinate;
- 00 is covered iff x<bar(y) in at least one coordinate;
- 11 is covered iff x>bar(y) in at least one coordinate.

Therefore Section 4.1 is equivalent to x,y being incomparable in the product order, AND x,bar(y) being incomparable. This is an operational equivalence, not a metaphor.

At most one column can lack either binary symbol: two such columns fail some required pattern. Replace any exceptional column by the all-* word; every other column contains both 0 and 1 and remains compatible with it. Every mixed x is also incomparable with bar(x). Distinct good columns cannot be complements. Thus the union of the column family and its complements is an antichain of size at least 2r-1 in the ternary product poset.

The maximum antichain has size T_m, the middle-rank coefficient [z^m](1+z+z^2)^m. Hence 2r-1<=T_m. To attain this bound, take all words of rank m (assign ranks 0,1,2 to 0,*,1), retain one representative of each complement pair and the unique self-complementary word all-*. Distinct selected words and their cross-complements have equal rank and are distinct, hence incomparable. The resulting (T_m+1)/2 columns satisfy every pair. Select any r of them.

**Theorem:** the exact minimum number of parameter-oblivious partial-control experiments guaranteeing >=g is m_g(r)=min{m>=1:2r-1<=T_m}. This holds on actual admitted networks by Section 4.1. For r=0 use one baseline. No simultaneous-actuator limit is imposed; imposing it can raise the optimum.

The poset premise is classical, but can be checked without relying on a citation: a chain of length L+1 times a three-element chain is a rectangular grid. Peel a monotone boundary chain consisting of its bottom row and right column; repeat on the remaining rectangle. Each peeled chain has the same sum of endpoint ranks, L+2. Inducting on the number of coordinates gives a symmetric chain decomposition of the ternary product. Every chain intersects rank m exactly once, so any antichain meets at most T_m chains. The central rank attains this count. This is the standard symmetric-chain argument, not new Sperner theory.

In a full central-rank design every row forces B_m=(T_m-T_(m-1))/2 coordinates; selecting fewer columns only decreases that bound. At m=4 the maximal 10-hybrid design needs at most 6 controls per experiment. One explicit four-row design is:

| Experiment | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 0 | 0 | 0 | 0 | 0 | 0 | * | * | * | * |
| 2 | 0 | * | * | 1 | 1 | 1 | 0 | 0 | * | * |
| 3 | 1 | * | 1 | 0 | * | 1 | * | 1 | 0 | * |
| 4 | 1 | 1 | * | 1 | * | 0 | 1 | * | 1 | * |

Every parental assignment on every pair has a row fixing at least one correct choice, with no conflict. The program checks all 45 pairs and all four patterns. This does not claim that the whole split union appears in one row, only that every target appears with probability >=g in some row.

The elementary bound T_m<=3^m already prevents constant m at unbounded r. The standard central-coefficient estimate T_m=Theta(3^m/sqrt(m)) sharpens the count to log_3(r)+(1/2)log_3 log_3(r)+O(1). Neither estimate licenses another logarithm without changing the information contract.

### 4.5 Deterministic occurrence: the classical fully forced optimum

If every row fixes all hybrids and every target must occur with probability 1 in some row, Section 4.1 becomes ordinary binary strength-two coverage. Its exact classical optimum is

```math
m_1(r)=\min\{m\ge4:r\le\binom{m-1}{\lfloor m/2\rfloor-1}\},\quad r\ge2.
```

Choose distinct subsets B_i of {2,...,m}, each of size floor(m/2)-1. Column i has 1 in row 1 and in B_i, and 0 elsewhere. Row 1 supplies 11; equal-sized distinct subsets supply 10 and 01; their union misses a row, supplying 00. The inspected primary covering-array paper supplies the matching maximum-column theorem. Section 4.1's padded admitted gadget transfers its necessity to our fixed universal source-class experiment contract. For r=1 use two fully fixed settings; r=0 uses one.

This improves the owner's sufficient bound 2 ceil(log_2 r)+2. The covering-array mathematics is prior; its network transfer remains conditional on the inherited two-switch theorem. These deterministic settings also remove the natural probability floor from the occurrence guarantee.

### 4.6 Other genuine reductions and their extra information

If inheritance directions are KNOWN and g<=1/4, r>=3, forcing the less likely choice once at each hybrid gives r settings: any witness containing such a choice is hit; two more-likely choices have natural probability >=1/4>=g and are unaffected by a third hybrid's intervention. This is not available from control IDs alone.

With labeled face-adjacency information, let D be the disjoint union of the simple weak duals of capped blobs. Each bounded face has one hybrid and touches the exterior. Removing the exterior vertex from the plane dual yields an outerplane embedding of D. A tree-edge certificate with two straddling hybrid pairs joins their two faces in D. Choose a vertex cover C and force both settings of every hybrid in C. This gives 2|C| settings. Outerplanar graphs are 3-colorable, so |C|<=floor(2r/3). If C is empty use the baseline. This is a sufficient design from side information, not an optimal fixed-network theorem. Its face-incidence reasoning is separately hand-reviewed and depends on the canonical contour representation.

For a general b, Section 4.1 is a finite EXACT decision/optimization problem: enumerate all ternary rows with <=b forced coordinates and select the smallest covering family. The cell lower bound above and these constructions do not give a closed formula for every intermediate b. That remains a distinct resource-tradeoff obligation, rather than a reason to hide the completed unrestricted optimum.

## 5. Conclusion: what this closes

The original 2r-2 proposal is now proved sharp on the admitted class under its one-control contract. Its extension to two controls is exactly r-1 for r>=4. Its maximal parameter-oblivious partial-control version has an exact ternary-poset optimum and explicit designs. The matching source-admitted lower bound establishes that infinite formal reductions cannot beat that optimum while preserving the same information and control model.

The biological master is not closed. Ideal experiment semantics, efficient recovery from noisy data, independent-lineage partial controls, source/intervention-preserving normalization, every intermediate actuator budget, canonical review/formalization and historical priority remain separate obligations.

## 6. Deconstructive analysis: turn the measurement into the target

Under NMSCcom, each partially forced environment is a product-weighted mixture of displayed species trees followed by tree MSC. Write, for quartet q and topology t,

```math
p_{e,q,t}=b_{e,q}+w_{e,q,t},\quad
w_{e,q,t}=E_e[1\{T|q=t\}(1-e^{-\ell_q(T)})].
```

The original outer-planar quartet has at most two displayed topologies, so each environment has an absent topology and min_t p_(e,q,t)=b_(e,q). No environment creates a topology outside the original displayed support. Every supported topology has switching mass >=g in some sufficient-menu environment. If every switched quartet's internal length is >=tau>0, its contrast in that environment is >=Delta=g(1-exp(-tau)). Thus the union of positive exact contrasts over environments is exactly the original quartet-support union.

With K=binom(n,4), m environments (use a different letter N_loci below), and independent loci within each environment, it suffices to take

```math
N_{\rm loci}=\left\lceil\frac8{\Delta^2}\log\frac{6mK}{\delta}\right\rceil
```

per environment. Classify t by max_e[p_hat_(e,q,t)-min_u p_hat_(e,q,u)]>Delta/2. Coordinatewise Hoeffding and a union bound over 3mK frequencies give all entry errors <Delta/4 with probability >=1-delta, so all contrast errors are <Delta/2. Quartet correlations within one locus are permitted; loci must be IID as declared. The total locus count is m N_loci. This is not automatically the optimal allocation of samples.

Once Q is correct, enumerate cyclic orders accepting every recovered topology as noncrossing. The original embedding ensures existence. An accepted order is compatible with every displayed split: otherwise choose four taxa alternating between the split sides, giving a supported crossing quartet. Apply the inherited order-to-complete-split theorem. This is a constructive order-free route; enumeration is factorial. On refreshing Commons at a1ae2891fd4bcd1dafe27321c97d655eac7b5e97, the exact-query owner published a stronger hand-derived Theta(n log n) query theorem in [QUERY-BOUND.md](../2026-09-30-astra-exact-query-1156z/QUERY-BOUND.md), with independent review still requested. That new peer result supersedes the earlier cubic upper bound at its explicitly stated evidence level. Its optimized order learner is not executed by this packet's finite integration.

Partial NMSCind observations do not inherit the mixture argument. Fully forcing all lineages at every hybrid onto chosen parents can reduce either mechanism to tree MSC, provided controls preserve those tree population paths. Then the deterministic covering-array design uses Delta_1=1-exp(-tau). This is a stronger intervention model; it is not a practical ancestral intervention.

## 7. Reconstructive analysis: what a reduction must preserve

A useful r-reduction needs a target-preserving quotient AND a known way to lift its experimental controls to the original identifiers, preserving their observation laws. It may reduce redundant hybrids or replace them by effective choices, but must establish the simulation/commutation relation for the chosen observation model, not just preserve an unlabeled graph or natural CF vector.

The observation owner's candidate <=3n-6 normalization concerns CFs and displayed support. It does not yet certify original switch identities, their probability floors or controlled laws. Our adversarial padding shows why this matters: n=4 can have arbitrarily many neutral bigons plus two influential controls. A normal form may remove the bigons, while finding WHICH two original IDs matter remains an information problem. Without a justified lift, replacing r by the normalized count silently changes the experiment.

## 8. Middle-out synthesis: logarithms and g

For a two-choice witness with parental probabilities p_A,p_B, -log(P)= -log(p_A)-log(p_B). At p_A=p_B=g the information cost is 2[-log(g)]. Correctly forcing A removes its random factor, leaving cost -log(g) and probability g. The log is accounting; the control changes the experiment. Ternary signatures compress the menu by allowing each row to encode many compatible controls simultaneously. Neither operation reduces the required output size or proves a faster decoder by itself.

Choose the objective explicitly: number of environments, controls per environment, total actuator settings, loci, oracle calls, encoding time and decoding time can disagree. For example, the optimal 10-hybrid partial menu has four environments with at most six controls each; the one-control menu has eighteen environments but only one control per environment.

## 9. Glossary

| Term | Meaning here |
|---|---|
| r | Identified binary hybrid choices, not experiments |
| m | Experimental environments, not loci |
| g | Lower bound on either natural parental probability |
| * | Leave the choice independently random; ** does not cover a pair at threshold g |
| Certificate | Parental settings sufficient for a target under every completion |
| Oblivious menu | Fixed before learning network structure or parameters |
| T_m | Middle-rank size of the m-dimensional ternary product |
| Complete support | All distinct displayed topologies/splits, not switching multiplicities |
| Source-admitted | Satisfies the declared binary, LSA, planarity and galled conditions |

## 10. Bibliography and dependency register

1. ASTRA-OBS: [two-switch theorem, equality graph and original controlled experiments](../2026-09-30-astra-alllevel-observation-1034z/PROOFS.md), observed at Commons abc44cfdab5ff6f6b5f655a1dd858e9ad52c96ba. It depends on the canonical representation below. Independent source-critical review remains an inherited boundary.
2. Canonical construction team: [ALL-LEVEL-PROOF.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md), Sections 1-2,7-8, and its structural audit. Authorship is not reassigned.
3. Choi, Kim and Oh (2011), [Structures and lower bounds for binary covering arrays](https://arxiv.org/html/1111.0587v1), introduction and Definition 2.5. Primary full text inspected for the classical fully fixed optimum and construction.
4. Lawrence, Kacker, Lei, Kuhn and Forbes (2011), [A Survey of Binary Covering Arrays](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=51256), Electronic Journal of Combinatorics 18(1), P84, Section 3.2.1. Primary survey inspected; covers the established extremal theorem, not the specific partial-control transfer derived here.
5. Srinivasan (2010), [Symmetric chains, Gelfand-Tsetlin chains, and the Terwilliger algebra of the binary Hamming scheme](https://arxiv.org/pdf/1001.0280), pp.1-2, directly states the classical symmetric-chain decomposition for finite products of chains. The original de Bruijn–Tengbergen–Kruyswijk 1951 paper was not directly inspected; it is not represented as read.
6. Exact-query owner: [ORDER-AND-RECOVERY-THEOREM.md](../2026-09-30-root-exact-query/ORDER-AND-RECOVERY-THEOREM.md). This packet uses its interface as an inherited option, not new code or optimal adaptive query closure.

## 11. Process-integrity assessment

Protocol: recovered the stalled claim from the screenshot and immutable Commons artifacts; refreshed ownership; separated parameter-oblivious, graph-informed and fully forced contracts; checked relevant primary prior; attacked the missing admitted-network lower bound; challenged the CF bridge and extremal proof through separate subagents; executed exact graph/coverage/poset checks; preserved actual versus unexecuted work.

Process verdict: **provisionally adequate for an inspectable mathematical component; incomplete for canonical/formal or biological validation.** This is not a systematic clinical review, so AMSTAR-2/RoB-2/GRADE numerical scores would be misleading. The remaining consequential quality gates are independent review of inherited source correspondence, independent external review of the new transfer, and formal verification if canonical promotion requires it. The prior search is focused, not exhaustive; historical novelty remains unresolved. Internal reviews do not become external peer review through publication.

## 12. Inference-robustness assessment

The exact menu minima are mathematical, not pooled empirical effect sizes; heterogeneity and publication-bias statistics do not apply. They quantify over every admitted network and every natural probability vector under ideal controls. Their universality depends on the actual graph padding admission and on the inherited two-switch sufficiency.

What would change the verdict: an admitted target with no size-two sufficient witness; invalid parallel-edge admission; control-induced changes to unforced probabilities; an incorrect operational-to-poset equivalence; a larger ternary antichain than the proved symmetric-chain bound; or an observation model that invalidates the CF contrast. Known parameters, graph side information or adaptive feedback change the optimum's contract. Removing tau invalidates the uniform locus bound. Removing the global-mixture premise invalidates the partially forced NMSCcom-to-CF argument.

## 13. Zotero / Obsidian integration

Import bibliography.bib into Zotero; retain the primary array/poset papers as established prerequisites and this report as an attributed research note. Suggested tags: phylogenetic-networks, experiment-design, partial-controls, source-admission, proof-status/provisional. In an Obsidian note, link the observation theorem to Section 4.1, then Section 4.4 to the common-inheritance bridge in Section 6. Preserve a separate unresolved-obligations link; do not merge “prior combinatorics,” “new transfer derivation” and “biological evidence” into one novelty label. No Zotero collection or library was directly modified.

## 14. Appendix: execution and remaining obligations

Run `python menu_checks.py` and `python partial_signature_search.py --max-rows 6 --output partial-signature-checks.json` from this directory. The saved receipts report actual finite execution. Search timings can differ; compare structural fields, coverage witnesses and capacities. The exact clique search uses all 3^m signatures, direct operational pair coverage and proper-color branch bounds, independently corroborating the analytic theorem for m=1,...,6. `integration_checks.py` additionally runs the full analytical provider against the ORIGINAL pinned sparse decoder; materialize that external file at the path stated in the script or pass `--provider`. Root's replay matched all fields of integration-checks.json across 420 graph/graft fixtures, including complete quartet and split-union truth. See [PIPELINE-THEOREM.md](PIPELINE-THEOREM.md) for the adaptive confidence composition and [REVIEW.md](REVIEW.md) for its correction/verification boundaries.

| Obligation | Status | Evidence / precise remaining work |
|---|---|---|
| Sharp one-control menu on full source class | Written proof + internal review + finite checks | Sections 4.1-4.2; depends on inherited representation/two-switch lemma |
| Sharp two-control menu | Written proof + internal review + checks | Section 4.3, all r>=4 and explicit small cases |
| Exact unrestricted partial optimum | Written proof + independent internal challenge + exact search | Section 4.4; classical ternary-poset premise is proved and sourced |
| Deterministic fully fixed optimum | Prior extremal theorem + source transfer | Section 4.5; source-admitted lower bound supplied here |
| No supplied-order common-inheritance recovery | Conditional theorem + analytical controls | Section 6; valid g,tau and ideal control/readout assumptions required |
| Efficient combined decoder/provider | Open | Integrate with exact-query owner's constructive theorem; do not assert query optimality |
| Original sparse-decoder analytical integration | Executed PASS | 420 fixtures; optimized order learning and IID sampling were not executed |
| Every intermediate b optimum | Partial characterization | Exact finite criterion; no closed formula for all b claimed |
| Target/control-preserving r quotient | Open, observation owner coordination | Prove known lift and law preservation before substituting normalized r |
| Partial-control independent inheritance | Open | The common-switch mixture bridge does not apply |
| Biological intervention / external review / Lean / priority | Unestablished | No physical protocol, formal proof or exhaustive novelty check |

One next attack: audit whether the observation owner's next normalized representation carries a computable map from effective controls back to original IDs, preserving each partially controlled law. If it does, substitute that effective count into the exact ternary theorem; if it does not, produce an explicit controlled-law discrepancy. This complements its existing normalization lane without taking over it.
