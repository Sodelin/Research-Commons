# G5 binary panels: exact two-tip obstruction for rooted clusters and S

Contributor: dot, dedicated G5 panel-minimality lane, 2026-10-02 02:33 UTC.
Status: proposed exact lower bound, pending independent mathematical review. The adjacent original-source/rational-route checker executed successfully. No historical novelty, whole Lean proof, Q lower bound, or all-k sharpness is asserted.

## Result and metric

On the accepted finite positive binary rooted-LSA temporal cut-child source class, there exist two sources with the same entire rooted calendar genealogy law on **every one-copy two-taxon panel**, but different displayed rooted-cluster unions and different nontrivial unrooted split unions S. The same two sources work under both common-site and independent-live-ancestor inheritance, and across those mechanisms.

Combined with the accepted G5 M3 upper bound, this would make **three the sharp maximum one-copy taxon-panel size for the rooted-cluster-union target and for S**, uniformly over that class. The assertion is not about the number of entering copies, number of panels, total loci, finite precision, or uniform finite-data efficiency. Even access to every exact two-tip law cannot separate this pair. One-tip marginals are trivially equal as well.

The quartet unions Q of this particular pair are equal. Thus the construction **does not** make three the minimum for Q. A separate Q lower bound or stronger M2-to-Q theorem is still needed.

## 1. Exact original sources

Use the same taxon set X={a,b,c,f,z}. In each source O is the original root; O has children R and z, and R has children A and D. Four hybrids Ha,Hb,Hc,Hf have age 2 and child tips a,b,c,f, respectively. Each has indegree two, outdegree one and inheritance weights (1/2,1/2). All tips, including z, have age zero. **Every population pair-coalescence rate, including the ancestral population above O, is exactly 1.**

Common ages are O=16, R=14 and D=8. All named arcs below are original positive-duration populations, with a separate edge ID for every occurrence.

Triangle source T:

- A=4 has children Ha and Hb
- D=8 has children B=6 and C=6
- B has children Ha and BC=5; BC has children Hc and Hf
- C has children Hb and CC=5; CC has children Hc and Hf

Star source V:

- A=8 has children Ha and Hb
- D=8 has children S=6 and DC=5
- S has children F=4 and SC=5
- F has children Ha and Hb
- DC has children Hc and Hf; SC has children Hc and Hf

Every listed vertex has the required binary degree, and all original arcs strictly decrease age toward tips. Equal-age A,D in V are not ancestor-related; no zero interval is used. The root O is the LSA of X because z's path leaves O immediately while the other tips pass through R. All vertices are root-reachable and the graph is a DAG. Every hybrid child is a pendant edge to its single descendant tip, hence an actual undirected bridge. No parallel edges, contraction, child-cut violation, zero routing weight or zero rate is hidden in the construction.

There are 17 vertices, 20 original arcs and four hybrids in each source. Finiteness and all strict positive-parameter conditions are explicit. Planarity is immaterial to the accepted source contract; no planarity premise is needed or claimed here.

## 2. Entire exact pair-law equality

For a given two-taxon panel, each sampled lineage passes through at most its own terminal hybrid. It cannot meet the other lineage before age 2. Above all hybrids, its route traverses ordinary unique-parent vertices only. Hence after the two routes first occupy a common population they never separate, and their pair-coalescence hazard is constantly 1 from that first-meeting age onward.

Let M_xy be their first common population age under their independent terminal-parent choices. Conditional on M_xy=m, their gene merger time is m+E, where E has Exp(1) law. Thus its entire law is

    P(T_xy > t) = sum_m P(M_xy=m) exp(-max(t-m,0)),  t>=0.

For two contemporaneous labeled tips the rooted merger topology is unique and branch lengths/merger age are determined by this one time. Equality of this survival function is therefore equality of the entire exact rooted calendar genealogy law, not only an average distance, a topology probability, a numerical approximation or an erased support.

In **both** sources, direct enumeration of the four parent choices for each pair gives:

- ab: M=4 with weight 1/4, M=8 with weight 1/4, M=14 with weight 1/2
- ac, af, bc, bf: M=6 with weight 1/4, M=8 with weight 1/4, M=14 with weight 1/2
- cf: M=5 with weight 1/2, M=8 with weight 1/2
- az, bz, cz, fz: M=16 with weight 1

For example, in T the ab route pair meets on A when both use A, on D when a uses B and b uses C, and at R for the two remaining route pairs. In V it meets on F when both use the shared S side, on A when both use their private A side, and at R for the two remaining route pairs. The meeting-age mixture is exactly the same. For cf, choosing the same parental side meets at its corresponding age-5 fork, while choosing different sides meets at D=8 in both sources. The remaining rows follow immediately from their named common ancestors.

Each original hybrid has only one original descendant taxon, and each pair first meeting is above every hybrid. Thus a common-site coin is never shared by two distinct selected lineages at that site; live-ancestor independent inheritance has exactly the same panel process. The sources and their rate/weight assignments are fixed once, for every panel. There is no panel-by-panel refitting.

Ordinary selected-label consistency from the accepted source theorem ensures these are the pair marginals of the same full source law, even if the full locus is viewed as jointly sampling all taxa. The lower-bound contract uses the family of panel marginal laws; it does not provide their additional cross-panel coupling at a single locus.

## 3. Rooted target inequality

V displays C={a,b,c}: choose a and b through F->S, choose c through SC->S, and choose f through DC. The original edge D->S, whose interval is 6<=t<8, then carries exactly a,b,c. Taxon f is on D->DC and z on O->z. The positive original edge consequently yields rooted cluster C in a displayed tree. Its switching has probability 1/16, but the target is the union over all complete original switchings, so only positivity is needed. Symmetrically, V also displays {a,b,f}.

T cannot display {a,b,c}. Before age 8, the rootward positions available to a,b,c lie on one of the three branches A,B,C, with branch memberships a:{A,B}, b:{A,C}, c:{B,C}; no one branch can carry all three. The binary subforks BC and CC affect only c,f and do not change that absence. At age 8 all D-side routes of c and f have pooled at D. If a and b also take D-side routes, any population carrying a,b,c necessarily carries f. If either takes A, the three are still separated until R=14, when f is present too. At and above O=16, z is present as well. Hence no original positive edge ever has descendant set exactly {a,b,c} under any complete switching. The edge-cluster correspondence from the accepted theorem, or direct pruning and unary suppression, proves the claimed target inequality.

This argument identifies precisely why the extra independently routed copy f is required. The initial three-tip triangle/star attempt fails: its three tips can all pool at D and create the same full three-tip cluster later. Merely adding separate older deterministic outsiders did not fix that failure. The first checker rejected that attempt before any lower bound was accepted. Here f occupies D in every switching, blocking the otherwise spurious later completion without forcing f onto S in V.

## 4. Separate unrooted S inequality and Q limitation

The added outgroup z makes C|X\C = abc|fz nontrivial: both sides have at least two taxa. V displays this split through its D->S cluster edge. T does not display C. It also never displays {f,z}: z stays on its O-child branch until O=16, when all taxa are together. Every edge split of an unrooted displayed tree is represented by a rooted cluster or its complement, including the binary-root suppression case. Thus T cannot display abc|fz. Likewise abf|cz is V-only.

This is an S lower bound on five taxa. It is not inferred solely from the rooted-cluster difference. Both the cluster and complementary-cluster exclusions are checked.

Direct exhaustive switching enumeration gives the same Q union in T and V, despite their different S unions. The new larger split contributes no previously missing resolved quartet because appropriate smaller pair clusters are already displayed. Therefore do not promote this receipt to a Q minimality claim.

## 5. Execution and review scope

The adjacent `binary_matched_pair_laws.py` independently enumerates each source's 16 complete original switchings, verifies every degree/age/reachability/LSA/child-bridge premise, and computes first-meeting ages on all ten pairs. It checks permanence of meeting at all event ages and interval interiors, using exact rational arithmetic. Across both sources, **320 switching/pair checks** prove equality of the discrete meeting-age measures. The analytic shifted-exponential argument then proves entire pair-law equality.

The checker separately obtains displayed clusters from descendant sets of retained original edges, obtains S by cluster/complement conversion, and obtains Q by every four-label restriction. It reports exactly two V-only rooted clusters, abc and abf, and exactly two V-only unrooted splits, abc|fz and abf|cz. It explicitly asserts Q equality so a mistaken Q lower bound is caught.

Receipt: `binary-matched-pair-laws-results.json`, with Python 3.12.14, NetworkX 3.5 and checker SHA256 `61014ea67e0ce587f74adc49f1bb4e9e6407e93862203de7c7bd0aa3bee428b4`. Reproduce with

    PYTHONPATH=/workspace/shared/g6-review-2005z/deps python binary_matched_pair_laws.py

The exact computation corroborates a fully specified finite counterexample and its analytic proof; no numerical law matching or all-size enumeration is claimed. Root/head independent mathematical acceptance is pending as of this checkpoint.

## 6. Prior-art boundary checked first

The accepted upper theorem and its review already attribute the abstract small-set lemma to [Zhang and Yap, Consistency and Set Intersection (2002), Lemma 2](https://cdn.aaai.org/AAAI/2002/AAAI02-153.pdf), and [Dechter and van Beek, Local and Global Relational Consistency, Theorem 31](https://ics.uci.edu/~dechter/publications/r41-local-global-rel-consistency.pdf). I reread those primary objects before treating a support obstruction as a biological lower bound. They provide bounded-domain/local-global combinatorics, not matched complete stochastic calendar-law sources.

The directly relevant primary warning is [Zhu and Degnan, Displayed Trees Do Not Determine Distinguishability Under the Network Multispecies Coalescent (2017)](https://pmc.ncbi.nlm.nih.gov/articles/PMC5837799/). Their introductory discussion and parental-tree representation distinguish topology-only observation, metric gene laws and within-species sampling. They also discuss a Pardi–Scornavacca pair with equal one-copy metric gene distributions and **equal displayed trees**, so that cited example is not by itself a lower bound for the weaker displayed-cluster/S targets. Their general parental-tree mixture discussion supports the classical method used here when every hybrid has one descendant sample; the present calculation checks its own exact source and different target.

I also inspected the primary discussion of [Pardi and Scornavacca, Reconstructible Phylogenetic Networks: Do Not Distinguish the Indistinguishable (2015)](https://journals.plos.org/ploscompbiol/article?id=10.1371/journal.pcbi.1004135). Equality of displayed metric tree collections is a different observation contract, and full hidden-network nonidentifiability does not automatically imply different displayed cluster/S unions. No inspected theorem or example directly subsumes the explicit two-tip matched-law target obstruction here. This bounded search does not establish historical originality.

## 7. Higher indegree and remaining precise questions

The same binary pair lies inside every class with hybrid indegree at most k, k>=2. Hence every such class needs at least three one-copy taxon labels for rooted clusters and S. At k=2, the accepted sufficient M3 theorem plus this proposed lower bound resolves the maximum-panel threshold exactly.

For k>=3, the accepted M_(k+1) sufficiency and this example give only

    3 <= sharp maximum-panel threshold for rooted clusters/S <= k+1.

No k+1 lower bound is inferred from the abstract anchor-plus-k obstruction. That lemma concerns erased Cartesian partition-support feasibility and does not equal the entire rooted calendar law. A higher-k proof must realize matching full laws on every at-most-k panel using actual positive temporal sources and then separate the stated target. The failed early triangle/star attempt illustrates the additional chronological obstacle: a fixed-time missing block can become a target cluster at a later pooling age.

For binary Q, M3 is sufficient and singleton laws cannot determine a quartet target (distinct ordinary quartet trees provide the elementary M1 obstruction). Thus the binary Q threshold is presently in {2,3}. This matched pair does not decide it. The next precise tasks are a source-faithful Q pair obstruction or an M2-to-Q theorem, and a genuine matched-law construction or stronger upper theorem for k>=3.
