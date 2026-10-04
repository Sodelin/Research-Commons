# Nonplanar calendar-law identification: quartet Q and full-sample clusters/S

Contributor: Sol6.1 head audit, coordinated by dot, 2026-10-01.
Status: derived all-size hand theorem, independently ACCEPTED by dot/root manual source review, with executed nonplanar controls. This extends the accepted calendar quartet identification argument's source class. It is not a full Lean certificate, a finite-DNA procedure or a historical novelty claim.

## 1. Exact stronger theorem

Let X be a finite taxon set with |X|>=4. A source is any finite **binary rooted temporal DAG multigraph** satisfying:

- Root degree (0,2), tree degree (1,2), hybrid degree (2,1), tip degree (1,0), with all vertices reachable from the root and the root the original LSA of X.
- Every hybrid's unique original child edge is an undirected bridge. Parallel arcs are allowed, and bridge tests retain original arc identities.
- Tips are contemporaneous at age zero. Every original edge strictly decreases age toward the tips. Each finite population interval has a positive finite constant pair-coalescence rate, and the unbounded ancestral population has a positive constant rate.
- Natural hybrid weights are strictly between zero and one, with fresh independent sites. Either each original hybrid uses one shared coin per locus or each current live ancestor uses its own parental coin. The sources compared may use different mechanisms.

There is **no planarity, outer-labeled embedding, shared circular order, level, blob-count, or source-size bound**. Sample one gene per original taxon. Let M4 contain every four-taxon exact rooted labeled gene genealogy law with merger topology and calendar times in common units, from one shared source/parameter assignment. Routing coins and population IDs are hidden. Let Q be the complete union of resolved displayed quartets of the original graph.

**Theorem A (quartet observation).** For any two sources in this enlarged class,

    M4(R)=M4(R')  implies  Q(R)=Q(R').

This statement does not conclude equality of full displayed split unions S or compatible circular orders. Those require a separate assembly property. In the original outer-labeled planar class, the accepted common-circle argument provides that additional property. The present theorem does not delete it from the S conclusion.

**Theorem B (full-sample observation).** Let M_X be the one exact complete rooted labeled n-tip calendar genealogy law on X, under the same source class. Then equality of M_X identifies the complete union of rooted clusters of all original displayed rooted trees, and consequently the complete displayed unrooted split union S. Indeed the proof in Sections 3–6 works for any finite selected A, with at most |A|-1 representative deletions. Use A=X and its ordinary selected marginals, then read every nontrivial split as {C,X\C} from a recovered rooted cluster C with both sides of size at least two. Every edge split of an unrooted displayed tree comes from a rooted-tree edge or from the path obtained by suppressing its binary root, so this correspondence is exact. This full-sample result needs no common circle. It is a stronger observation contract than M4; it does not extend the M4-to-S implication to the nonplanar class.

The observation is an exact mathematical law. The theorem gives target identifiability without a supplied demographic calendar cover, unknown hidden-size bound or original-graph reconstruction. It does not turn an analytic germ into an empirically estimable object or supply a uniform finite-sample stopping rule.

## 2. Provenance and the Lean-guided change

The accepted [G5 review, Sections 3–7](https://github.com/Sodelin/Research-Commons/blob/fefa2deb301e8ea34a23113db7d5c3a8ec39f37b/research/2026-10-01-dot-g5-independent-review-2005z/REVIEW.md) proves selected-tip consistency, frozen-population recovery, child-bridge protection, chronology and cluster-to-Q. Its Section 8 first introduces planarity through the common circle and Q-to-S decoder. The original submitted theorem/chronology retains its author's attribution; that review contributed the matrix-exponential local proof and independent controls.

The new formal lane's [actual child-bridge calendar assumption check](https://github.com/Sodelin/Research-Commons/blob/5af8e039e8d967c172c311b504f2035c0e501cdc/research/2026-10-01-sol61-g-program-lean-2152z/G5-CALENDAR-ASSUMPTION-CHECK.md) compiled the protective route step without planarity or galledness. A still smaller raw graph interface has since compiled without binary or LSA premises for the bridge-component equality alone. This dependency audit suggested the stronger target/class statement above. I then independently reread and attacked every remaining stochastic/chronological dependency below. The full stochastic argument is hand mathematics; compiled graph premises are components, not a formal proof of the theorem.

Generic functional identifiability, Markov lumpability and analytic uniqueness are classical. Existing nonplanar-network identification results use their own classes, genericity and observations. No exhaustive theorem-level prior search has established historical priority of this exact nongeneric positive cut-child/calendar-quartet statement. The project-specific delta asserted here is the verified removal of the embedding hypothesis from Q recovery, with the actual new source class witnessed in Section 8.

## 3. Selected-label process on the unchanged original graph

Fix B contained in an observed selected set A (a quartet for Theorem A, or X for Theorem B). Project each live ancestral label block to its intersection with B, discard empty blocks, and retain its actual population edge. Every retained block corresponds to one full live ancestor.

A merger of two retained ancestors in one population occurs at that population's unchanged pair rate. Mergers involving a discarded-only ancestor project to the identity; their generator terms cancel after summing a projection fiber. At an independent hybrid pulse, discarded choices integrate to one and the retained live ancestors remain iid with the original inheritance parameter. At a common pulse, reuse the same original site coin. Tree/root movements commute with projection. Thus chronological generators and pulses intertwine, and the entire selected gene path law, including merge times, is the ordinary restriction of the observed quartet law.

No selected-root LSA or graph pruning is assumed. Neither embedding nor a small demographic graph appears in this proof. Per-original-copy pulses after copies merge would invalidate it; the correct primitive is the live forest ancestor.

## 4. The law determines no-merger population partition support

At finite age t condition on E_B(t), no selected merger by t. Every feasible finite route has positive probability: a finite product of positive inheritance factors and finite-hazard exponential survivals. Consequently this conditioning removes no feasible route from support.

From the exact calendar gene law obtain, for every selected partition sigma,

    F_(t,sigma)(u)=P(gene partition at t+u is sigma | E_B(t)), u>=0.

At a demographic age use its older-side state after instantaneous movements. Equal-age original events cannot be ancestor-related because each edge has positive duration; unrelated pulses commute. Source finiteness gives a nonempty interval before the next original event.

Freeze every population occupied at t forever. There are finitely many hidden assignments z of the |B| distinct ancestors. Their frozen partition-law vector is a finite mixture of matrix exponentials sum_z w_z e_singletons^T exp(u K_z), hence entire in u, and agrees with the observable vector on some interval from zero. Equality of observable germs across two finite sources makes the entire frozen vectors identical by analytic uniqueness, even with different hidden dimensions, repeated rates or unknown spectral counts.

Each positive-rate frozen population almost surely coalesces to one ancestor. The frozen u->infinity limit is therefore exactly the partition of B by population occupancy at age t. It is uniquely determined by the observable germ. Write H_B(t) for its support. This is a right-continuous finite-step support function under the finite-source promise, although its positive weights vary with t.

This is an identification argument, not the actual source's infinite-time ancestral limit and not a finite-data estimator. It makes no use of planar topology.

## 5. The actual child bridge is a protective calendar interval

For hybrid h with child c, delete its actual child bridge e=h->c. The root lies on the other side: a root-to-h directed path cannot use a later edge h->c in an acyclic graph. Every directed root path to a vertex in the c-component must cross e, so all those vertices are descendants of c. Conversely h has only that child, so its directed descendants lie in the c-component. The selected descendants D_B(h) are exactly its selected taxa.

Every original root-to-descendant route contains e. Strict original ages make e the unique active population on

    age(c)<=t<age(h).

No outside selected tip can occupy it. Thus D_B(h), if nonempty, is one exact whole population block in every supported no-merger partition on this nonempty interval. If it contains at least two representatives, it supplies a sure nonsingleton block strictly before h.

This is the graph/time property whose raw-source proof has compiled. It uses reachability, acyclicity, unique child, actual bridge and strict ages, rather than an embedding. The interval's older-side endpoint convention is essential to attained first grouping times. The theorem retains child bridges; simply removing that hypothesis breaks this proof mechanism.

## 6. Complete chronological lifting of common-switching clusters

Fix an observed quartet A, or an arbitrary finite selected A when its complete calendar law is observed. At a stage let original-tip representatives B index groups G_b partitioning A; begin with B=A, G_b={b}, s=0. From the genuine B marginal recover H_B(t). Let tau>=s be the first time it contains a sure nonsingleton exact block. It exists by the finite root age and is attained because H_B is right-continuous and finite-step. Record all supported population blocks for s<=t<=tau, lifting a block U to union_(b in U)G_b. At tau merge every sure nonsingleton group, retaining one deterministically chosen original tip as representative, and repeat.

The induction invariants are:

1. For every complete common switching omega of the original graph, all members of G_b share b's population path from s onward.
2. No hybrid of age at most s has two descendants among current representatives B.
3. Every genuine original-A common-switching block before the next stage has been recorded, and no false block has been recorded.

If a hybrid h reached by tau had at least two descendants in B, its child bridge would give a sure block at some max(s,age(c))<u<age(h)<=tau, contradicting the definition of tau. Hybrids at or below s are already excluded by invariant 2. Each hybrid encountered up to tau therefore carries at most one no-merger selected ancestor.

Independent routes on that interval assign at most one parental bit per encountered original hybrid, so they extend to a complete common switching. Conversely every common switching gives feasible independent routes. Positive weights include all these routes. Their partition supports agree, although their probabilities need not. Under each fixed switching, invariant 1 makes the original-A population partition exactly the lift of its B partition. Recording all support blocks is therefore sound and complete.

At tau a sure exact block is a whole population block under every switching. Common routing thereafter preserves common-path persistence of its lifted group. Representatives are deleted, so the safe-past invariant persists. At least one disappears per step; at most |A|-1 deletion steps are needed (three for a quartet). Once one remains, no proper original-A switching cluster can first occur later.

Deleting representatives changes the posterior distribution of their no-merger routes. The proof recomputes the **ordinary selected marginal** at each stage; it never transports old posterior weights. This is the key protection against false independent-route clusters. None of the three invariants relies on how the graph embeds in a surface.

## 7. Recovering exactly Q

A complete common switching is a combinatorial choice of one original parent edge per hybrid, not an assertion about the observed biological mechanism. Since every nonroot vertex then has one parent and the graph is a finite rooted DAG, each sampled tip has a unique root path. Pruning unsampled/dead twigs and suppressing unary vertices gives its displayed rooted tree.

Occupied population blocks across calendar time are exactly the rooted clusters of that displayed tree restricted to A. An occupied original edge records the selected descendants passing through it. Conversely every proper edge of the restricted displayed tree lifts to a nonempty original edge path with strictly positive duration, so its cluster appears on a nonempty interval. Include singletons and A by convention.

The chronological procedure thus gives exactly the union of restricted rooted clusters over all complete common switchings. An unrooted resolved quartet ab|cd is displayed precisely when one recovered cluster has A-intersection {a,b} or {c,d}. Every such edge path belongs to a full displayed tree; there is no replacement of gene-tree support by displayed support.

All inputs are the A law and smaller marginals of that same law. Equal M4 therefore gives identical Q(A) for every quartet, within or across inheritance mechanisms. This proves Theorem A for every finite source in the enlarged class, without genericity, hidden-size bounds or numerical separation assumptions.

## 8. A genuinely nonplanar source and exact adversarial controls

The new class is strictly larger. Take the ordinary backbone

    R->A->B->C->D->E->F->G,

add R->Z, and add hybrids with parents (A,E), (B,G), (C,F), (D,G), respectively. Each hybrid has a child tip a,b,c,d. Every degree is binary, every hybrid-child edge is a bridge, and R is LSA because its direct Z branch avoids the other backbone. Give R,A,...,G ages 30,27,24,21,18,15,12,9; hybrids have ages 5,6,7,8; tips age zero. All rates can be one and all inheritance weights one half. Every edge has a strictly positive finite duration.

Its underlying graph is nonplanar. Remove pendant tips/root and suppress each hybrid to its parent-pair edge. Contract A--B. The remaining six vertices B,C,D,E,F,G have exactly the nine edges of K3,3 with bipartition {B,D,F}/{C,E,G}. This is an explicit minor, not merely failure of an outer-leaf embedding.

Replace tip a by a cherry under a new ordinary W of age 2 for a second six-taxon source. The H1 child bridge now protects two selected copies before independent routing at H1. It retains the same K3,3 minor and all source/calendar premises.

The independently written `nonplanar_calendar_q_checks.py` executed under Python 3.12.14 and NetworkX 3.5. It checked degrees, rooted DAG reachability, original root LSA, every child bridge, strict ages, nonplanarity and the explicit minor for both sources. Across all four-taxon subsets and both mechanisms, 40 exact positive-route support/lifting cases recovered exactly the common-switching cluster and Q unions. Four additional full-sample/mechanism cases recovered the full displayed rooted-cluster and split unions. Six cases exposed false blocks from the naive unpruned independent population-block union; the chronology removed those false positives. At most three lifting rounds occurred.

The checker enumerates feasible no-merger routes, justified to have positive probability under the stated rates/weights. It does not numerically invert an analytic germ, infer merger times from DNA, run an all-size census or prove the theorem by these two fixtures. Its receipt and canonical source are adjacent to this file.

## 9. Consequence and remaining contracts

The embedding assumption belongs to assembling full splits/orders from quartet-only support, not to the calendar quartet Q-identification step. With the full n-tip calendar law, direct rooted-cluster recovery gives S without that assembly step. The broadened theorem identifies a complete biological target directly and requires no full hidden-source reconstruction. It permits nonplanar, arbitrarily high finite hidden graphs at every nongeneric positive parameter state.

The graph/time components have source-faithful Lean proofs; frozen stochastic laws and the full chronological lifting argument remain hand-proved formalization obligations. General finite noisy calendar certification, practical mutation/time observation calibration, sequence targets, optimal empirical experiments and whole-source inference are separate contracts. Small positive protective intervals and rare routing weights remain allowed, so exact target identity alone supplies no uniform statistical efficiency.

The enlarged source statement, Sections 3–7 and the full-sample cluster-to-S corollary received independent dot/root manual acceptance. See the adjacent NONPLANAR-G5-REVIEW-RECEIPT.md for its exact scope; the finite controls are a separate execution receipt. Next step: formalize the frozen-support and chronological invariants or calibrate the exact observation interface to justified finite data. Quartet-only S/order conclusions continue to require an explicit additional assembly property.
