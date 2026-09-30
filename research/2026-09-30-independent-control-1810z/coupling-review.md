# Coupling and scope review

## Claim that is valid

For every fixed intervention row, a locus-level synchronization program on an independently inheriting network can reproduce the entire gene-tree law of the corresponding common-inheritance intervention row. This is a control-compilation statement. It changes the independently inheriting experiment; it does not preserve its original passive law. It does not require a passive normalization theorem.

Let \(H\) be the original, labeled hybrid set. A row fixes a set \(F\subseteq H\) to prescribed parent choices \(a_h\). At every remaining hybrid, the target common-inheritance row draws one parent bit \(B_h\sim\operatorname{Bernoulli}(\gamma_h)\) per locus, independently over hybrids and loci, and applies that bit to every gene lineage choosing a parent there during that locus.

The independently inheriting experiment must provide an actuator that can force every lineage at a specified hybrid to the prescribed parent. A random control bit persists for the whole locus, including all encounters with that hybrid. The edge/population coalescent process conditional on routing, sampling scheme, and gene-tree observation rule must be the same in the two experiments.

For a known graph, let \(d_h\) be the number of sampled gene copies descended from the child of hybrid \(h\), counting sampling multiplicity. Define

\[
S=\{h\in H\setminus F:d_h\ge 2\}.
\]

Externally draw independent \(B_h\sim\operatorname{Bernoulli}(\gamma_h)\) for \(h\in S\), independently of coalescent randomness and all other locus randomness. Force all lineages at each such hybrid according to \(B_h\). Force the fixed row at \(F\), and leave the other hybrids naturally independent. Then

\[
\mathcal L(G_{\mathrm{controlled\ ind},a})
=\mathcal L(G_{\mathrm{com},a}).
\]

The equality holds for the complete ancestral routing/coalescence history and hence for every measurable gene-tree observable: topology, rooted or unrooted restrictions, branch lengths, coalescence times, ranked tree, or their joint law. It holds for arbitrary finite numbers of sampled copies and original hybrid sites. It is not restricted to triplets or quartets.

When the graph is unavailable, synchronize every unfixed original hybrid. The same conclusion follows without computing descendants. Known hybrid identifiers and parent labels remain necessary for addressing the controls.

## Pathwise proof

For one locus, prepare independent target bits \(B_h\) at all unfixed hybrids and use \(a_h\) at fixed hybrids. Prepare common coalescent randomness, independent of these bits. The target experiment uses each prepared bit at every parent choice at the corresponding hybrid.

Every extant ancestral lineage carries a nonempty block of original sample labels. Coalescence merges blocks; backward lineage inheritance selects one parent and does not split a block. Every lineage entering hybrid \(h\) through its child carries labels drawn from its sampled descendants. Different lineages choosing parents at \(h\) have disjoint original-label blocks: a lineage cannot return to \(h\) after leaving it, because the network is a directed acyclic graph. Consequently, the total number of lineage parent-choice events at \(h\) is at most \(d_h\). In particular, if \(d_h\le 1\), there is at most one natural inheritance choice at that hybrid in the locus.

At a synchronized hybrid or a fixed hybrid, the controlled experiment makes exactly the target routing choices. At an unsynchronized hybrid with at most one visit, couple its sole natural independent choice, if it occurs, to \(B_h\). This is a valid natural independent choice: the bit has the required Bernoulli distribution, is independent of the coalescent randomness and other hybrid bits, and can be revealed only on first use. An unused bit is irrelevant. There is no second lineage choice at this hybrid with which the natural choice must be independent.

Now couple the two coalescent processes using the prepared common randomness. They start in the same state. Whenever a routing transition occurs, they make the same transition. Whenever a coalescent event occurs, they have the same lineages in the same population and use the same event randomness. Induction through the ancestral process makes the complete histories equal almost surely. This also covers histories in which a hybrid receives no lineages.

Applying this construction independently at each fresh locus proves equality of the joint product laws across loci, not merely equality of one-locus marginals. For a row-stratified design, perform it independently within every row.

The child-cut-edge hypothesis is compatible with this sufficiency proof and supplies the intended descendant interpretation. Sufficiency itself needs only the bound on the number of choices at an unsynchronized hybrid; it does not otherwise use the cut-edge structure. The cut-edge hypothesis has a substantive role in the necessity proof below. One gene per sampled taxon makes \(d_h\) a taxon count. With multiple sampled copies, distinct-taxon counting is insufficient: one descendant taxon with two sampled genes can send two lineages to the hybrid.

## Distribution restoration and its assumptions

* The result restores a specified common-inheritance intervention law. Generally it is not the passive independently inheriting law of the original network. The controller replaces independent choices at synchronized sites by correlated choices.
* Exact emulation of the original target weights requires the corresponding \(\gamma_h\). If the controller instead uses \(\widetilde\gamma_h\), it emulates the common-inheritance law with those new weights. A theorem uniform over \(\widetilde\gamma_h\in[g,1-g]\) can still apply; original-weight recovery cannot be claimed.
* The bits must be independent across hybrids and fresh independent loci and independent of the genealogy-generating randomness. Reusing bits between loci does not provide the product law required by ordinary concentration guarantees. Drawing a separate bit for each lineage, encounter, or segment does not emulate a locus-wide shared bit.
* The actuator must address all live lineages that encounter a site and retain the setting for the whole locus. A hybrid is not revisited by an individual lineage in a DAG, but different lineages can encounter it; persistent forcing removes ambiguity about their joint routing.
* Conditional on routing, the controls must retain the specified population process and its parameters. A biological manipulation that changes population size, coalescence rates, migration opportunities, sampling, or locus dependence requires a separate model and does not obtain exact emulation from this proof.
* This is an abstract operational capability, not evidence that a biological intervention accomplishing it exists. Drawing shared randomness is straightforward; applying a parent-specific force to all relevant ancestral gene lineages is the substantive actuator assumption.

## Exact full-history boundary and minimal compiler

The following strengthening is valid in the admitted child-cut-edge class. Assume finitely many sampled copies, finitely many edges, finite coalescent duration on every edge below every hybrid, and natural inheritance weights in \((0,1)\) at every unfixed hybrid. The row's fixed settings and every extra shared control are persistent pre-locus settings. Conditional population dynamics remain the specified finite-rate MSC. The history here records the sampled ancestry's actual routes and coalescent events, not unused random seeds.

For a fixed row, define

\[
M=\{h\in H\setminus F:d_h\ge 2\}.
\]

For a compiler that synchronizes an additional set \(S\subseteq H\setminus F\) using the correct independent locus bits and leaves every other hybrid naturally independent,

\[
\mathcal L(\text{sampled ancestral history}_{\mathrm{controlled\ ind},a})
=\mathcal L(\text{sampled ancestral history}_{\mathrm{com},a})
\quad\Longleftrightarrow\quad M\subseteq S.
\]

Therefore \(M\) is the unique inclusion-minimal set of additional synchronization sites for exact full-history emulation. Ordinary partial forcing without additional synchronization agrees with the corresponding common-inheritance row's full-history law if and only if every unfixed hybrid has \(d_h\le 1\).

Sufficiency is the coupling above. To prove necessity, take \(h\in M\setminus S\). Removing its child cut-edge separates its descendant component from the root component. Every ancestral path from a sampled descendant copy must leave this component through that edge and hence through \(h\). Other fixed row choices or shared control settings cannot make these copies bypass the bridge. A backward lineage does not split and cannot revisit a node in the DAG.

Let \(E_h\) be the event that no sampled descendant lineages coalesce anywhere below \(h\). It has strictly positive probability for every choice of prepared controllers and inheritance random seeds specifying the no-coalescence descendant paths below \(h\). One can prepare a natural inheritance seed for each possible lineage-label block at each hybrid, independently of coalescent randomness; on a no-coalescence trajectory only the singleton-copy seeds are used. Thus this conditioning does not itself prescribe or reveal a merger. If \(\ell_e\) is the edge's finite duration in coalescent units and \(E_{\downarrow h}\) is the finite edge set in the descendant component together with the child cut-edge, the trajectory's integrated coalescence hazard is at most

\[
\binom{d_h}{2}\sum_{e\in E_{\downarrow h}}\ell_e<\infty.
\]

Consequently, conditional on any such prepared choices, its no-coalescence probability is at least

\[
c_h=\exp\!\left[-\binom{d_h}{2}\sum_{e\in E_{\downarrow h}}\ell_e\right]>0.
\]

This loose bound is enough. Chronological interleaving among finite population edges does not invalidate it: at most \(d_h\) descendant lineages are present, each population contributes only its finite integrated duration, and a DAG gives only finitely many transitions. No no-coalescence condition is imposed on an infinite ancestral root population above \(h\).

On \(E_h\), exactly \(d_h\) distinct descendant lineages make parent choices at \(h\). Their natural choices there are independent of the history strictly below \(h\), of other hybrids' choices, and of the externally prepared controls. Thus the controlled independent experiment has mixed-parent routing probability at least

\[
c_h\big[1-\gamma_h^{d_h}-(1-\gamma_h)^{d_h}\big]>0.
\]

The common-inheritance experiment has mixed-parent routing probability zero at \(h\). This measurable full-history event separates the two laws, proving necessity. It is unnecessary to condition on any particular private choice at another hybrid: the bridge property and positive no-coalescence bound hold for every such assignment. Interior inheritance is essential to this necessity statement; a naturally deterministic parent weight would already synchronize choices without an actuator. Finite durations are essential to the stated no-coalescence argument; a hypothetical infinite bottleneck could force coalescence first.

This exact minimality conclusion is for full ancestral history in this admitted graph class. It is not a necessity or minimality theorem for observed gene-tree topology, metric or ranked marginals, or for a support-recovery objective. Marginalization can erase routing distinctions. Outside the child-cut-edge class, descendant-copy counting remains a sufficient compiler rule but is not asserted to be graphwise minimal, because other row choices can route copies away from a hybrid.

The independent anomalous triangle is an explicit obstruction to the stronger universal claim about observable support. In the report's quartet fixture, the arcs are \(R\to D,U\), \(U\to V,H\), \(V\to C,H\), \(H\to W\), and \(W\to A,B\). Its sole displayed unrooted quartet is \(AB\mid CD\). With the report's positive finite parameters, that quartet's independent CF is \(59/200<1/3\), whereas its common-inheritance CF is \(23/50>1/3\). An unforced unsynchronized hybrid supporting that triangle prevents a universal transfer of the common min-CF provider by ordinary partial controls alone. The fixture can also be included in a larger network.

Fully forced rows are a separate valid baseline. Once every hybrid parent is deterministic, independent and common inheritance agree automatically and both reduce to the appropriate displayed-tree population process. That observation is already available without the randomized compilation. Historical novelty of correlated inheritance or of fully forced tree rows is not claimed.

## Statistical transfer and costs

An exact law equality transfers every existing common-inheritance statistical guarantee whose assumptions are otherwise satisfied by the controlled observations. In particular, the existing robust CF provider with uniform margin

\[
\Delta=g(1-e^{-\tau})
\]

and its conservative noise gates

\[
\varepsilon<\Delta/4
\quad\text{(TV)},\qquad
\eta<\Delta/(\Delta+2)
\quad\text{(Huber)}
\]

can be used after compilation, with the same sampling and provider hypotheses. These are inherited provider bounds, not new consequences of coupling alone. The lower bound \(g\) applies to both parental weights of relevant unfixed random sites; \(\tau\) and all other structural assumptions remain those of the provider. Exact equality transfers sample complexity and success probability immediately. For noise, the specified perturbation model must be applied to the same controlled row law; equality does not make arbitrary experimental noise harmless.

If a row fixes \(f\) hybrids and synchronizes \(k\) additional unfixed hybrids, it actuates \(f+k\le r\) sites per locus. The graph-free program has \(k=r-f\), so it actuates all \(r\) sites per locus. The fixed bits are constant within the row; the \(k\) remaining bits vary independently from locus to locus.

A nominal design with \(2r-2\) rows or \(O(\log r)\) rows counts intervention programs or mixture laws. A single independent-bit exact-emulation program can have \(2^k\) distinct deterministic completions when all synchronized weights are nondegenerate. This is an exponential possible setting repertoire, not automatically an exponential number of loci or an obligation to enumerate or cover every setting. A marginal-law sample theorem can use the original number of independent loci per program. The implementation still pays the additional per-locus actuation cost, and any equipment that requires one preconfigured deterministic setting per completion may have a different cost accounting. The support-only corollary below uses a different joint switch law and reduces this actuator repertoire to at most two settings per program.

The graph-free worst-case additional synchronization count \(r-f\) is sharp for this full-history objective. In the admitted multigraph class, stack \(r\) binary bigons above an \(A,B\) clade, with the root's other branch carrying \(C,D\). Every hybrid then has at least the two sampled descendant copies \(A,B\), every hybrid child edge is a cut-edge, and all edge durations may be finite and positive. Every unfixed hybrid lies in \(M\). If the particular network definition excludes parallel-edge bigons, the same worst-case count is obtained by a simple-graph chain of triangles, each with its own side leaf and all lying above the \(A,B\) clade; this version uses additional sampled taxa. The bigon version should only be stated with a network definition that admits it.

## Recommended theorem wording

“Assuming locus-wide parent-forcing controls and unchanged conditional population dynamics, independent inheritance can implement each common-inheritance intervention row exactly by independently sampling and synchronizing every unfixed hybrid with at least two sampled descendant copies. In the child-cut-edge class with finite edge durations and interior natural inheritance, this is the unique inclusion-minimal synchronization set for equality of the complete sampled ancestral routing/coalescence history laws. Synchronizing all unfixed hybrids is a graph-free implementation, with a sharp worst-case additional site count of \(r-f\). Therefore the established common-inheritance robust support and statistical guarantees apply to these controlled data. This modifies the passive independent-inheritance law and may require all original hybrid sites to be actuated per locus. Full-history minimality does not imply minimality for observed gene-tree marginals or support recovery, and nominal intervention-program counts do not bound the number of deterministic actuator settings.”

## Support-only corollary: one shared coin and two actuator settings

There is a stronger implementation conclusion when the objective is the existing robust min-CF support provider, rather than emulation of the original common-inheritance distribution. Independence between hybrid switches is unnecessary for that provider once its partial pair-hitting menu leaves at most one required certificate choice free.

This corollary retains the unrooted quartet provider's structural hypotheses, including its sufficient one- or two-literal certificates, the relevant internal-length lower bound \(\tau\), and the missing-resolution property used to identify the min-CF baseline. It applies to arbitrary finite taxon sets satisfying those hypotheses. It does not establish a new certificate theorem from the child-cut-edge assumption alone.

For each row, permit any joint distribution \(\mu_a\) of its free hybrid bits, independent of the coalescent randomness, provided that both parental marginals at every free site are at least \(g\). Bits may be arbitrarily correlated between hybrids. Fixed row values are interventions that override the corresponding bits. The marginal floor is required under the intervened row law; conditioning a correlated vector on a fixed bit can destroy that floor and is not the same operation.

All lineages at a hybrid must still use that hybrid's single locus bit. Leaving a hybrid with at most one sampled descendant copy naturally independent provides such a bit on its sole possible use; it can be represented by an independent pre-generated bit. As before, lineages must have the same conditional population dynamics. Site correlation is permitted, but dependence between the prepared switch vector and coalescent event randomness is not.

### Conditional-tree mixture proof

Fix a sampled quartet and a row. Given its complete global switch vector \(b\), the sampled genealogy has the displayed-tree MSC law. Let \(j(b)\) be that tree's restricted unrooted quartet resolution and let \(\ell(b)\) be its internal quartet length. Its CF for resolution \(i\) is

\[
\operatorname{CF}_i(b)
=\frac13e^{-\ell(b)}
+\mathbf 1\{j(b)=i\}\big(1-e^{-\ell(b)}\big).
\]

Integrating against any switch law \(\mu_a\) gives

\[
\operatorname{CF}_i(a)=\beta_a+R_i(a),
\qquad
\beta_a=\frac13\mathbb E_{\mu_a}e^{-\ell(B)},
\qquad
R_i(a)=\mathbb E_{\mu_a}
\left[\mathbf 1\{j(B)=i\}\big(1-e^{-\ell(B)}\big)\right].
\]

No independence between components of \(B\) appears in this identity. If the provider's row has a missing quartet resolution, then that resolution has \(R=0\); all resolutions have \(R\ge0\). Therefore its min-CF baseline is \(\beta_a\) and its excess score is exactly \(R_i(a)\). Changing the joint switch law can remove conditional displayed trees but cannot create ones outside the row's original displayed-tree set, so the inherited missing-resolution premise is preserved. More generally, one must retain the premise of the existing provider that makes the chosen baseline valid; the mixture identity alone does not imply that every arbitrary row has a missing resolution.

For each present target resolution, suppose the existing certificate theorem supplies a sufficient cylinder event \(C\), involving at most two hybrid literals, such that every full switch vector satisfying \(C\) displays the target with \(\ell(B)\ge\tau\). “Sufficient” means that all unmentioned switches may be arbitrary. Choose a covering row compatible with every literal of \(C\), fixing at least one literal when \(C\) has two. A row that fixes one literal correctly but fixes another required literal incorrectly is not a covering row.

Under this row, at most one literal of \(C\) remains free. If none remains free, \(\mu_a(C)=1\). If one remains free, the parental marginal floor gives \(\mu_a(C)\ge g\), regardless of correlation with any other free switch. A one-literal certificate is handled in the same way. Consequently, in the covering row,

\[
R_i(a)\ge \mu_a(C)(1-e^{-\tau})
\ge g(1-e^{-\tau})=\Delta.
\]

An absent target has \(R_i(a)=0\) in every row. Thus the existing “present in at least one row with gap \(\Delta\); absent in every row” guarantee survives arbitrary within-locus site correlation. The same cross-row maximum of min-CF excesses can be used. The argument is quartet-local but applies simultaneously to every quartet in an arbitrary finite admitted taxon set.

The covering condition is essential: parental marginal floors alone give no positive lower bound for a conjunction of two free literals. For example, if \(B_1=B_2\) is a fair coin, the event \(B_1=0,B_2=1\) has probability zero even though both parental marginals are \(1/2\). The corollary makes no analogous claim for a passive row, for a certificate leaving two free required choices, or for a witness that is not a sufficient cylinder event.

### Selective one-coin implementation

In every fresh locus of a nominal row, draw one fair coin \(Z\), independently of all coalescent randomness, natural inheritance choices, and the coins of other loci. At each unfixed hybrid with at least two sampled descendant copies, force every lineage to parent

\[
B_h=Z\mathbin{\mathrm{xor}}\sigma_h,
\]

where \(\sigma_h\) is any fixed orientation bit. Keep the row's fixed hybrids forced as prescribed. Leave hybrids with at most one sampled descendant copy naturally independent, assuming their two natural parental weights are at least \(g\).

Each synchronized free site now has parental marginals \(1/2\), and each natural singleton site retains its marginal floor. Hence all required free marginals are at least \(g\), for \(g\le1/2\). There is one shared parent choice at every hybrid encountered by more than one lineage, so the conditional-tree mixture applies. The support gap remains \(\Delta=g(1-e^{-\tau})\).

This program uses one external random bit per locus and at most two deterministic actuator configurations per nominal row: the fixed settings plus the synchronized-site vector for \(Z=0\), or the fixed settings plus its complement for \(Z=1\). If there are no additional synchronized sites, only one actuator configuration is needed. The number of actuated sites remains \(f+k\); this improvement changes neither that count nor the requirement to force all relevant lineages. In the graph-free version, synchronize all unfixed sites with the same coin, so all \(r\) sites are actuated and there are still at most two actuator configurations per nominal row.

For the selective version, unsynchronized singleton sites can produce additional natural global switch vectors. Thus “two configurations” counts the externally set actuator vectors, not all underlying routing vectors, displayed trees, or possible gene trees.

This shared-coin program generally does not match the original target common-inheritance full-history or full gene-tree law: it changes free-site weights to \(1/2\) and correlates sites. Its conclusion is the preserved support-provider guarantee. A guarantee about original weights, the complete gene law, or another statistic must be proved separately or use the independent-bit exact compiler.

### Robust cross-row and finite-sample guarantees

Let \(S_i(a)=\operatorname{CF}_i(a)-\min_j\operatorname{CF}_j(a)\), with the inherited baseline assumptions above, and use \(\max_a S_i(a)\) across rows. An absent target has ideal score zero in all rows; a present target has ideal score at least \(\Delta\) in a covering row.

Under per-row TV noise at most \(\varepsilon\), every CF changes by at most \(\varepsilon\), and each excess score changes by at most \(2\varepsilon\). Hence absent scores are at most \(2\varepsilon\), while a present score is at least \(\Delta-2\varepsilon\) in its covering row. These remain separated whenever \(\varepsilon<\Delta/4\).

Under per-row Huber contamination \(Q_a=(1-\eta)P_a+\eta R_a\), an absent target's score is at most \(\eta\). A present target's covering-row score is at least \((1-\eta)\Delta-\eta\). To see the latter, evaluate the noisy minimum against an ideal missing resolution, whose ideal CF equals the baseline. The two populations are separated whenever

\[
(1-\eta)\Delta-2\eta>0
\quad\Longleftrightarrow\quad
\eta<\frac{\Delta}{\Delta+2}.
\]

These bounds hold row by row with arbitrary row-specific contaminating distributions. Taking a maximum preserves the “present in one row; absent in every row” separation.

Fresh independent loci are still required for the existing concentration guarantees. Within-locus site dependence does not impair concentration of the gene-tree indicators across loci. For example, with \(L\) rows, \(n\) taxa, and \(m\) independent loci per row, Hoeffding plus a union bound over the three resolutions of all unrooted quartets gives

\[
\Pr\!\left\{\max_{a,i,\text{quartet}}
|\widehat{\operatorname{CF}}_i(a)-\operatorname{CF}_i(a)|>\delta\right\}
\le 6L\binom n4 e^{-2m\delta^2}.
\]

No independence among quartet restrictions within a locus is used. On this event's complement, excess-score errors are at most \(2\delta\). Therefore TV separation follows from \(\varepsilon+\delta<\Delta/4\), and Huber separation follows from \(4\delta<(1-\eta)\Delta-2\eta\). This yields the same provider-style sample scaling and robustness gates, without an independence assumption between hybrid switches.

The existing menu can be reused; its count should not be declared optimal among these enlarged correlated support-only protocols. Correlated schedules may permit different menus, and any lower bound proved for the original parameter-oblivious ternary-menu class needs its original scope. Fully fixed covering arrays remain a stronger prior baseline when their additional forcing burden is acceptable. The trivial \(r=0\) and \(r=1\) menu cases must use their separate existing conventions rather than blindly evaluating a \(2r-2\) formula. No historical novelty is claimed for correlated inheritance or fully forced rows.

## Final audit of REPORT.md Sections 4.2–4.6 and 5

Reviewed the actual report at `/workspace/scratch/c82ede027ea7/research/2026-09-30-independent-control-1810z/REPORT.md`, including its Section 3 contract. No substantive overclaim was found in the full-history iff/minimal-set result, support-only one-coin result, robust cross-row bounds, control-error TV bound, cost table, or completion register.

* Section 4.2 correctly restricts unique minimality to persistent site synchronization and full sampled routing/coalescence histories. Its child-bridge argument is unaffected by other row settings. The finite below-h hazard argument gives positive probability, and interior natural weights make mixed routing a separating history event. The admitted bigon construction legitimately establishes the fixed-four-taxon worst case. It does not claim a support-only lower bound.
* Section 4.3 correctly separates exact original-weight compilation from the passive independent law and from more general biological interventions. The finite-size statement is governed by the declared model contract.
* Section 4.4 explicitly carries the essential sufficient-cylinder, compatible-covering-row, missing-resolution, and length-floor hypotheses. The conditional switching mixture formula and one-free-literal bound do not use site independence. The report correctly distinguishes two actuator vectors from potentially many natural routing vectors and declines to import old count-optimality claims into the enlarged protocol class.
* Section 4.5's TV and Huber score bounds and gates are correct. The actuator extension is the standard coupling inequality followed by the triangle inequality; gene-dependent failure need not be Huber contamination. Its union bound does not require independent failures. The completion register treats scientific floors and actuator calibration as outstanding premises rather than measured facts.
* Section 4.6 accurately separates random draws, forced-site count, repertoire, and sample counts. Exact compilation can have exponentially many possible actuator settings without requiring their enumeration; the support-only compiler has at most two settings without reducing site actuation. Original IDs and response-family preservation remain necessary for a controlled normalizer.

Two explicit clarifications would remove minor ambiguity if the report is revised. First, the external shared coin and all prepared inheritance bits used in the ideal conditional-switching proof must be independent of coalescent randomness; in the one-coin protocol the coin should also be independent of natural singleton choices. This is intended by the construction, but “fresh fair bit” alone does not logically state the within-locus independence needed to conclude that conditioning on the switching leaves a tree MSC. Arbitrary correlation is allowed between site bits, not between their prepared vector and merger randomness. Second, a per-site failure quantity \(\nu_{eh}\) must bound any relevant failure at that site during the whole locus, rather than just one lineage's actuation attempt; otherwise the sum over sites omits repeated attempts. The existing whole-locus coupling premise is already correct.

These are clarifications of the ideal randomization/failure-event contract, not flaws in the displayed proofs. No report or code edits were made in this final audit.
