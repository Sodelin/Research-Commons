# Statistical recovery with systematic error: general criterion and executable support certificates

ID: ROBUST-STAT-20260930-1620Z. Contributor/publisher: Codex Work, with attributed internal proof and implementation reviewers. Nolan selected statistical recovery and explicitly requested the general problem rather than stopping at a concrete special case. Accepted standard: MASTER-CLOSURE-STANDARD-20260930.

**Status:** hand-derived general characterization for a declared finite observation experiment; robust complete-support component with executable rational certificates; biological omnibus master in progress. No historical novelty, formal verification, or physical intervention validation is claimed.

## 0. Full question and obligations

The promised biological endpoint remains BOTH the complete nontrivial displayed split union and a compatible circular order, for every finite admitted binary semi-directed LSA-rootable outer-labeled planar galled network, including arbitrary finite levels/blob counts and the established parallel-edge/bigon convention. One sample per taxon, NMSCcom and NMSCind, passive and controlled observations, and freely varying positive parameters must be distinguished. Uniform finite recovery is a possible/impossible classification, not an assumed positive result.

This packet answers the statistical interface whenever a justified observation class or support-gap provider is available. It does not classify the biological observation classes itself. A fresh consequential-peer read at Commons `e6a308d34da104b362826885ae28da409e852a0a` found Astra's [submitted normal-form/global-image result](../2026-09-30-astra-bio-prover-1612z/README.md), published at `567def4fe7f22fee00350c0e83bd285f66b75522`. Its all-size proof and finite decision construction are submitted, not independently accepted; the full catalogue, complete QE integration and explicit whole-space stratification were not executed. Section 8 gives the resulting statistical interface.

A final consequential read at `9ffb185e27dc2f057f4a9a2a32a927cecb6855f7` found Astra's [later certification packet](../2026-09-30-astra-certification-1701z/README.md), pinned at `20c7370176918b9a605e6cde9ef73cc4952f7d12`. It adds a runnable guarded algebraic/global image frontend and a conditional robust-fiber characterization. This supersedes the earlier implementation-missing description for those supplied pieces. Its normal-form/local-image proofs and every-tree extension still require independent review, and no unrestricted all-n catalogue was executed. Our controlled-provider sharp noise threshold and exact rational feasible-law implementation are complementary; passive certification retains that owner's attribution.

| Obligation | Evidence | Status and next action |
|---|---|---|
| General finite-experiment statistical recovery | Section 2: positive separation iff bounded-budget uniform recovery above chance | Hand proof internally challenged; effective law access separate |
| Robust complete quartet support | Sections 3–6; robust_support.py and law_feasibility.py | Conditional component; error/gap premises must be certified |
| Full split/order output | Section 7; pinned actual joint decoder in checks.json | General composition conditional on inherited exact decoder/source theorem; finite replay checks implementation |
| Biological passive model images and globally compatible ambiguity | Astra submitted NF and later certification packets; Section 8 interface | Guarded backend delivered conditionally; source-critical review and unrestricted global computations outstanding |
| Controlled NMSCind law | No provider supplied | Open; common-switch mixture cannot be substituted |
| Normalization, physical controls, error calibration | Sections 8–9 | Conditional contracts; no empirical validation |
| Publication, independent scrutiny, prior | Reviews, hashes, primary bibliography | Internal review only; canonical/formal promotion remains separate |

## 1. Governing prior and contribution boundary

Classical concentration, experiment comparison, contamination neighborhoods and confidence sequences supply the mathematics. The already delivered [general-transfer audit](../2026-09-30-general-transfer-audit/README.md) and [compact certificate](../2026-09-30-general-transfer-closure/compact-certificate.md) are reused, not superseded. The earlier [statistical bridge](../2026-09-30-astra-statistical-bridge/README.md) explicitly provides a level-one gap component. The [control-menu pipeline](../2026-09-30-control-menu-continuation/PIPELINE-THEOREM.md) supplies the conditional all-level NMSCcom provider and fixed-transcript composition.

Primary prior inspected: Hoeffding (1963), DOI 10.1080/01621459.1963.10500830; Howard–Ramdas–McAuliffe–Sekhon (2021), DOI 10.1214/20-AOS1991; Wang–Ramdas (2023), PMLR 206:9662–9679. The latter develops substantially more sophisticated robust confidence sequences. Our elementary summable-error construction is conservative, not a claim of optimal sequential width. Read original paper metadata/abstracts and the available Hoeffding PDF; do not imply full replication of those papers.

The contribution here is a source-scoped robustness bridge, its necessity controls, and exact feasible-law inference/composition. Clinical evidence grading and meta-analysis do not apply to these mathematical claims. Their evidence is proof, source admission, independent internal criticism, and finite implementation checks.

## 2. General recovery criterion, including negative regimes

Fix a common known finite menu of m environments and a k-category observation alphabet. The declared target has a finite nonempty set Z of mutually exclusive answers. For fixed taxon count, the complete split union is such a target; a canonical compatible order can be computed from it. A negative theorem for a task allowing ANY compatible order must distinguish incompatible valid-output sets, not merely different arbitrarily selected orders. For each z let R_z be the nonempty set of all observed probability arrays permitted by source states with answer z, including the allowed systematic errors. Their coordinate and environment labels must mean the same thing across hypotheses.

For the positive theorem, stationary categorical row laws and IID observations within each fixed row stream suffice; dependence between row sample blocks is harmless. For the negative theorem and the stated iff, the declared experiment must additionally consist of fresh conditional draws from the chosen fixed row law given the ENTIRE past. Otherwise encode the whole joint observable law rather than only marginal row arrays. Correlations can themselves carry target information: two Bernoulli(1/2) row streams with equal paired bits versus opposite paired bits have identical marginals but distinguishable joint data. The same caution applies to full gene-tree laws versus marginal quartet CFs. Define

```math
h=\inf_{z\ne z'}\inf_{r\in R_z,s\in R_{z'}}
\max_{e,t}|r_{e,t}-s_{e,t}|.
```

If |Z|=1 no observations are needed. Otherwise:

**Positive theorem.** If h>0, choose the answer minimizing d_z(rhat)=inf_{r in R_z} ||rhat-r||_infinity, with a fixed tie rule. Infima need not be attained. The distance functions are Lipschitz and measurable, and the finite answer minimizer exists. With N IID loci per environment,

```math
N\ge\left\lceil\frac{2}{h^2}\log\frac{2mk}{\delta}\right\rceil
```

gives uniformly correct recovery with probability at least 1−delta. Indeed the empirical array is within h/2 of its true law except with probability at most 2mk exp(−Nh²/2). On the strict good event the true-answer distance is <h/2 and every other distance is >h/2. This is an existence theorem until the relevant distances can be computed or certified to sufficient precision. A normalization/model-image algorithm must discharge that obligation; a definition of R_z alone does not.

**Bounded-budget necessity.** If h=0, every procedure with a hard cap of M observations fails to have uniform success 1/2+gamma for any gamma>0. Choose differing-target row arrays with coordinate distance a arbitrarily small. Each row's TV distance is at most ka/2. Couple successive fresh observations while histories agree, including the procedure's random seed and predictable adaptive choice of environments. Transcript TV is at most Mka/2. The two-point testing inequality makes at least one error probability at least (1−Mka/2)/2. Let a tend to zero. This includes arbitrary computation and adaptive row selection within the common fixed menu. With zero cap the same conclusion follows immediately.

**Unlimited-data impossibility.** If actual R_z sets intersect, two answers have exactly the same observed row laws; neither unlimited sampling nor a representation change can distinguish them. Touching closures with disjoint sets is weaker: it excludes uniform bounded-budget recovery but can permit pointwise recovery with source-dependent unbounded sample sizes. Do not conflate these statements.

Thus positive separation characterizes arbitrarily accurate uniform recovery with bounded sample budgets in this declared finite experiment. It does not assert finite expected-time optimality, practical access, infinite-alphabet completeness, or effective membership in arbitrary biological model images. Earlier general-transfer work handles broader experiment-comparison frameworks.

## 3. Robust contrast provider: all rows, all admitted sizes

For every quartet q let p_e(q) be its ideal three-category law and C_t=max_e(p_et−min_j p_ej). The provider contract is: an absent displayed topology has C_t=0, and a present topology has C_t>=Delta, where 0<Delta<=1 is a certified uniform floor. The complete legal mask is in a declared finite set (default 1..6 for at most two displayed quartet topologies). These assumptions are separate from concentration.

If TV(r_e,p_e)<=epsilon_e, each coordinate moves by at most epsilon_e, and each contrast by at most 2epsilon_e. For an absent coordinate observed contrast D_et<=a_e=2epsilon_e; a present topology has a witnessing row with D_et>=b_e=Delta−2epsilon_e.

For homogeneous epsilon, d=Delta−4epsilon>0 is a sufficient margin. Estimate row coordinates and threshold the maximum empirical contrast at Delta/2. For ANY deterministic exact-support decoder using at most B queries on promised ideal transcripts,

```math
N\ge\left\lceil\frac8{(\Delta-4\epsilon)^2}
\log\frac{6mB}{\delta}\right\rceil
```

suffices. Coordinate errors <d/4 imply contrast errors <d/2; absence remains below the threshold and presence above it. More loci cannot remove epsilon.

**Huber distinction.** Under r_e=(1−eta_e)p_e+eta_e u_e for an arbitrary simplex u_e, absence has D_et<=eta_e and presence somewhere has D_et>=(1−eta_e)Delta−eta_e. For homogeneous eta use d_H=(1−eta)Delta−2eta>0 and threshold (1−eta)Delta/2 in the same formula. This stronger budget requires the actual clean-mixture contract. A topology-dependent calling error rate or an arbitrary coupling mismatch supplies TV, not automatically a Huber mixture.

The heterogeneous certificate uses rowwise a_e,b_e. It asserts presence when one row's contrast lower bound exceeds a_e; absence when every row's contrast upper bound is below b_e. Conflicting conclusions yield MODEL_INCOMPATIBLE. Insufficient information yields INCONCLUSIVE. Empty or ambiguous candidates never become an arbitrary tree.

## 4. Exact abstract noise boundary: beyond simple thresholding

The preceding margin is sufficient, and often sharp, but the legal support constraints can improve it. Define the ABSTRACT provider class: arbitrary arrays of three-category simplex rows, nonempty global masks of size at most two, zero contrast in every row for absent coordinates, and maximum contrast >=Delta for every present coordinate. No claim that every array is biologically realizable is made.

For this entire class, observed through fresh categorical row draws with no extra target-specific correlation channel, the minimum distance between different masks in max_e TV is exactly

```math
H_m(\Delta)=
\begin{cases}
\max\{\Delta/2,(4\Delta-1)/3\},&m=1,\ 0<\Delta\le1/2,\\
\Delta,&m=1,\ 1/2<\Delta\le1,\\
\max\{\Delta/2,\Delta-1/3\},&m\ge2.
\end{cases}
```

**Lower proof.** Any differing masks have a coordinate absent in one and present in the other. Its contrast changes by >=Delta in a witnessing row, implying TV>=Delta/2. An absent coordinate is at most 1/3 and a witnessing coordinate at least Delta, giving TV>=Delta−1/3. If m=1, every supported coordinate has contrast >=Delta in that row; the absent baseline is at most (1−Delta)/3, giving TV>=(4Delta−1)/3. For Delta>1/2 two supported coordinates in one row are impossible. The remaining singleton/singleton comparison has coordinate difference >=Delta, hence TV>=Delta.

**Attainment.** Write b=(1−Delta)/3. For m=1 and Delta<=2/5 compare (b+Delta,b,b) with (b+Delta,b+Delta/2,b−Delta/2). For 2/5<=Delta<=1/2 compare ((1+2Delta)/3,b,b) with (1−Delta,Delta,0). For Delta>1/2 compare the singleton vector with its first two coordinates exchanged. These achieve the displayed formula. For m>=2 share a row ((1+2Delta)/3,(1−Delta)/3,(1−Delta)/3) witnessing the first coordinate. In the second row compare the uniform vector with (1/3,1/3+Delta/2,1/3−Delta/2) if Delta<=2/3, or with (1−Delta,Delta,0) otherwise. Additional rows can be common copies. These achieve H_m and obey the target masks {1} and {1,2}.

In a three-category simplex TV(p,r)=max_i|p_i−r_i|: since the differences sum to zero, one sign has at most one nonzero coordinate and its magnitude is the sum on the other sign. This identity is specific to three categories.

**Exact homogeneous contamination threshold.** For this compact abstract class, uniform finite recovery is possible iff

```math
\epsilon<H_m(\Delta)/2\quad\text{(TV)},
\qquad\eta<H_m(\Delta)/(1+H_m(\Delta))\quad\text{(Huber)}.
```

At and above the boundary different masks admit identical observed row laws. TV balls intersect exactly when distance<=2epsilon, with a midpoint witnessing sufficiency. Huber neighborhoods intersect exactly when (1−eta)(1+TV)<=1: a common law must dominate (1−eta)max(p_i,r_i), whose sum is (1−eta)(1+TV), and that condition also constructs one. Apply independently in every row to the attained clean pair. Below the boundary robust class separation is at least H_m−2epsilon or (1−eta)H_m−eta, respectively, so Section 2 gives finite recovery. This is exact for the abstract provider class; richer scientific constraints/side information can change the boundary.

## 5. Executable whole-class feasible-law certificates

law_feasibility.py implements the abstract class rather than merely a contrast threshold. At each row construct a conservative rational confidence box [l_i,u_i] for its observed law. A candidate global mask survives iff there exist ideal simplex rows and observed rows in those boxes satisfying the noise contract, zero absent contrasts, and witnesses for every supported coordinate. It checks every legal mask and returns a unique one only when justified.

Feasibility is exact rational arithmetic in two free ideal coordinates. For TV, |p_i−r_i|<=epsilon is equivalent to TV<=epsilon here. Eliminate r by requiring p_i in [l_i−epsilon,u_i+epsilon] and, for every coordinate subset S,

```math
\sum_{i\in S}p_i\le1-\sum_{i\notin S}l_i+|S|\epsilon,
\quad
\sum_{i\in S}p_i\ge1-\sum_{i\notin S}u_i-|S|\epsilon.
```

These are precisely sum_i max(l_i,p_i−epsilon)<=1 and sum_i min(u_i,p_i+epsilon)>=1, together with nonempty coordinate intervals. For Huber, require (1−eta)p_i<=u_i and all subset inequalities (1−eta)sum_{i in S}p_i<=1−sum_{i notin S}l_i. They express existence of an r dominating (1−eta)p within the box; remaining mass constructs the contaminant. Empty/inconsistent boxes are rejected.

An absent t adds p_t<=p_j for every j. A witness adds p_t−p_j>=Delta for one comparator j. Enumerate comparator choices and row witness subsets; a tiny union-of-subsets dynamic program checks that their union covers the candidate global mask. Every nonempty compact two-dimensional feasible polytope has a vertex; exact intersections of constraint pairs provide a finite decision procedure. The returned rational p/r witnesses can be independently checked. This solves the ABSTRACT image-membership obligation, not Astra's tighter biological source image.

On the simultaneous confidence event the true mask survives. When the robust classes have positive separation and every row prefix grows, boxes shrink and every incorrect mask is eventually excluded. The three-category identity gives uniqueness once the conservative coordinate box radius is less than half the robust separation. No optimal sample-cost or runtime claim is made; rational bit complexity and m matter.

## 6. Valid monitoring and adaptive sampling

For every fixed ideal-transcript quartet, row e, coordinate t, and UNIQUE within-row prefix length k>=1, allocate failure probability delta/[3mB k(k+1)]. The elementary radius is

```math
a_k=\sqrt{\frac{\log(6mB k(k+1)/\delta)}{2k}}.
```

The two-sided Hoeffding upper bound equals the allocated probability; summing over k telescopes to one, and over 3mB streams gives delta. Thus repeated examination and data-dependent stopping at prefixes are covered. Independence between quartets is unnecessary. Rows must belong to the declared fixed menu; adaptively introducing new environments is outside this allocation.

Both implementations conservatively replace ln(x) by c=ceil(log2 x), giving exact radius squared c/(2k). robust_support.py compares squared rational distances and never relies on floating log/sqrt. law_feasibility.py rounds the square root upwards rationally; its rounding error tends to zero. Fixed-time mode omits k(k+1) and must use the declared sample lengths fixed before inspecting data.

Predictably choosing the next row is valid with fresh draws. A stronger conditional mean drift promise also works: for a fixed ideal p_e, every fresh sample's conditional categorical mean lies in its convex TV/Huber neighborhood. Bernoulli conditional log-MGF <=lambda²/8 gives the same concentration around average conditional means, which remain in that neighborhood. This extension does not automatically preserve tighter graph-coupled nuisance restrictions in Section 2.

Reused data are fixed row prefixes of unique loci. Selecting locus indices after observing correlated quartet information, pretending repeated reads are fresh loci, or conditioning a fixed-time interval on optional stopping invalidates the stated sampling guarantee. These are actual contract boundaries, not testable consequences of count arithmetic.

## 7. Whole decoder composition and actual checks

Let A be ANY deterministic exact-complete-support decoder with at most B ideal queries, returning both the true split union and its chosen compatible order. Require termination on bounded transcripts or a computation guard sufficient on every promised ideal run. Run it through GuardedOracle: memoize certified masks, enforce the query cap, and latch INCONCLUSIVE/MODEL_INCOMPATIBLE/input failures so execution cannot continue after abstention.

The true source and A define one deterministic ideal transcript independent of the data. A first incorrect certified mask must occur on this transcript, since every preceding mask was correct. Union-bound the anytime coverage events for its <=B quartets. With probability >=1−delta, every emitted mask is correct. An unresolved certificate aborts the whole decoder. This is unconditional risk control under the stated premises, not a promise to return an answer at every sample size. At a sufficient prefix or in the positive-separation regime with all rows sampled and adequate computation, the same event also guarantees return of the complete correct output. Unbounded waiting and inadequate computation guards must not be called a finite-time recovery algorithm.

checks.py executes the actual pinned [joint order/split decoder](../2026-09-30-astra-exact-query-1156z/recover_all.py), not a substitute decoder. It verifies six unchanged Git blobs and runs 18 contrast-provider combinations of n=4,5,6, r=2,3,4, TV/Huber errors, plus six actual feasible-law-provider decoder runs at r=4, n=4,5,6 under both noise models. Exact analytical NMSCcom mixtures provide coverage-event counts. Full expanded split sets, every queried mask, and compatibility of the returned order are checked against actual switched-tree edge cuts. Insufficient counts abort all 24 actual decoder runs. These are analytical fixtures, not sampled data, coverage-frequency experiments or full-class proofs.

The earlier pipeline's outdated query-review status and normalization-count wording are not inherited blindly: the independent query reviews and normalization correction are documented in the [omnibus refocus](../2026-09-30-omnibus-refocus/REPORT.md). This packet leaves peers' original artifacts intact.

## 8. Normalization and g²-to-g: the exact integration obligation

For the inherited common-inheritance switching provider put zeta=1−exp(−tau). Its certified floor is Delta=gamma*zeta, with gamma=g² for a passive two-choice witness, g for one correctly targeted force, or 1 for certainty coverage. Substitute that floor into the statistical theorems; changing gamma does not change the proof's quantifiers. The simple TV margin is gamma*zeta−4epsilon. Under ideal observations the sufficient sampling factor improves from g^-4 to g^-2 after one correct control. With errors, the improvement only applies when a positive robust separation remains.

An exact passive normal form may preserve passive quartet laws and displayed support, but cannot supply controlled experiments by itself. To transfer this recovery theorem require a KNOWN implementable lift from normalized experiment rows to original control IDs, target preservation, common observation-coordinate labels, a valid replacement gap, and law equality or a certified TV discrepancy rho per row. Add rho to the TV error budget by the triangle inequality; this does not automatically preserve a Huber mixture contract. An existential hidden-state-dependent lift is not an experiment design.

**The newly returned passive bridge.** Astra's PROOFS.md Sections 8–11 submit simultaneous positive CF/Q/S normalization for NMSCind and NMSCcom separately, combine it with the inherited r<=2n−3 count, and give a finite actual-source grammar with a converse. Every candidate target image is a finite union of polynomial maps with strict positive parameter inequalities, tested with ONE shared graph/parameter assignment across all quartets. Conditional on that proof, these are the actual all-original-size CF target images rather than an unbounded definition. The implemented controller retains ALL_ADMITTED_TARGETS when enumeration or solving is incomplete. The full catalogue/general QE backend were not executed. Source-critical acceptance is outstanding.

The statistical continuation can immediately replace Astra's fixed-time box by the all-prefix box in Section 6, taking B=binom(n,4) and one passive environment. With TV error epsilon per quartet, enlarge the empirical coordinate box by epsilon (clamped to [0,1]); it contains the true IDEAL CF vector on the simultaneous event. Alternatively add the exact simplex/noise constraints of Section 5 to every quartet while retaining the single common graph/parameter assignment. A singleton is justified only after all competing images are excluded; incomplete or unknown solver results remain inconclusive. This supplies a conservative robust/anytime passive extension conditional on the submitted normalization theorem. It preserves same-locus quartet dependence in the positive coverage proof and makes no full-joint-law impossibility claim from CFs alone.

cf_confidence.py implements this outward box in the actual peer boxes=True API and guards interpretation of controller outputs. Its source-CF coverage-event fixture, zero-data case and incomplete/contradictory-result controls passed in checks.json. The compiler API was inspected at Git blob 4847e9f104be89d65b0aa41f508a5787036c3d1f. The biological solver/catalogue was not executed in this continuation; the current runtime lacks its NetworkX/SymPy dependencies, and no installation or unrestricted run was needed for these statistical checks.

The later Astra certification packet supplies the passive compactification that should now be reused: closed polynomial parameter cubes retain the SAME interior graph target labels, so their finite union equals each target-image closure. Its robust fiber distinguishes exact uniqueness from stable finite certification; its fresh-locus marginal experiment is explicit, and it does not export CF-only necessity to full joint loci. It also submits an every-positive-tree rare-reticulation obstruction for full rooted metric gene laws. These strengthen the source-specific negative/positive classification beyond our generic interface and require the declared NF/LOCAL or source-construction review. They were read, not independently replayed or accepted here. No passive solver was rewritten to compete with the returned backend.

A parameter-independent observation kernel contracts TV; compression alone cannot create previously missing distinctions. A reverse simulation certificate can establish statistical sufficiency. A deterministic CF normalization dividing by an estimated quantity needs its own denominator floor and stability/concentration theorem; it cannot retain epsilon by declaration. These are the precise interfaces for Astra's biological normal form, not extra claimed results of its passive task.

## 9. Practical control/readout budgets and remaining unknowns

If a coupling shows the observed outcome differs from the ideal one with probability at most kappa, then TV<=kappa. A control mismatch bound kappa_c and readout mismatch bound kappa_r give epsilon<=min(1,kappa_c+kappa_r); independence is not needed for this union bound. A clean-event mixture independent of the ideal gene outcome can justify Huber instead, but outcome-dependent errors need not.

For s forced parental choices with individual failure bounds beta_i, a conservative control bound is sum_i beta_i. Thus three graph-informed environments can still have error costs growing with the number of actuators. Constant row count alone does not certify a practical constant error budget. Bounds learned from calibration require a uniform model/validation guarantee; allocate delta_cal plus delta_stat for a combined guarantee. Neither g nor tau becomes known merely by collecting count vectors.

The full freely positive-parameter biological class usually admits arbitrarily small support gaps. A positive-gap uniform theorem must state its parameter restriction. The generic zero-separation theorem explains why there is no universal fixed finite sample budget in such regimes; earlier biological rare-switch arguments remain provenance. Pointwise or sequential acquisition without a known gap is a separate question, and exact absence need not be finitely certifiable near a boundary.

## 10. An admitted exact systematic-error obstruction

In quartet order (AB|CD, AC|BD, AD|BC), tree A has law p_A=(2/3,1/6,1/6). Give every edge coalescent length ln2; its resolved internal edge also has length ln2.

Network B has directed edges R->D,U; U->V,H; V->A,W; W->B,H; H->C. It is a binary DAG with one gall U-V-W-H-U, all taxa exterior, and a cut edge H-C. R is the leaf-set LSA. Set inheritance weights 3/4 on U->H and 1/4 on W->H; edge U->V has length ln4 and every other edge length ln2. Both switched trees have strictly positive quartet internals. They display AB|CD with internal ln4 and AD|BC with internal ln2, giving p_B=(2/3,5/48,11/48). The tree-MSC formula is (1−2x/3,x/3,x/3), with x=exp(−internal length), placed in the appropriate coordinate.

Their complete supports differ. With g=1/4 and tau=ln2, Delta=1/8; TV(p_A,p_B)=1/16=Delta/2. Their TV neighborhoods share the midpoint at epsilon=1/32=Delta/4. Their Huber neighborhoods share r=(32,8,11)/51 at eta=1/17=Delta/(Delta+2), with contaminants respectively point masses on AD and AC. All IID locus data then have the same law for different supports. No method can recover both with worst-case success >1/2, even with unlimited passive topology observations.

This is actual source-admitted passive four-taxon sharpness. It is not a lower bound for a richer graph-informed menu or side information revealing the network graph/reticulation count. Symbolic versions require all source branch survival values <1; the exact numerical example avoids any missing realizability constraint. Source admission has the direct argument above plus executed degree/DAG and independent four-point CF arithmetic in checks.json.

## 11. Process assessment

Read current Commons admission/workflow/master standard, delivered statistical and general-transfer components, the actual Astra acceptance, and immutable decoder files. Narrow internal reviewers independently challenged the proof and implementation; their corrections are preserved. The full question remains the endpoint. Small fixtures discharge arithmetic/integration obligations and do not imply a general proof. No new enumeration, external chat assignment, formal proof or unattended execution was launched.

## 12. Robustness assessment

The strongest general claim distinguishes observed-law overlap, zero separation and positive separation. The exact abstract noise boundary improves conservative thresholding; its biological applicability still requires an actual provider. More samples resolve sampling uncertainty but cannot average away a fixed observational ambiguity. Unknown physical controls, systematic bias or invalid gap floors are not solved by software.

## 13. Publication and reproducibility

README.md gives commands; manifest.json pins every contributed artifact. Peer decoder snapshots are materialized for execution but remain unchanged in their original repository paths, with Git blob checks. Review receipts distinguish hand proof from finite tests. Publication is preservation, not proof of truth, peer receipt, journal readiness or canonical promotion.

## 14. Next master step

Independently review the NOW returned normal-form and passive certification theorems, then use their guarded global image backend and exact target-labeled closures; do not reassign that implementation as still missing. No unrestricted all-n catalogue was run here. For controlled recovery, require the explicit row lift and law/gap/error certificates in Section 8. Passive proof acceptance/practical global computation, full-joint classification, NMSCind partial controls and empirical practicality remain open. The statistical side has a general interface and executable robust controlled provider to consume the submitted results conditionally.
