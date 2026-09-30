# 0. Executive decision brief

**The next omnibus component is a finite-data certification boundary, not another review of the biological replacement proof.** This packet gives a conditional all-size construction for computing both exact CF-compatible targets and their limiting competitors, and proves when the latter permit uniformly honest finite certification in a precisely stated CF sampling experiment. It also extends the inherited rare-reticulation obstruction from one quartet fixture to **every positive binary species tree on every n >= 4**.

Contributor/publisher: GPT-6 Astra Pro. Session: **ASTRA-CERTIFICATION-20260930-1701Z**. Date: 2026-09-30. Governing standard: MASTER-CLOSURE-STANDARD-20260930. Acceptance: Commons commit `e6a308d34da104b362826885ae28da409e852a0a`. Nolan directed this downstream continuation while another researcher checks the biological normal form. No takeover of that review or assertion of live peer presence is made.

Evidence band: **authored mathematical proofs and exact computational controls; independent review pending**. All-size image results depend on the submitted 1612Z normal form. The all-tree rare-reticulation construction does not depend on that normal form. The explicit four-taxon classification depends on ASTRA-OBS's local image lemmas, which remain attributed and subject to review.

The highest-leverage results are:

1. For each target, its CF-image closure is the image of the **closed parameter cubes of the same labeled graphs**. This reduces closure membership to the existing kind of existential polynomial feasibility problem, with no universal epsilon quantifier. Boundary graphs must not be silently retargeted.
2. A shrinking, simultaneous, all-prefix confidence construction eventually retains exactly the robust target fiber on its coverage event. It certifies a full answer precisely when that fiber is a singleton, under the CF sampling contract below. It also supports certified partial splits and correctly associated candidate order spaces.
3. Every admitted binary tree has arbitrarily close, differently targeted, one-reticulation competitors. A uniformly honest procedure has probability at most delta of issuing a correct terminal tree certificate at any finite time at such a tree. The argument covers full rooted metric genealogies, not just CFs, under the stated one-copy/free-demography contract.
4. The complete four-taxon robust classification distinguishes an exact equality boundary previously hidden by a positive-gap statement: under NMSCind, at `(1/6,5/12,5/12)` the exact target is unique but a different target is arbitrarily close. The robust singleton regime on this symmetry line requires **strictly less than 1/6**.
5. Executed checks include 1,368 exact solver/grid comparisons, 123 admitted tree/reticulation pairs with 3,306 mechanism-specific CF equalities, 1,653 separate switched-tree formula comparisons, algebraic-input and shared-parameter controls, and timeout/unknown/incomplete-catalogue guards.

**Status:** the CF-certification component is characterized conditionally at written-proof level and has an implemented guarded backend and complete conditional n=4 image frontend. The complete all-n catalogue has not been executed. Full joint n-gene classification, control-aware inference, source formalization and canonical promotion are not closed.

# Exact answers, limiting competitors, and finite biological certification

## 1. Abstract

Exact identifiability does not imply that a finite sample can support an honest terminal certificate uniformly over the admitted model class. We exploit the previously submitted source-specific finite polynomial normal form to compute the closures of target-labeled quartet concordance-factor images. We prove a compactification identity, an effective robust-fiber construction, and a confidence-sequence inversion whose limiting candidate set is the robust fiber. Necessity is proved for an explicitly CF-determined sampling experiment; a separate source construction supplies a stronger full-genealogy obstruction at every binary tree. An exact six-image four-taxon implementation resolves the endpoint at 1/6 and illustrates why labels at degenerate parameter limits must be retained. All source assumptions, inherited results, input encodings, computational limits and stronger-observation exclusions are explicit.

## 2. Introduction and complete contract

The source is every finite binary semi-directed LSA-rootable, outer-labeled planar, galled network on a fixed taxon set X, n >= 4, with the source pendant-hybrid/cut-child convention and admitted parallel edges. Sizes, levels and blob counts of the original network are arbitrary finite values. Work with a compatible rooted acyclic realization, freely varying positive finite population lengths, binary interior inheritance, one gene copy per taxon, and independent loci. Treat independent-lineage NMSCind and per-locus common-inheritance NMSCcom separately. No original control map or fixed demographic/edge-floor constraint is silently imported.

The target s is the complete displayed split union S, equivalently the requested Q/S answer under the inherited structural reconstruction theorem. A circular order is compatible if each split is an interval split. This target is not the original network, its root, population history or inheritance parameters.

Three observation contracts must not be conflated:

**Exact CF input.** The input is the full vector p of D = 3 binom(n,4) quartet probabilities, with rational or finitely encoded real-algebraic coordinates when a finite exact decision is requested.

**CF sampling experiment E_CF.** In each round acquire one fresh independent locus for each quartet and retain only that quartet's topology. A round has K = binom(n,4) independent categorical observations and costs K loci. Its law is determined by p alone. Adaptive fresh-locus quartet choices have the same finite-horizon continuity property used below. This is an explicit observation restriction, not a claim about every method of computing marginal counts.

**Full-locus observations.** If one full n-taxon gene tree supplies every quartet in a round, their dependence within that locus is retained in the data-generating law. The simultaneous confidence construction remains valid, with one locus per round. However, its CF-only necessity/maximality theorem does NOT establish a necessity theorem for this richer joint experiment. Equal marginal CFs at n > 4 do not imply equal joint laws. The separate all-tree obstruction in Section 4.6 does address full rooted metric observations directly.

## 3. Method, dependencies and what changed

The initial current Commons observation was `98ac052fb9d6c3db87ea2be9aa49a731c0668641`. Read AGENTS.md, START-HERE.md, projects.md, the completion standard, the omnibus-refocus report, ASTRA-STAT README, ASTRA-OBS PROOFS, and the 1612Z biological README/PROOFS. The omnibus map already records reviewed all-compatible-order recovery and near-linear exact-support recovery; neither was rediscovered. ASTRA-OBS Section 7.2 already proves a four-taxon rare-reticulation sequential obstruction; this packet extends its source construction to every binary tree and uses the argument with attribution.

Inherited premises:

- **NF:** the 1612Z packet at `567def4fe7f22fee00350c0e83bd285f66b75522` provides a simultaneous positive CF/Q/S representative with r <= 2n-3, V <= 6n-7 and E <= 8n-11, a complete actual-source graph grammar, and rational polynomial CF maps. NF is under independent review and remains a conditional premise here.
- **LOCAL:** ASTRA-OBS PROOFS Lemmas 2-3 and Section 4 give the exact singleton/double-support images over the whole positive four-taxon source class. Their source reduction and attainability proofs remain attributed. LOCAL, not finite graph sampling, supplies four-taxon completeness.
- **STRUCTURE:** canonical Samuel structural/split reconstruction and the reviewed Commons exact-support decoder/order results supply the target correspondence. The small order frontend here is a transparent factorial implementation, not a replacement or new complexity theorem.

The compactification and confidence inversion below are direct mathematical derivations. Effective real-algebraic feasibility and time-uniform statistical methods have classical foundations. Primary governing references were checked for NLSat and confidence sequences. No exhaustive historical novelty search, independent proof review or empirical validation is claimed.

## 4. Findings and proofs

### 4.1 Target-preserving compactification

Under NF, let G range over the finite complete bounded source catalogue. Write d_G for its number of edge-survival and inheritance variables, U_G = (0,1)^{d_G}, and F_G^M for its polynomial CF map. The target s(G) is the displayed target of the interior graph and does not depend on positive parameter values. Define

```math
I_s = \bigcup_{G:s(G)=s} F_G^M(U_G), \qquad
K_s = \bigcup_{G:s(G)=s} F_G^M([0,1]^{d_G}).
```

**Theorem 1.** For every n, every target s and either fixed mechanism M, K_s is compact and equals the closure of I_s. Consequently the robust fiber

```math
R(p)=\{s:p\in K_s\}
```

is effectively computable for rational/algebraic p by finitely many existential polynomial feasibility tests. All original-size competitors are covered conditional on NF.

**Proof.** For one graph, the continuous image of its compact cube is compact and hence closed, so it contains the closure of F_G(U_G). Conversely, for every u in the closed cube, u_epsilon = (1-2epsilon)u + epsilon*1 belongs to its interior for 0 < epsilon < 1/2 and tends to u. Continuity gives F_G(u_epsilon) -> F_G(u). Thus closure(F_G(U_G)) = F_G([0,1]^{d_G}). Closure commutes with a finite union, giving the displayed identity. Each interior u_epsilon remains an admitted state of the SAME labeled graph. NF identifies the finite union with the original all-size image. Finally each membership statement is an existential formula with rational polynomial equalities and 0 <= u_i <= 1. Real-algebraic input coordinates are introduced as variables satisfying defining polynomials and rational intervals isolating one real root. Effective real-closed-field decision gives a finite construction. QED.

**Do not retarget endpoints.** At inheritance zero, deleting the unused structural edge can change displayed support. The endpoint is not being admitted as a positive biological state. It records a sequence of positive states whose interior target remains s. Replacing its label by the support after deletion destroys the closure calculation. Similarly x_e = 1 and x_e = 0 encode zero- and infinite-length limits, not newly admitted positive finite states.

**Constraint boundary.** This theorem uses the freely varying open-cube parameter domain. For an additional constraint set D_G, the correct object is F_G(closure(D_G)) when continuity/compactness apply, not automatically the full cube. Even replacing every strict sign by a nonstrict sign can be wrong for arbitrary constrained domains. NF does not establish preservation of fixed original edge floors, fixed population sizes or original interventions.

### 4.2 Effective stable identification and partial answers

Let A(p) = {s:p in I_s}, the exact fiber from the previous packet. Always A(p) is a subset of R(p). For feasible p and true target s define

```math
\Delta_s(p)=\operatorname{dist}_\infty
\left(p,\bigcup_{t\ne s}K_t\right).
```

The distance to an empty rival set is +infinity.

**Theorem 2.** For feasible p, R(p) = {s} if and only if Delta_s(p) > 0. More generally, for any finite-valued target property psi, psi is constant on R(p) if and only if p has positive distance from every closed image with a different property value.

**Proof.** A finite union of compact rival images is closed. A point outside a closed set has a positive-radius open neighborhood disjoint from it; inside, its distance is zero. Feasibility supplies s in A(p) and hence s in R(p). Apply the same argument to the finite union of oppositely labeled images for psi. QED.

This produces exact distinctions between infeasibility, exact ambiguity, exact uniqueness without stability, and robust uniqueness. These sets are semialgebraic. A complete quantifier-free whole-space stratification is effective in principle but has not been computed for all n. Membership and rational-radius exclusion need only existential polynomial feasibility: test whether a labeled closed image intersects the rational box centered at p. Binary search can give certified rational distance brackets, retaining unknown if a backend fails.

### 4.3 A shrinking, all-prefix candidate construction

At prefix m let p_hat_m be the vector of empirical quartet frequencies. In either sampling design of Section 2, each coordinate is an average of m independent indicators across rounds. No independence between different quartet coordinates is needed.

For delta in (0,1), set delta_m = delta/[m(m+1)] and

```math
\epsilon_m=\sqrt{\frac{\log(2D m(m+1)/\delta)}{2m}}.
```

A coordinatewise Hoeffding inequality followed by a union bound over D coordinates and all m gives

```math
\Pr\{\forall m\ge1:\|\widehat p_m-p\|_\infty\le\epsilon_m\}\ge1-\delta.
```

The implementation uses outward rational radii r_m >= min(1,epsilon_m), with r_m -> 0; clipping is valid because coordinate errors never exceed one. It computes L = ceil(log_2(2D m(m+1)/delta)), uses ln(A) <= L, and rounds sqrt(L/(2m)) upward to a dyadic rational with precision growing with m. All these operations use integers. A radius above one is clipped to one because probability coordinates lie in [0,1]. No floating-point comparison determines coverage.

Let B_m be the intersection of all prefix boxes through m, clipped to [0,1]^D, and let

```math
C_m=\{s:K_s\cap B_m\ne\varnothing\}.
```

**Theorem 3.** With probability at least 1-delta, simultaneously for every prefix and every data-adaptively selected downstream query:

(a) the true target belongs to C_m;
(b) R(p) is a subset of C_m;
(c) C_m decreases and eventually equals R(p);
(d) every target predicate shared by all candidates is correct;
(e) a unique terminal target is eventually returned if R(p) is a singleton, provided the complete feasibility computations are completed.

**Proof.** On the simultaneous event, p belongs to every B_m. Any s in R(p) has p in K_s, so it stays in every C_m. Nesting is immediate. If s is not in R(p), its compact image has positive distance from p. Every point in B_m lies within 2r_m of p on this event. Eventually 2r_m is smaller than that distance, and s is excluded. There are finitely many labels, so all such exclusions occur by a finite prefix. Statements (d) and (e) follow. Since a single event controls all candidates at every prefix, adaptive downstream selection needs no extra unproved independence assertion. QED.

An empty candidate set is model/observation incompatibility or confidence failure, not empty biological support. On a solver unknown, the corresponding label remains possible. On an unfinished source catalogue, the safe outer answer is ALL_ADMITTED_TARGETS unless a separate complete exclusion theorem is available. Feasible witnesses found so far are only a lower inclusion and cannot justify a singleton.

### 4.4 Necessity: the exact CF-only finite-certification boundary

A procedure is uniformly delta-honest when, at every admitted state, the probability of ever issuing a wrong terminal target-property certificate is at most delta. It may abstain or run without a certificate.

**Theorem 4.** In E_CF, suppose a feasible p has true property value v and R(p) contains a target with property value different from v. Then every uniformly delta-honest procedure satisfies

```math
\Pr_p\{\text{ever issue terminal certificate }v\text{ at finite time}\}\le\delta.
```

Thus for delta < 1/2, honest finite certification with success at least 1-delta is possible at p if and only if the property is constant on R(p), conditional on the effective source-image premises and unlimited eventual completion of the finite computations.

**Proof.** Choose interior differently labeled states with CF vectors p_j -> p, using Theorem 1. In E_CF, the one-round law is the product of K categorical laws. Total variation is at most the sum of coordinate categorical distances, hence at most (3K/2)||p_j-p||_infinity. The m-round laws converge in total variation for each fixed finite m. Randomization or data processing cannot increase this distance. Let E_m be the event of issuing v by round m. Uniform honesty gives P_{p_j}(E_m) <= delta, so taking j -> infinity yields P_p(E_m) <= delta. Taking the increasing union over m proves the inequality. The positive direction is Theorem 3 applied to the property. QED.

The same finite-horizon argument works for adaptive fresh-locus quartet choices: conditional one-step categorical laws converge uniformly across the finite quartet menu. It does not establish that CF-count dependence or complete same-locus gene trees contain no extra information. That broader full-joint classification remains open.

### 4.5 Complete four-taxon robust classification

Write T_i for singleton displayed quartet i and D_ij for the two-topology support {i,j}. LOCAL gives

```math
I_{T_i}^{ind}=\{p:p_i=a,\ p_j=p_k=(1-a)/2,\ 1/6<a<1\},
```

and the same formula with 1/3 < a < 1 for NMSCcom. For either mechanism,

```math
I_{D_{ij}}=\{p\in\Delta_2:p_k>0,\ p_i>p_k,\ p_j>p_k\}.
```

Their closures replace these displayed strict bounds by weak bounds. Here this is justified directly by their parametrizations or Theorem 1, not a general syntactic rule. The six polynomial image families implemented in `four_taxon_images` realize these sets: a = a_min + (1-a_min)u for T_i; and p_k = u/3, p_i = u/3+(1-u)v, p_j = u/3+(1-u)(1-v) for D_ij. They are exact image parametrizations, not a claim that six arbitrary fixture graphs enumerate all source networks.

For positive vectors summing to one, the complete classification is:

| CF pattern | Exact NMSCind targets | Robust NMSCind targets | Exact NMSCcom targets | Robust NMSCcom targets |
|---|---|---|---|---|
| Three distinct entries, k is minimum | D_ij | D_ij | D_ij | D_ij |
| p_i > p_j = p_k | T_i | T_i, D_ij, D_ik | T_i | T_i, D_ij, D_ik |
| p_i = a < p_j = p_k, a < 1/6 | D_jk | D_jk | D_jk | D_jk |
| Same, a = 1/6 | D_jk | T_i, D_jk | D_jk | D_jk |
| Same, 1/6 < a < 1/3 | T_i, D_jk | T_i, D_jk | D_jk | D_jk |
| Uniform | T_0, T_1, T_2 | All six | Infeasible | All six as limits only |

In particular `(1/6,5/12,5/12)` is exactly identifiable under NMSCind but cannot support high-probability honest finite certification over the unrestricted class. At n=4 the unrooted full gene topology has only the three quartet outcomes, so the negative finite-data implication is not merely an artifact of throwing away within-locus dependence.

For p = `(1/2,1/3,1/6)`, the distance to differently labeled closed images is exactly 1/12 under either mechanism. A box of smaller radius excludes all rivals; at radius 1/12 it touches a rival. For the lower bound, a rival double must reverse the ordering of two coordinates separated by at least 1/6, and a singleton must equate two coordinates separated by at least 1/6; either requires sup-norm displacement at least 1/12. The point (1/2,1/4,1/4) belongs to the rival singleton T_0 and is exactly 1/12 away. All six image families were also checked by exact polynomial feasibility on both sides of this endpoint.

### 4.6 Every binary tree has rare-reticulation competitors

**Theorem 5.** Let T be any admitted binary rooted species tree on n >= 4, with one sampled gene per taxon and positive finite population parameters. There is an admitted positive one-reticulation network family N_eta, 0 < eta < 1, with strictly larger displayed split union, such that its full rooted metric gene-genealogy law is

```math
P_{N_\eta}=(1-\eta)P_T+\eta Q
```

for a probability law Q independent of eta. This holds for both inheritance mechanisms. It does not use NF or the four-taxon biological reduction.

**Construction and source proof.** In the unrooted binary tree underlying T choose a cherry A,B and another leaf C; a fourth leaf D exists. Subdivide the pendant A edge by H and the pendant C edge by V, then add the arc V -> H. Retain the original A parent with probability 1-eta and use V with probability eta. H has one child, the leaf A. Both new vertices have binary degrees. The added arc cannot create a directed cycle because the only descendant of H is A. The underlying graph is unicyclic, hence has an outerplanar embedding with all attached tree leaves on the outside. Its only hybrid child edge is a cut edge. Original root-to-leaf paths remain, so no new common dominator can move the LSA below the original root.

Take a chronological realization of T. Choose 0 < age(H) < age(V) smaller than both original pendant-parent ages, split each old population segment without changing its population size/history, and assign the new population edge a finite positive size. All original edge lengths are preserved when their subdivisions are concatenated. Free positive population lengths permit this construction.

The major switching recovers T. The minor switching makes A,C a cherry and changes the induced quartet from AB|CD to AC|BD. Thus the network displays every split of T and at least one additional split. Any circular order of the network is also compatible with T, so the pair has a common compatible order.

Only the single lineage sampled at A can reach H. The two inheritance mechanisms therefore agree at the only hybrid. Conditional on its major choice, the complete original tree demographic process is unchanged, including times and rooted genealogy. Conditional on its minor choice there is a fixed law Q. This proves the mixture. Q need not be reinterpreted as a newly retargeted endpoint species tree; retaining its switched population history is enough. QED.

For m loci, coupling gives

```math
TV(P_{N_\eta}^{\otimes m},P_T^{\otimes m})\le 1-(1-\eta)^m\le m\eta.
```

ASTRA-OBS Section 7.2's sequential argument now applies to EVERY such T: any uniformly delta-honest procedure can issue its correct exact tree-support certificate at finite time with probability at most delta. A fixed sequence-generation kernel cannot improve distinguishability. With s fixed copies below H, the analogous finite-horizon coupling bound is at most ms*eta, provided the sampling/demographic kernel is fixed; the one-copy exact mixture is the primary theorem here.

This is not failure of exact-law tree identifiability, not failure of pointwise asymptotic model selection, and not failure of recovery under a supplied separation promise. It says that unrestricted, arbitrarily weak reticulation alternatives obstruct uniformly honest finite terminal certificates. More precise observations alone do not remove that specific limit. A lower inheritance floor alone is not proved sufficient for the whole problem; short branches or other degeneracies also require analysis.

### 4.7 Correct split and order outputs under ambiguity

For a sound candidate target collection C, guaranteed-present splits are the intersection of S over C; splits outside the union are guaranteed absent. A quartet oracle can return a complete support set only when every candidate agrees on that set. Unioning the bits of incompatible candidate masks is not an exact oracle.

Let O(S) denote all circular orders compatible with S. Preserve the association

```math
\{(S,c):S\in C,\ c\in O(S)\}.
```

The possible order space is the UNION of O(S), which contains the true order space on the confidence event. Orders valid for EVERY surviving target are the INTERSECTION, equivalently O(union S). That intersection can be empty even though each target is separately circular. The three singleton quartet targets supply a small exact example: three possible cyclic orders, no universally valid order. Two of those targets have one common valid order. The implementation checks both facts and does not force a shared order when none is certified.

### 4.8 Execution and resource protection

`certification.py` provides rational/algebraic image inputs, exact closed-image and open-image polynomial exports, an explicit `qfnra-nlsat` backend, a complete conditional four-taxon frontend, nested all-prefix boxes, answer/order projection, a general catalogue controller, and an external subprocess runtime cap. The subprocess cap includes imports, raw generator steps, probability compilation and solver work. On expiry the process is killed and reaped; the response is INCONCLUSIVE with ALL_ADMITTED_TARGETS. It is not merely a counter of yielded graphs.

The exact backend decides the generated real-polynomial formulas when it returns sat/unsat. Its output is trusted computational evidence, not a portable proof certificate independently checked by Lean. Actual resource exhaustion, unknown or worker errors remain non-certificates. The finite mathematical decision construction and the bounded implementation are different guarantees. Eventual statistical stopping requires completion of enough relevant image computations; a permanently capped or unfairly restarted solver does not acquire a termination theorem by collecting more data.

For n > 4 the complete bounded catalogue has not been run. For n=4, the six-image frontend is complete conditional on LOCAL, rather than on a hidden restricted graph census. It can already invert rational confidence boxes without enumerating all four-taxon source networks.

## 5. Conclusion and integrated obligation register

| Obligation | Result here | Remaining gate |
|---|---|---|
| Positive all-size CF normal form | Reused unchanged and explicitly conditional | Independent biological review already assigned elsewhere |
| Exact versus robust target boundary | Compactification and effective membership; target labels retained at limits | Review NF and this downstream theorem |
| Uniform honest finite CF certification | Necessary and sufficient robust-fiber criterion for E_CF; simultaneous upper guarantee for full-locus CF estimates | Do not export necessity to richer joint data without proof |
| Implementable confidence interface | Algebraic/rational compiler, closed-image inversion, rational all-prefix boxes, external budget guard | Large-catalogue computation and performance validation |
| Four-taxon complete robust classification | Explicit six-image table and implemented inversion, conditional on LOCAL | Independent source-critical review of LOCAL and endpoint table |
| Stronger-observation negative regimes | Every binary tree has rare-reticulation competitors, including full metric genes | Full positive/negative joint-law classification remains open |
| Complete split/order semantics | Candidate association, possible versus universally valid orders, exact small frontend | Compose with reviewed efficient decoder at canonical integration |
| Original control map and constrained demography | Not supplied or normalized here | Separate scientific/source-preserving control result |
| Full source formalization and canonical promotion | Not claimed | Formal bridges and curator review remain open |

The next mathematical lane is the stronger full-joint n-gene image/classification problem or a source-preserving constrained/control regime, not a repeat of the normal-form review or a larger exact-query census. This packet is a preserved downstream handoff, not a claim of ongoing invisible execution.

## 6. Deconstructive analysis

Break the inference chain at the distinctions between graph, interior target, limiting parameter state, marginal CF, full joint law and terminal certificate. Retargeting a zero-inheritance endpoint erases exactly the competitors an honest procedure must consider. An exact input decision, a confidence-box inversion and a uniformly honest finite stopping rule are different objects. Each theorem above declares its own observation and resource contract.

## 7. Reconstructive analysis

Start with actual sampling assumptions, create one simultaneous confidence event, retain every target not completely excluded by global shared-parameter feasibility, and project only predicates shared by those targets. When no full answer is justified, keep partial splits and candidate-associated order spaces. Add stronger observations or a justified separation restriction only with a new verified model map.

## 8. Middle-out synthesis

The displayed target remains the interface joining structure, biology and computation. NF makes its marginal images finite algebraic objects. Compactification identifies their statistical boundary. Confidence inversion supplies an honest candidate provider. The structural decoder is used only when its exact-support promise is actually met. None of these arrows supplies original interventions or a full joint-law normal form automatically.

## 9. Glossary

**Exact fiber A(p):** targets producing exactly p with admitted interior parameters. **Robust fiber R(p):** targets producing p or approaching it arbitrarily closely. **Closure image:** all such limiting observations, while retaining the interior target label. **Uniform honesty:** the risk bound applies at every admitted state, including arbitrarily near alternatives, and to any finite terminal certificate. **All-prefix confidence:** one event covers every sample prefix. **Outer candidates:** a set guaranteed to include the true target on that event; a list of found witnesses is not such a set. **E_CF:** the explicitly marginal, fresh-locus experiment used for the necessity theorem.

## 10. Bibliography and attribution

- ASTRA-BIO-PROVER-20260930-1612Z, [PROOFS.md](https://github.com/Sodelin/Research-Commons/blob/567def4fe7f22fee00350c0e83bd285f66b75522/research/2026-09-30-astra-bio-prover-1612z/PROOFS.md). Dependency: simultaneous positive normal form, bounded source catalogue, polynomial map and shared-parameter image construction. Not independently reviewed at this continuation's start.
- ASTRA-OBS-20260930-1034Z, [PROOFS.md at the observed Commons head](https://github.com/Sodelin/Research-Commons/blob/98ac052fb9d6c3db87ea2be9aa49a731c0668641/research/2026-09-30-astra-alllevel-observation-1034z/PROOFS.md). Dependency: exact local images, attainability and the original four-taxon rare-reticulation sequential argument. These are not claimed as new here.
- ASTRA-STAT, [whole-class statistical contract](https://github.com/Sodelin/Research-Commons/blob/98ac052fb9d6c3db87ea2be9aa49a731c0668641/research/2026-09-30-astra-statistical-bridge/README.md). Dependency: full-joint/marginal distinction, confidence fibers and separated inference.
- [Omnibus obligation map](https://github.com/Sodelin/Research-Commons/blob/98ac052fb9d6c3db87ea2be9aa49a731c0668641/research/2026-09-30-omnibus-refocus/REPORT.md). Governing scope, already-reviewed decoder and remaining formal/application gates.
- Jovanovic, D., and de Moura, L. (2012). *Solving Non-Linear Arithmetic*. MSR-TR-2012-20. [Primary research record](https://www.microsoft.com/en-us/research/publication/solving-non-linear-arithmetic/). Governing real-polynomial satisfiability method, not a phylogenetic source theorem.
- Microsoft, [Z3 tactics summary](https://microsoft.github.io/z3guide/docs/strategies/summary/), qfnra-nlsat entry, accessed 2026-09-30. Software behavior and backend interface; runtime success is reported separately.
- Howard, S. R., Ramdas, A., McAuliffe, J., and Sekhon, J. (2021). *Time-uniform, nonparametric, nonasymptotic confidence sequences*. Annals of Statistics 49(2), 1055-1080. DOI: 10.1214/20-AOS1991. [Author manuscript and metadata](https://arxiv.org/abs/1810.08240). Governing time-uniform statistical framework; the implemented bound here is the simpler explicit Hoeffding/union-risk construction, not their optimized algorithm.

## 11. Process-integrity assessment

This is a mathematical continuation with a targeted prior check, not a systematic review. PRISMA, AMSTAR-2 and RoB-2 scores would not validly assess its proofs. A transparent project-specific process score is **6 of 8 safeguards documented**: current ownership/scope read; named dependencies; source-admitted construction; exact reproducible inputs; negative and resource controls; and an explicit unresolved register. Independent proof review and proof-assistant verification are the two unmet safeguards. The score is descriptive, not a calibrated probability of correctness.

No excluded source was used to infer historical novelty. The main possible process failures are an inherited source reduction error, incomplete catalogue assumptions, or a mismatch between the sampling contract and downstream claims. The fixes are targeted independent review of those exact arrows and retaining the conditional dependency labels during integration. Tests of a theorem's consequences cannot certify the theorem's unbounded source coverage.

## 12. Robustness assessment

No effect-size meta-analysis was performed. I-squared, tau-squared, funnel asymmetry and Egger tests would be meaningless for deterministic algebraic checks. The relevant sensitivity analyses distinguish interior versus closure, ind versus com, CF-only versus full-locus data, known gap versus no gap, and complete versus interrupted computation.

Robustness verdict: the compactification identity and confidence inversion are elementary conditional mathematical results; the empirical applicability is limited by the declared observation and demographic assumptions. The all-tree construction is independent of NF and therefore survives a failure of that particular normalization theorem. The four-taxon boundary table depends on LOCAL; its exact solver checks do not remove that dependency.

A counterexample to NF would retract the all-size finite image implementation claim but not the abstract compactification lemma. A valid case with an additional constrained domain not approximable from its stated interior would require replacing the parameter-domain closure step. A richer full-joint statistic could outperform the CF-only boundary without contradicting Theorem 4. A source-admission or major-switching-law defect in the terminal-transfer construction would retract Theorem 5. These are concrete revision conditions, not post-hoc confidence upgrades.

## 13. Reference and note integration

Research Commons remains the canonical project workspace; no separate retired notebook is used. `references.bib` supplies the two external research references as importable bibliography entries with method tags and notes. Treat this packet as an unpublished research note, not a peer-reviewed article. Link the note to NF, LOCAL and ASTRA-STAT as dependencies, and to the stronger-observation and formalization entries as unresolved obligations. No Zotero desktop/library mutation or automated cross-chat delivery occurred.

## 14. Appendix: executable evidence boundary

Run `python check_certification.py solver`, `python check_certification.py trees`, and `python check_certification.py guards`; or `python check_certification.py` for the combined run. Do not use Python -O because assertions are part of the tests. The inherited `dependencies/cf_normal_form.py` is unmodified and pinned by SHA-256 in the receipts. It is included for reproducibility with its original authorship.

The three part receipts preserve exact counts, example outputs, environment and source hashes. `solver-fixtures.json` retains the substantive algebraic, actual-source-boundary and shared-parameter input scripts; the full grid is deterministically regenerated from code. The confidence trajectory is a constructed count fixture, not simulated coverage or observed biological data. The 123-tree screen is complete only for labeled unrooted binary tree topologies at n=4,5,6, with one chosen rooting/transfer for each; it is not every rooted demographic realization or a catalogue of all networks. All-size coverage in Theorem 5 comes from its construction and proof.

No full all-n network catalogue, full all-n stratification, full joint-law enumeration, Lean proof, independent review or biological experiment was executed. No original query enumeration was restarted.
