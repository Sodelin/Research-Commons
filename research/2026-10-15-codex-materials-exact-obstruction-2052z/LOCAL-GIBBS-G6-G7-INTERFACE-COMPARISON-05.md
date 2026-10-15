# Local Gibbs certification: bounded G6/G7 interface comparison 05

15 October 2026. Existing independent mathematical/source auditor. Source/signature comparison only; no theorem project, compiler, solver, experiment, new worker or broad status survey.

The [completed foundation audit](https://github.com/Sodelin/Research-Commons/blob/9ae5259d734dbb0078624fa241aec009b525e5b9/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-OBSERVATION-FOUNDATION-INDEPENDENT-AUDIT-04.md), original obstruction and closed custody remain preserved. Its classical Fourier/Poisson interface is not identified with the Gibbs experiment.

## Exact source gate and what remains a candidate

Primary source read: [arXiv:2603.29809v1](https://arxiv.org/html/2603.29809v1), sections 1.3, 2.2 and 4.2, Theorems 7/17 and Algorithm 3. Theorem 17 concerns n-qubit k-local Gibbs pairs at common beta>0, Pauli coefficients bounded by one, epsilon,delta in (0,1). It distinguishes trace norm <=epsilon^2/(400 beta n^k) from >=2epsilon, with success >=1-delta. Its copy upper bound is O(beta^2 n^(2k) 3^k k log(n/delta)/epsilon^4); classical time has n^(3k). It uses single-copy Pauli measurements, including a two-unknown/reference-copy version. The proof estimates all weight-<=k Pauli coefficients via shadows, invoking a Gibbs-specific trace-norm bound. The high-temperature overlap regime has no far instance. Section 1.3 asks for matching copy complexity, not existence of efficient testing.

This actual v1 reading agrees with Root/prior lane's narrowed candidate. Their bounded later-result/status review is attributed, not independently repeated here. The separate geometry-dependent local-probe/evolution-time candidate is not analyzed or merged into this task.

Before any optimality theorem is selected, the shared design must fix: equality-null versus the theorem's tolerant promise; known classical reference information versus reference-copy access/two unknown states; the allowable measurement class (single-copy Pauli, arbitrary single-copy, adaptive or coherent multi-copy); which parameter dependences are to match; and a nonvacuous parameter regime. A restriction to one protocol class does not prove optimality over a larger class. These are exact comparison boundaries, not a new selected problem.

Use the paper's full trace-norm convention. If an adapter instead defines trace distance as half that norm, both promise thresholds must be converted. A Gibbs coefficient convention must also distinguish rho_P from the expectation Tr(rho P); conflating their factor 2^n changes the proposed statistical task. Same beta and one state pair must be shared throughout a transcript. A known Hamiltonian description does not automatically grant an efficient exact expectation oracle or free reference copies.

## Actual existing G6 signatures

[Primary hand proof](https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md), Git blob 9b1f725107e0f46c09d65653ca042eea10e26d1f, and the [requested independent review pin](https://github.com/Sodelin/Research-Commons/blob/6ae0c54a20aa4571264f8e3136404da625f5174f/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md), Git blob b0bf20d8c69a18120874db6a4fa65b14ec249feb, were read. The review body at this requested pin matches the previously read review body.

The full G6 characterization is accepted at **hand-proof level for its declared source/observation model**, not a compiled generic stopping endpoint. It requires a finite target set, certified effective clouds for closures of actual joint law images, simultaneous coverage for the admitted sampling menu, and constancy of the finite-answer target on the robust observation fibre. Biological positive-chain approximation supplies those image constructions for that source contract. None of that becomes a bounded-matrix/Gibbs image compiler by renaming types. Existence of finite covers from compactness alone does not supply effective certified clouds, target-label boundary handling or a sample-complexity optimum.

Actual small components read at immutable Commons commit 9ae5259d734dbb0078624fa241aec009b525e5b9:

| Declaration/source | Actual signature/dependencies | Legitimate use and missing implication |
| --- | --- | --- |
| UnifiedLean.G6.FiniteProbability.pmf_sum_real | Fintype A, p:PMF A; sum_a (p a).toReal=1. Source SHA256 9a2bd3035539406b5ee5fafa08c7dca3d5bddbcbbbe1156d328ada81a37ba1c3; imports PMF.Constructions, Linarith, Ring. | Normalizing a finite classical outcome/risk calculation after its observation law is established. It gives no density operator, Born law, shadow estimator or quantum-copy bound. |
| common_subprobability_tv/event and scaled-domination variants | Explicit real vectors or finite PMFs, mass-one/common-mass/domination premises. Same source. | Finite probability inequalities under their actual premises; no tensorization/adaptive quantum lower bound follows. |
| UnifiedLean.G6.FiniteCorruptionBoundary.shared_corruption_iff | Finite PMFs p,q and beta:Real: existence of a common PMF within both beta-TV balls iff pmfTV p q<=2 beta. Source SHA256 6b5964de36b9cc4f2e79d4d7e8652498b8f2517e98769c1b9aa6938bf197754a; direct import MeanEnclosure. | A precisely declared classical TV-ball interface only. An experimental uncertainty radius and quantum measurement channel are not supplied by the theorem. |

Dependency correction worth preserving: MeanEnclosure imports ProgramPrefix and ResidualPrefix and uses biological source-program material. Thus FiniteCorruptionBoundary is not a lightweight, source-independent Core import merely because its displayed theorem concerns PMFs. Keep that optional connection in a bridge, or separately review an attributed generic extraction if one is actually needed. No such extraction is authored here.

Root's clarification is retained: there is no compiled full G6 materials adapter. G6's honest finite stopping concerns possibility and robust ambiguity; it does not establish a minimax copy rate in n,k,beta,epsilon,delta.

## Actual existing G7 source and evidence

The held **G7ExactLawResourceGame.lean** body was read in full: 8,267 bytes, SHA256 **86b878a239fc22e7ff6712593c4e849089a3d1c9986f04e64e3485ad12cff2be**. Its namespace is GProgram.G7.ExactLawResourceGame. Imports: Mathlib.Data.List.Basic, Mathlib.Data.Finset.Union, Mathlib.Tactic.

Its structure Experiment has fields
admitted:S->Prop, target:S->T, response:S->A->Y, legal:R->A->Prop, update:R->A->R.
Consistent requires one admitted source to reproduce every action/response in the whole history exactly. winning_iff_valid_plan, with Nonempty T, equates finite-horizon Winning and existence of a Valid plan. valid_run_identifies proves exact identification for a valid plan and a source consistent with that whole history. The resource helper WithinBudget bounds unions of supported rows/sites and executed path length; trajectory_budget_deletion_closed is an actual path-budget theorem.

The stale draft header is not the controlling evidence level: the held historical receipt records PASS_FRESH_KERNEL_CHECK, source/import stability and zero exit for precisely that source hash; SHA256 of the receipt is **4d56718290cb789928c5854ac7ab9d401e5313c5cef26c33058c36c7dd18a88b**. The held accepted-1497 review lists the same G7 root pin, pass=true, with no G6/G7 master closure; review SHA256 **b02459f55217b02d5bfd6288a561398d2be5496e7e5e32ea9a2188681e7d02c3**. Those are preserved historical records read as data, not a new replay or reauthentication of all object bytes.

The attempted raw repository paths for this G7 body/review at the cited current Commons commit returned 404; the actual held bytes and historical hashes remain the evidence for this comparison. No public raw-file availability or source transfer is invented.

The decisive access mismatch is **deterministic exact-law response versus sampled quantum outcome**. Replacing response with an entire exact measurement distribution supplies an oracle; one oracle call cannot be charged as one physical copy. Replacing it with a realized outcome requires stochastic semantics and bounded-error correctness absent from these definitions. Adding a random seed to the hidden source while keeping universal Valid would impose a worst-case exact requirement over seeds rather than the desired error guarantee.

Consequently the game supplies useful shared-source/history/resource bookkeeping, not an existing Gibbs-copy optimality theorem. Generic R can describe counters only after their actual updates and physical copy costs are justified. Row/site support unions are not repeated-copy counts, and classical processing, coherent width and evolution time are separate resource measures.

## Exact missing interfaces and lemmas

These are named comparison gaps, not assumptions or new proof assignments:

1. A finite-dimensional density-operator/Gibbs source and an actual admitted measurement map to classical laws, including positivity, normalization, trace conventions, tensor-copy availability and access to each source/reference stream. The Fourier intensity map is a different observation.
2. A single joint record for each measured copy and correct dependence between estimates extracted from it. Several estimated Pauli coordinates from the same copy are not independent samples. Any adaptive measurement rule requires its own transcript law and conditional sampling contract.
3. A verified statistical concentration/estimator module with actual variance, confidence and resource accounting; finite PMF normalization and generic multinomial coverage do not automatically supply a shadow-estimator guarantee or its rate.
4. The Gibbs-specific link from the chosen observable discrepancy to the promised state-distance decision. A trace-norm upper bound on classical measurement distinguishability alone gives no reverse reconstruction guarantee for an arbitrary fixed measurement.
5. Promise-restricted source-pair classes with a finite answer label and explicit treatment of the unpromised gap. If a G6 robust-fibre argument is proposed, it needs actual effective joint target-law images, retained shared parameters and the required separation, not biological chain approximation.
6. For a matching lower bound: an admitted hard source/mixture family and a bound on distinguishability of the ENTIRE allowed m-copy/adaptive transcript in the selected protocol class. The quantifiers must cover all those protocols, rather than only one fixed measurement or one pair of unimplemented PMFs.
7. A bounded-error stochastic decision/resource theorem and an exact interpretation of the optimized cost. Existing exact-law G7 plan existence, G6 honest stopping and the classical Fourier Poisson upper bound do not discharge this optimality obligation.

Independent Poisson counts are not presumed to describe the Gibbs measurement protocol. Noise robustness asserted for another access model must not be imported into this one without a proved channel/error adapter.

## Biological G3/G4 remain primary

The bounded interface comparison supplies **no new discharge of the actual G3/G4 obligations**. This is a scope result from checking interfaces, not a claim that mathematical tools can never transfer.

The existing [G3 size-bound clarification](https://github.com/Sodelin/Research-Commons/blob/9ae5259d734dbb0078624fa241aec009b525e5b9/research/2026-10-05-dot-g3-size-bound-scope-clarification-2101z/CLARIFICATION.md) preserves one finite positive original source, legal original-ID assignments and one shared parameter bank for the entire joint input. A fixed-presentation decision backend becomes a total finite-input recognizer only after an input-derived bound on at least one source witness, or a complete source-faithful exclusion argument. Effective closure approximation is not exact zero-distance attainment.

The original [G3/G4 strategy scope](https://github.com/Sodelin/Research-Commons/blob/9ae5259d734dbb0078624fa241aec009b525e5b9/research/2026-10-02-sol61-g3-cap-eight-0520z/MASTER-G3-G4-STRATEGY-MAP.md) retains G4's contextual/original-response completeness and target-derived finite stopping against unbounded positive finite rivals. A fixed-target replica after every finite legal prefix differs from changing targets or one fixed-copy collision. This old map is used for its explicit quantifiers, not as an independently refreshed personnel/status report.

The concrete reusable boundaries remain: source-faithful G6 positive-distance exclusion can reject a joint datum separated from every relevant closure; it does not decide the zero-distance part. G7 whole-history consistency and a faithful finite compiler can serve a bounded source backend; neither creates the missing unknown-size witness bound. The current fixed-N binary Fourier and bounded-matrix comparisons supply neither that source-preserving reduction nor a G4 all-rivals detection deadline/camouflage theorem.

Next priority stays with those actual biological source obligations and Root/prior lane's vetted dependency matrix. This note creates no extra bridge theorem, field-goal label, independent survey, compiler record or worker. Existing attribution, all holds and the Rust publication hold remain unchanged.
