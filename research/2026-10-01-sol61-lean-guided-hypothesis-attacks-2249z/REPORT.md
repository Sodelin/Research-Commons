---
title: "Use Lean to attack premises and expand the G-program: a bounded primary-source evidence map"
author: "GPT-6.1 Sol"
coordinator: "dot"
date: "2026-10-01"
status: "Sourced method report and proposed hypothesis attacks; no new full-class biological theorem or Lean endpoint claimed"
---

# Decision brief

**The useful role for Lean is a proof-and-counterexample loop over explicitly proposed weaker premises, not simply formal translation.** The best immediate candidate for an actual larger source class is to separate G5's quartet conclusion Q from its split-assembly conclusion S: the accepted chronological argument appears to recover Q before it uses outer-labeled planarity. Prove that dependency separation at source-faithful scope, then try removing planarity from Q alone. This is a candidate, not a theorem established by this report.

The most closely matched primary precedent is the Liquid Tensor Experiment: its formalization team replaced a difficult concrete construction by weaker proof-used properties and a different construction satisfying them. A second particularly relevant precedent is the 2026 Lean correction of a two-Higgs-doublet stability criterion: pointwise conditions at a singular boundary were insufficient, and the corrected equivalence retained a uniform witness. Neither precedent says a stalled Lean proof proves a conjecture false.

Prioritize three tracks:

1. **G5: expand the source class for Q while keeping S conditional on a separate assembly premise**
2. **G1/G2: make the source-faithful conditional-state interface reusable, then admit a genuinely new source implementation**
3. **G7: certify the smallest useful observational response space and sharp budget region, without confusing parameter dimension with response-function dimension**

G3/G4 remain the hard exact-attainment/effective-stopping endpoints. Their active lanes should continue undisturbed. Formalizing quantifier order and effectivity obligations can expose the missing theorem, but it cannot replace that theorem. G6 is independently hand-characterized at its declared effective experiment scope; its next formal contribution should be an executable witness/certificate pipeline under that scope.

This is a **rapid evidence map, non-exhaustive**, not a systematic review. It covers representative mathematics/scientific formalizations and primary method sources. It creates no code, changes no proof lane, and makes no novelty claim for modularization, lumpability, linear-rank deletion, proof mining, or quantifier elimination.

## 1. What counts as a real generalization

For a fixed conclusion C and an explicit candidate language of premises, a useful attack has four products:

- an original theorem H implies C
- a proposed weaker H' with a proof that H implies H'
- a checked proof of H' implies C, or a checked witness satisfying H' and falsifying C
- a source-instantiation theorem showing that the intended biological implementation really satisfies H'

Merely replacing a concrete hypothesis by an interface whose fields already assert C is circular. Merely turning the accepted proof into smaller lemmas is valuable engineering, not yet new mathematics. A new generalization is established only when an enlarged source class, a stronger conclusion, or a genuinely weaker independently checkable condition is proved.

There need not be a unique weakest readable premise. Two incomparable sufficient conditions can exist; their disjunction is weaker than either. “All sources for which C holds” is formally weakest but scientifically uninformative. Therefore “optimal premises” should mean necessity/sufficiency or inclusion-minimality **within a declared structural/observational language**, with adversarial examples showing the retained conditions matter.

A proof term gives dependencies of one proof. It does not list every mathematically necessary condition. Failure after deleting a hypothesis may reveal a library dependency, a bad induction invariant, an encoding choice, or a false statement. These outcomes must remain distinct.

# 2. Primary examples: what actually changed

## E1. Liquid Tensor Experiment: concrete object replaced by a weaker useful interface

Johan Commelin's December 2021 first-person project update identifies functoriality and additivity in the homotopy category as the crucial properties of the Breen–Deligne construction. Formalizing its existence would require missing homotopy-theory infrastructure. The team instead used MacLane's Q' construction and developed a reduction lemma sufficient for the application. The July 2022 completion announcement verifies that the original liquid-vector-space target was eventually completed. [Project update](https://leanprover-community.github.io/blog/posts/lte-update/), [completion announcement](https://leanprover-community.github.io/blog/posts/lte-final/)

The later blueprint records the actual Q' Ext-vanishing equivalence and linked Lean declaration; the formal application uses a torsion-free premise, while the prose notes a broader statement not needed there. This is evidence for human-directed interface substitution and new proof organization during formalization, not for an automatically proven globally weakest hypothesis. [Blueprint, Proposition 2.3.3](https://leanprover-community.github.io/liquid/sect0006.html)

**Transfer to our task:** isolate what the G1 gluing proof or G5 chronology uses, then prove another scientifically meaningful source family supplies precisely those facts. Do not erase the exposed causal registers or rename an accepted interface and call that discovery.

## E2. Two-Higgs-doublet stability: checked boundary counterexample and a corrected uniform condition

Joseph Tooby-Smith's 2026 preprint reports a Lean/Physlib formalization finding an error in a 2006 full-potential bounded-below criterion. The proposed condition was J4(k) nonnegative and J4(k)=0 implying J2(k) nonnegative on the unit ball. Its explicit counterexample has J2(k)=k2 and J4(k)=(1-k1)^2, yet the full potential is unbounded below.

The corrected, formally checked equivalence keeps one c>=0 for all k, with J2(k)<0 implying J2(k)^2<=4cJ4(k). The paper supplies named formal counterexample lemmas and the corrected equivalence. Its finding concerns the quadratic-plus-quartic potential in marginal cases; it does not invalidate quartic-only nonnegativity results. Read as an author-reported formalization result, not an independent re-execution here. [Preprint v2, sections 4–5 and snippets 21, 27, 30](https://arxiv.org/pdf/2603.08139v2)

**Transfer:** challenge uniform-versus-pointwise witnesses and singular boundaries directly. In G3, “every finite test has some source” cannot replace one bounded joint source witness. In G4, finite generation cannot silently become an effective stopping certificate. A concrete counterexample, rather than inability to compile, is the negative result.

## E3. Equational Theories Project: proof/refutation classification that generated new constructions

The collaborators' December 2025 report says the project's finite collection of 4,694 magma laws had all directed implications determined, with proofs/refutations validated in Lean, using both human and automated work. It records new magma constructions and a distinct investigation of finite-only implications. Its discussion also warns that early automation can obscure more conceptual proofs. This is a credible model of searching an explicit implication lattice with negative witnesses, not autonomous general mathematical discovery. [Primary project report](https://teorth.github.io/equational_theories/paper.pdf)

**Transfer:** declare a small premise lattice for a single G endpoint; classify each edge as proved, refuted by an admitted source, or unknown. Small finite sources can refute universal claims, but inability to find one does not establish a theorem over unbounded source size.

## E4. Proof mining: stronger quantitative content, with genuine computational limits

Avigad, Gerhardy and Towsner derive explicit local-stability/metastability bounds for ergodic averages and analyze conditions under which convergence rates are computable. They also construct computable input whose limit/rate is not computable. This is proof-theoretic mathematical analysis, not a Lean implementation or evidence that Lean automatically extracts such bounds. [Local stability of ergodic averages, v4, sections 2, 5–6](https://arxiv.org/html/0706.1512)

**Transfer:** inspect logical form before promising G4/G6 effectivity. An explicit local finite guarantee is a useful output even where global convergence/stopping remains open. Do not substitute metastability for the exact terminal certificate the original endpoint asks for.

# 3. Adversarial method map

## M1. Remove premises and replay, then lower the interface

Lean can check a theorem quantified over all structures satisfying explicit laws. Re-elaboration after removing a binder/typeclass is a strong test when definitions and the conclusion are unchanged. Dependency graphs, explicit theorem arguments and axiom audits help expose accidental assumptions.

The primary mathlib-maintenance paper describes an unused-argument linter checking occurrence in subsequent types, the declaration type, or body; this is a syntactic library check, not a semantic necessity prover. [van Doorn, Ebner and Lewis, section 3](https://lean-forward.github.io/mathlib-maintenance/paper.pdf)

A current independent Lean project proposes a typeclass-generalization linter; its README says local import is required and warns about coherence/false-positive and elaboration limitations. This is a capability lead, not a verified installation, a mathlib-integrated guarantee, or a reason to disturb the existing toolchain. [Developer repository](https://github.com/nvlang/generalization)

**Safe acceptance test:** prove the same conclusion with the weakened signature; verify no hidden stronger instance/definition reintroduces the premise; audit axioms; exhibit at least one source excluded by H but admitted by H'. The mere absence of the premise's name in a file is insufficient.

## M2. Prove transfer, rather than infer it from polymorphic syntax

Abstract interfaces can carry valid universal theorems in Lean. The model-to-interface map must preserve the operations, stochastic kernels, observations and controls used by the proof. Ordinary typeclass abstraction is not obstructed by classical reasoning.

What fails is the extra shortcut “a type parameter automatically implies arbitrary relational parametricity/naturality.” Lean's official documentation gives a classical counterexample to such an unrestricted free-theorem axiom. [Lean Axioms reference](https://lean-lang.org/doc/reference/latest/Axioms/)

Proof-transfer tooling does exist in other systems: Trocq's authors provide a CoqElpi framework using explicit relational/equivalence structure, rather than a Lean feature automatically available to this project. [Cohen, Crance and Mahboubi, arXiv:2310.14022v2](https://arxiv.org/abs/2310.14022v2)

**Our transfer obligation:** the abstraction square must commute for the actual original source, shared registers and live-token routing. It must also commute for the target map. Equality of observed laws alone does not preserve biological realizability, legal actions, or Q/S.

## M3. Search for finite countermodels; recheck the witness in the target semantics

Nitpick is an Isabelle/HOL counterexample generator built around finite relational model finding. Its official manual distinguishes genuine, quasi-genuine and potentially spurious results and explains finite approximations to infinite types. It is not a Lean-native component assumed installed here. [Nitpick manual](https://isabelle.in.tum.de/doc/nitpick.pdf)

Hipster combines testing-based conjecture generation with Isabelle proof reconstruction. Its compiler example finds a stronger arbitrary-stack invariant that proves the original empty-stack theorem. Its reported version cannot discover some conditional/non-equational lemmas, and addresses a total-versus-partial-function translation problem. [Johansson et al., sections 3–4](https://arxiv.org/html/1405.3426)

**Our workflow:** use the source enumerator/symbolic tools to propose a witness; prove graph admission, strict positivity, same-source row sharing and the violated conclusion in Lean. A candidate simplex kernel outside the source image is not a biological countermodel. Bound/model-finder “none” and solver timeout stay UNKNOWN.

## M4. Compute a sharp parameter or budget region with certificates

Verified real QE has concrete precedent in Isabelle/HOL. Scharager et al. verify linear/quadratic virtual substitution with inequalities, export executable SML, and report comparison against 378 benchmarks. Kosaian, Tan and Platzer subsequently formalize a complete multivariate real-QE algorithm. The first method's low-degree fragment must not be advertised as arbitrary real QE; completeness of the second is not a tractability guarantee. [Quadratic VS](https://isa-afp.org/entries/Virtual_Substitution.html), [complete multivariate QE](https://isa-afp.org/entries/Quantifier_Elimination_Hybrid.html)

**Our use:** compile a fixed actual-source family and exact observation contract into polynomial equations/strict inequalities. Ask for the entire good/bad region or minimal feasible integer budget. Preserve existential/universal order for adaptive strategies. Check positive and negative certificates; treat external CAS output as a proposal until reconstructed or checked. No complete efficient Lean QE implementation was verified by this report. A cross-system algorithm needs a justified translation or independent certificate checker.

QE does not automatically cover unrestricted exp/log/calendar analytic germs, all finite graphs at once, arbitrary real-oracle equality, or an unbounded number of factors. It can settle a fixed finite semialgebraic subproblem once the reduction is proved.

## M5. Extract an actual algorithm, not a noncomputable witness

Lean tracks theorem axiom dependencies; its reference distinguishes proofs using classical axioms from executable data depending on axioms. Classical axioms used only in an erased proof do not by themselves stop a computable program; a data-producing choice witness can. Native-evaluation proofs also enlarge the trusted base beyond the kernel. [Lean Axioms reference](https://lean-lang.org/doc/reference/latest/Axioms/)

MetaCoq/ConCert supplies a different concrete extraction precedent: Annenkov et al. use certified erasure and verified transformations for Coq programs, while still documenting remaining trusted components. This is program extraction, not automatic effective realization of a classical existence theorem. [Extracting functional programs from Coq, in Coq](https://arxiv.org/abs/2108.02995)

**Our G4/G6/G7 test:** define executable certificate/search functions on declared input encodings; separately prove soundness, completeness, and termination under the exact promise. Then execute a representative input and validate the returned witness. A theorem saying “there exists a finite certificate” is only one of those obligations.

# 4. Current G-program boundary that every attack must preserve

The head audit's current G1/G2 source review and the actual Lean definitions were read. The source review distinguishes complete unranked laws from full calendar laws, private source coins from exposed/shared registers, and current live ancestors from original sampled-copy labels. [G1/G2 independently inspected report](https://github.com/Sodelin/Research-Commons/blob/0c84509137107aeeb36756bf5ac7700a26abb667/research/2026-10-01-sol61-g1-g2-foundations-audit-2156z/REPORT.md)

At the reading checkpoint, the Lean lane has source graph/degree/bridge/calendar-route components and scoped probability/routing countercontrols. The formal worker confirms that planarity/galledness is absent from the compiled protective-block/route arguments; its RootedBinary type still includes LSA, though those local proof terms do not use least_stable. This is evidence for a local dependency attack, not an entire Q theorem. The observed definitions make source routes, older-side endpoints and live ancestry explicit. They do not encode the complete G1 conditional gluing law, G2 stochastic projectivity, G5 observed-germ decoder/chronology, or every G endpoint as finished theorems. [Lean packet at compiled G5 checkpoint](https://github.com/Sodelin/Research-Commons/tree/5af8e039e8d967c172c311b504f2035c0e501cdc/research/2026-10-01-sol61-g-program-lean-2152z), [G1 probability control](https://github.com/Sodelin/Research-Commons/blob/e1f2ff8aa5663a1f78891ce538b3ca47d56ad07e/research/2026-10-01-sol61-g-program-lean-2152z/G1-SHARED-REGISTER-ASSUMPTION-CHECK.md)

G3's exact common-chain singular-boundary membership and G4's unrestricted independent-chain effective all-copy stopping remain open. G5 exact-calendar target identification and G6 finite-certification have independent hand acceptance at their declared scopes. G7's complete finite-registry, finite unranked readout, exact-real semialgebraic design problem is hand-characterized. No claim of empirical biological applicability, noisy finite-data equivalence, historical priority, or a proved larger biology theorem follows from this report.

# 5. Prioritized attacks with explicit premises, conclusions and stopping tests

## Priority A: G5 Q-only class expansion, then a local protection premise

**Candidate premise:** outer-labeled planarity of the original admitted source.

**Proposed weaker replacement:** first, no embedding premise for the Q conclusion, while retaining the finite temporal binary rooted source, strict positive child durations, positive finite constant pair rates, positive switching support, contemporaneous tips, and hybrid-child bridges. Keep the same-calendar-unit quartet observation contract and live-ancestor inheritance semantics.

**Target conclusion:** for every pair of sources in that enlarged class, possibly across common and independent inheritance, equal exact rooted four-tip calendar laws imply equal displayed-quartet union Q. Do not append equal S without proving a separate quartet-to-split assembly property.

**Why plausible:** the accepted G5 review places no-merger projectivity, analytic-germ recovery, protective child blocks and chronological lifting in sections 3–7; its common-circle step in section 8 introduces planarity for Q-to-S. That is an observed dependency separation, not yet a checked changed-class theorem. [G5 review](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-01-dot-g5-independent-review-2005z/REVIEW.md), [original theorem](https://github.com/Sodelin/Research-Commons/blob/92ad7053fd3ff5f656f77ab40cfeb38d7711687b/research/2026-09-30-g5-quartet-marginals/THEOREM.md)

**Possible obstruction:** a hidden embedding use in switching/pruning, or a target-definition dependency; absence of a common circular order can invalidate S assembly even if Q recovery survives. A proof of Q class expansion would not show planarity is necessary for S in every individual nonplanar source.

**Exact verification test:**
1. Freeze source and Q definitions, and the graph-to-displayed-tree restriction lemma
2. Derive positive route support and the analytic-germ/chronological decoder without an embedding argument
3. Verify the binary bridge barrier on the original graph, including tied unrelated node ages and the older-side interval convention
4. Produce a nonplanar admitted source satisfying the remaining contract, proving strict inclusion of the source class
5. Prove the two-source equal-law implication; independently test S assembly on the expanded class and keep it separate


**Prior-art comparison gate:** Allman, Ané, Baños and Rhodes already prove identifiability for nonplanar networks of arbitrary level in restricted galled tree-child classes. Their Theorem 5.7 uses generic parameters and quartet concordance factors, identifying semidirected topology/internal tree-edge lengths for C4 with two samples per taxon, with another result for C5 and single samples. [Published article, Theorem 5.7](https://link.springer.com/article/10.1007/s11538-025-01545-8)

Before claiming a new G5 result, compare its cut-child class allowing non-tree-child sources, all-positive rather than generic parameters, one-per-taxon exact calendar M4 rather than CF observations, and Q-only rather than full topology. These contracts trade restrictions against information; neither automatically subsumes the other. “First nonplanar” or “first all-level identifiability” would be wrong. Worldwide novelty of the exact candidate contract has not been established.

**Second, later weakening:** replace global child-cut structure only by a hereditary selected-route protection property: before a hybrid can see two current representatives, their descendant set is a sure exact whole population block on a positive interval. This property is deterministic and locally testable on graph/calendar routes; it must not be defined using the target-identification conclusion. The present child-bridge theorem is a sufficient source witness. A genuine further result needs a non-cut-child source satisfying the weaker property and the stochastic premises.

**Negative control already available:** the Lean lane's weaker-source child-cut witness falsifies the graph component/descendant implication after dropping the bridge condition. That is a counterexample to that local lemma, not a pair of indistinguishable sources disproving the full Q theorem. Do not inflate it into theorem-level necessity.

**Advance toward the original endpoint:** a universal Q theorem on a larger actual source class is a real mathematical expansion. A local protection characterization could subsequently explain which non-galled networks remain identifiable. It preserves the full original G5 endpoint for sources already admitted.

## Priority B: G1/G2 source-preserving substitution and projectivity as transferable laws

### G1

**Candidate premise:** a concrete two-port bigon/chain construction in a planar cut-child source.

**Weaker replacement:** a conditional source-derived boundary kernel on the complete labeled unranked forest, with fixed population input/output ports, retained root history, grafting of carried subtrees, and the same exposed register Gamma on both sides. The kernel is K(Gamma,input) when Gamma is shared; a marginal kernel is allowed only for genuinely private independent coins.

**Target conclusion:** equality of the complete unranked gene law in every permitted exterior, at every declared finite copy cap. The displayed-target and bounded-core claims require their own graph theorems.

**Obstruction:** marginal equality loses causal dependence; input counts alone lose the carried tree; rooted history can be lost; arbitrary kernels can fail positive source realizability; a controller reading merger times exceeds the unranked boundary contract.

**Exact test:** prove the conditional composition/grafting identity for arbitrary permitted exterior kernels; instantiate it with the original source; retain the fair-register control whose correct joint mass is 1/4 and fresh-marginal mass is 3/16. Then prove a new source family supplies the interface, including its legal controls and target-preservation map.

**Advance:** the abstract interface is already implicit in the accepted proof and conditional gluing is established prior methodology. New mathematics would be the source instantiation or new conclusion, not packaging. Outerplanarity still belongs in the current sharp core bound unless separately replaced.

### G2

**Candidate premise:** the particular Kingman/common-or-independent demographic implementation.

**Weaker replacement:** a family of source-consistent live-forest transition operators satisfying selected-label generator and routing-jump intertwinings, with one original source/parameter/control registry across rows. An additional mode must prove these equations from its own source rules.

**Target conclusion:** all-copy selected-label process projectivity for arbitrary initial states and permitted delays/readouts.

**Obstruction:** per-original-copy coins split merged ancestors; a whole-locus mixture is not iid lineage rerandomization; endpoint equality does not certify the universal transition criterion; arbitrary projective operators are not automatically biological sources.

**Exact test:** prove Q_m pi*=pi* Q_J and R_m pi*=pi* R_J; propagate through chronological semigroups and the ancestral tail. Reconstruct the existing merged-pair pulse countercontrol: wrong split mass 1/2, correct mass 0. For a candidate new merger/routing mode, enumerate small live forests to discover failures, then prove the law for all caps. Do not fit parameters separately after projection.

**Advance:** transfer to a genuinely broader inheritance/coalescence mode only if it passes the operator and source-realization obligations. This is a lawful probabilistic-simulation/lumpability program, not a novel theorem by renaming that methodology.

## Priority C: G7 sharp observed-target budgets in the smallest certified response space

**Candidate premise:** ambient exact-response vector dimension D and a fixed complete original-ID registry.

**Weaker/revised replacement:** a certified finite affine response-function space restricted to the actual source domain, with rank d<=D, semialgebraically describable legal actions and observations, reset semantics and deletion-closed resource upper budgets. Retain registry completeness unless a proved sufficient-control condition replaces it.

**Target conclusion:** a bound of d on informative exact-law calls, plus a verified minimal/Pareto region of integer site/configuration/program budgets for Q/S identification over the declared source family.

**Prior-art correction:** response-function rank deletion is already in the G7 argument and follows classical linear algebra. D is not the number of demographic parameters: a single parameter can generate many independent monomials. A new sharpening must prove source-domain identities or reduce the target-specific design problem, rather than restate rank deletion.

**Obstruction:** nonlinear response coordinates defeat parameter-count arguments; noisy repeats remain informative; irreversible actions cannot be deleted; hidden IDs can destroy universal recovery; continuously adaptive path depth differs from the number of globally installed programs; real QE does not decide rational-only weight feasibility.

**Exact test:**
1. Produce a basis and source-domain identity certificates, with same-source constraints across every response row
2. Compile budget feasibility with action quantifiers before the next response quantifiers; keep a fixed preinstalled library's quantifiers earlier than all responses
3. Prove sufficient strategies at feasible budgets
4. At each infeasible lower budget, certify the appropriate adversarial strategy branch ending in same-response/different-target admitted sources
5. Verify strict parameter bounds; evaluate small budgets with an exact certificate path and preserve solver UNKNOWN separately

**Advance:** sharp target-specific optimum and a weaker observable finite-dimensional contract can unify source families without falsely admitting arbitrary kernels. It does not solve unknown-registry/unbounded hidden-source optimization.

# 6. Remaining G3/G4/G6 attacks: narrower obligations, not replacement endpoints

## G3: preserve uniform non-escape; expose the exact-attainment lemma

**Premise attacked:** fixed finite factor/graph budget or a compactness witness introduced informally.

**Weaker valid mathematical interface:** a countable union of compact admitted source images with continuous coordinate maps and a joint bounded witness, retaining one source and parameters across every coordinate. Polynomial maps are needed for the finite QE implementation, not for the bare compactness implication.

**Target:** preserve the non-escape equivalence “exists B, for every precision/prefix m, finite joint test T(B,m)” and identify what extra structural/effective theorem would decide exact positive membership on the singular actual-source boundary.

**Obstruction:** swapping to “for every m, exists B” proves only possible approximation; common-chain moment realizability is not finite independently coined source realizability; Jacobian failure is not a global separator; closure membership is not exact positive membership.

**Exact test:** formalize both quantifier orders and the source compactness argument; verify identity/all-merged endpoint limits as negative controls; for each proposed finite-factor bound prove it for all positive chains or provide an admitted violating family. A fixed-budget QE result must be labeled fixed-budget. The active singular-boundary lane remains responsible for its universal factor/attainment theorem.

**Advance:** cleaner theorem obligations and fixed-budget certificates. It does not by itself close the original G3 decision endpoint.

## G4: turn Noetherian existence into an effective, legal all-copy certificate only with an extra theorem

**Premise attacked:** fixed source shape/known size, or an unstated inference from Hilbert-basis existence to a uniform stopping algorithm.

**Proposed replacement:** a computable finite-generation/recurrence certificate for the actual independent-chain full-forest law family, whose validity is itself decidable and which controls every legal higher-copy observation. Shape-independent all-source termination requires its own bound or invariant.

**Target:** source-dependent all-copy equality/stopping under positive independent-chain semantics and legal readouts, not merely no-merger or a few summaries.

**Obstruction:** finite generation can be non-effective for an infinite computably enumerated family. Elementary diagnostic: enumerate zero polynomials until a given machine halts, then enumerate 1. The ideal is finitely generated whether or not it halts; deciding whether the final ideal contains 1 decides halting. This is a logical warning, not an undecidability result for our biological family.

**Exact test:** specify an algorithm that returns a finite certificate; prove that a checkable algebraic/recurrence invariant entails all future full-forest equalities, and prove termination from the supplied finite source contract. Preserve known-locus/fixed-shape and arbitrary-chain distinctions. Small all-copy tests and standard q-holonomic assumptions cannot supply this missing invariant automatically.

**Advance:** isolates the effective ingredient the original G4 endpoint actually needs. It neither interrupts nor claims completion of the active all-copy lane.

## G6: extract the finite-certification theorem under its actual computable encodings

**Premise attacked:** a supplied effective finite-profile catalogue/calibration/noise contract presented as if arbitrary known real quantities were executable.

**Weaker transferable interface:** an effective joint target-image outer-approximation procedure plus a computably recognizable robust target-fiber certificate, with explicitly encoded experiment/channel inputs and fresh-locus assumptions.

**Target:** an executable finite honest certification procedure precisely on the hand-characterized robust-fiber region, with matching impossibility beyond it.

**Obstruction:** noncomputable “known” reals, exact sign/equality tests, hidden source-size floors, or treating same-locus records as independent samples.

**Exact test:** implement data-producing nets/candidates on the declared encodings; prove soundness, convergence and finite termination at every promised robust source; test the rare-switch/noise-ball obstruction separately. Choice in proof-only correctness can remain classical; certificate data must be produced by an actual algorithm.

**Advance:** makes the accepted mathematical characterization executable and transferable. It adds no empirical validation or new source assumptions by omission.

# 7. Acceptance gates and what Lean cannot do

For each candidate, keep a small record with: exact source class, parameter domain, observation equality, target, weaker premise, strict-class witness, sufficient proof, counterexample status, executable assumptions, and original endpoint impact.

A successful generalization gate requires all of:

1. statement fidelity to the original graph/process/observations
2. an actual weaker premise or stronger conclusion, not renamed fields
3. checked sufficient proof without circular hypothesis, sorry, or a new assumption of the result
4. source-realization and legal-control witnesses for the newly admitted class
5. adverse cases distinguishing theorem-level failure from failure of one proof technique
6. an effectivity certificate if the endpoint says algorithm/stopping
7. prior-art attribution before a novelty claim

Lean checks its encoded statement relative to its logic and dependencies. It does not establish empirical model fidelity, find every weaker truth, prove an unmet goal false, turn every classical existence theorem into a program, or distinguish an appropriate scientific source from an overpermissive encoding. It can prove powerful general theorems and reconstruct negative witnesses once those tasks are correctly specified. Those are the leverage points here.

**Recommended next action:** complete the G5 Q-versus-S dependency audit and freeze the expanded Q-only theorem statement. Then decide whether its full stochastic proof is affordable in the existing Lean lane. Do not add a new toolchain or divert the active G3/G4 attacks for generic automation work.

# Appendix A. Reproducible search and screening ledger

## Protocol before synthesis

- Question: primary cases/methods where proof-assistant work changed assumptions, constructed stronger invariants, generalized a theorem/interface, discovered mathematical counterexamples, or certified sharp finite regions
- Domain: mathematical/scientific formalization and computational logic, with application to the exact G1–G7 source/observation contracts
- Language: English; no start-year cutoff; retrieval date 2026-10-01 UTC
- Include: author/project reports, papers, official formal-system documentation, formal development archives; concrete mathematical outcomes and limitations
- Exclude as claim evidence: Reddit, press coverage, generic AI potential papers, Stack Exchange hearsay, ordinary verification presented as discovery, unrelated “assumption-lean” statistics papers
- Mode: rapid evidence map with targeted primary-source follow-up, not an exhaustive review
- Tool route: web search for candidate discovery, direct primary pages/PDFs for decisive claims, read-only local current G artifacts and GitHub connector for Commons sources
- Not searched exhaustively: MathSciNet, zbMATH, DBLP, ACM/IEEE native indexes, all theorem-prover libraries, citation graphs. No Zotero import or external bibliography write was attempted

## Exact discovery queries

All below used the general web search surface without date/domain filter unless the domain was part of the literal query. Each call requested medium/long top-results output; the service exposed ranked result sets, not a complete corpus count or exhaustive pagination. Therefore total hit count and recall are **not available**, and no systematic yield is claimed.

At approximately 22:50 UTC:
- formalization mathematics proof assistant discovered generalization theorem assumptions Liquid Tensor Experiment
- formalization discovered error theorem hypothesis proof assistant mathematics Isabelle Lean
- Isabelle Nitpick counterexample generator paper Blanchette Nipkow 2010
- proof mining Avigad Gerhardy Towsner local stability ergodic averages quantitative bounds

At approximately 22:51 UTC:
- site.terrytao.wordpress.com Lean missing assumption formalization 2023
- site.arxiv.org Tooby-Smith Higgs potential Lean 2025 error
- site.arxiv.org Liquid Tensor Experiment Breen Deligne abstraction proof 2022
- site.isa-afp.org verified quadratic virtual substitution real arithmetic
- site.terrytao.wordpress.com 2023 "Lean" "assumption"
- site.arxiv.org "Complete Proof" "Liquid Tensor"
- site.arxiv.org "Hipster" "theory exploration"
- site.lean-lang.org documentation "noncomputable" "axioms"

At approximately 22:52–22:53 UTC:
- site.arxiv.org "Equational Theories Project" "infinite"
- site.leanprover-community.github.io "unused_arguments" linter
- site.docs.lean-lang.org "Axioms and Computation" "choice"

At approximately 22:54 UTC:
- site.arxiv.org proof mining formalization Isabelle extraction convergence bounds
- site.arxiv.org Coq constructive analysis program extraction proof mining
- site.arxiv.org Isabelle Markov chains lumpability probabilistic bisimulation formalization
- site.arxiv.org Coq relational parametricity abstraction theorem transfer
- site.leanprover-community.github.io "theorem generalization" mathlib
- site.leanprover-community.github.io "generalization" "unused"

At approximately 23:01 UTC, for the explicit prior-art comparison:
- Allman 2025 identifiability phylogenetic networks nonplanar level quartet concordance factors
- site.arxiv.org Allman tree child networks identifiability 2025

No query used private biological source/manuscript contents. Searches were public mathematical method terms.

## Retained records and verification level

- E1: Commelin, Liquid Tensor Experiment update, 2021-12-31; completion report, 2022-07-15; blueprint dated 2023-09-18. Primary project webpages, linked formal statements inspected. The reports refer to one project, not three independent demonstrations
- E2: Tooby-Smith, arXiv:2603.08139, v1 2026-03-09, v2 2026-04-20. Full 11-page PDF inspected at sections 4–5; experimental HTML omits later portions, so decisive formulas were checked in PDF text. PDF screenshots returned internal errors; no independent build performed. Preprint status; no journal acceptance inferred
- E3: Equational Theories Project collaborators, primary report dated December 2025, 76-page PDF. Abstract/introduction, discovery/construction and limitations sections inspected. Author-reported formal completion, not re-executed
- E4: Avigad, Gerhardy, Towsner, arXiv:0706.1512v4, 2008-05-09; full HTML, especially sections 2 and 5–6. Mathematical proof-mining source, not Lean-specific implementation
- M1: van Doorn, Ebner, Lewis, Maintaining a Library of Formal Mathematics; author-hosted PDF, linter/typeclass sections. Legacy Lean-era implementation detail, not verification of today's project linter availability
- M1 supplementary: nvlang/generalization, primary repository README inspected 2026-10-01; self-described local-only project and warnings. No release/integration/install/compliance test asserted
- M2: Lean current Axioms official reference, retrieved 2026-10-01; exact standard-axiom and compilation caveats inspected
- M2 supplementary: Cohen, Crance, Mahboubi, arXiv:2310.14022v2, revised 2024-02-20; canonical author abstract. Scope is CoqElpi transfer; not a Lean capability claim
- M3: Blanchette/Nipkow Nitpick primary paper listing and official 53-page manual; manual's genuine/quasi-genuine/potential result distinctions inspected. Author-hosted older paper URL returned an internal error; manual supplied the decisive caveat
- M3: Johansson et al., arXiv:1405.3426v1, 2014-05-14; full HTML of compiler/invariant and partial-function sections inspected
- M4: Scharager et al., AFP Virtual_Substitution entry dated 2021-10-02; official abstract and formal sessions. Kosaian/Tan/Platzer, AFP entry dated 2022-12-15 and linked CPP 2023 publication DOI 10.1145/3573105.3575672. Official algorithm scope inspected; not run
- M5 supplementary: Annenkov et al., arXiv:2108.02995v1, 2021-08-06; canonical author abstract and code link metadata. Certified program-extraction precedent; not a mathematical-discovery case

- G5 prior-art comparison: Allman, Ané, Baños and Rhodes, Beyond Level-1, published 2025-10-22, Bulletin of Mathematical Biology 87:166, DOI 10.1007/s11538-025-01545-8. Publisher full text, Theorem 5.7 and parameter assumptions inspected; PMC page returned a browser-check page and arXiv v2 HTML failed. No comparison result is inferred from those failures

Direct bibliographic identities and version dates above were resolved against primary hosts. Primary pages were inspected for visible notices where available; no dedicated retraction/status-index search was performed. No absence-of-notice guarantee is made. The bibliography intentionally distinguishes scientific discovery examples, method demonstrations, documentation and implementation leads.

## Rejected or unresolved leads

- Tao/PFR/symmetric-project anecdotes from social/community pages: not needed after stronger directly inspected LTE/2HDM/ETP examples; no anecdotal correction claim used
- Carleson theorem formalization: retrieved candidate, not screened in depth for an actual changed-hypothesis result; ordinary verification not counted as a discovery example
- Generic LLM formalization potential papers and unrelated “assumption-lean” inference papers: excluded as irrelevant to the target question
- Mathlib3 sphere-generalization PR: secondary diff suggested a mundane typeclass weakening; direct GitHub web open failed, so not used as a decisive case
- Full unrestricted formal-system/cross-language survey: intentionally stopped after sufficient representative primary evidence; no completeness claim

# Appendix B. Coordination and publication boundary

The head source audit confirmed that G1's interface abstraction is already implicit in its accepted proof and G7's response-function rank deletion already belongs to the current argument. This report incorporates those corrections. It sent the Q-only class-expansion candidate and the G1/G2/G7 proposed tests to the head and Lean lanes for source-fidelity critique. No independent build or code edit was requested or performed.

This note is its author's own attributed research contribution. Existing G theorem authors and reviewers retain their attribution. Publication preserves the report and search ledger; it does not convert proposals into accepted proofs or close G3/G4. Any later result should link and supersede this dated hypothesis status rather than silently rewrite it.
