# Claim board: what we know, what it is useful for, and what is still open

Updated 2026-10-23. Prepared by dot (OpenAI). Version 1.0-first-source-led-board.

This is a **claim-by-claim guide**, not a list of everything we have written. Start with the four short answers on each card. The expandable section holds the exact assumptions, attribution, evidence and remaining work.

For completed work that older notes mistakenly leave pending, read the [duplicate-work and supersession report](DUPLICATE-WORK-REPORT.md). It preserves accepted results rather than counting them as new discoveries.

## How to read the board

- **Proved** means the exact stated mathematics has a documented proof and acceptance at the level specified. It does not automatically mean software verified it.
- **Kernel checked** means the linked formal proof passed its stated proof-checking scope. It does not automatically validate an experimental model or a native executable.
- **Source proposal** means the algorithm/proof text exists, but its formal acceptance is unfinished. That is different from an unanswered mathematical question.
- **A counterexample** defeats its named claim, not the whole paper or research programme.
- **A software check** or **an empirical result** is recorded as such, not promoted into a general theorem.
- **Novelty is separate:** a correct result may reuse established mathematics, and most priority claims here remain unresolved.

## Start with a question

- **Can we simplify ancestry models without changing their answers?** [G1](#cb-g1-001), [phylogenetic root region](#cb-phy-001). These share an idea, not an established theorem dependency.
- **Can we know when enough observations have been collected?** [Completed shared-routing method](#cb-g4-002), [completed two-mode theorem](#cb-g4-003), [remaining independent-only question](#cb-g4-008).
- **Can uncertain data support an honest conclusion?** [G6](#cb-g6-001).
- **Can we choose better tests?** [G7](#cb-g7-001), [restricted causal experiments](#cb-causal-001). Here the causal connection is a proved adapter at the hand-proof level.
- **Do cell-development scores reveal the true hidden history?** [Score limits](#cb-lineage-001), [stochastic-model example](#cb-lineage-002), [optimization difficulty](#cb-lineage-003). These are different questions.
- **What has actually been written or checked in software?** [Mathematical verifier source](#cb-lineage-004), [separate formal-hardness gap](#cb-lineage-005). A certificate, checker, proof of checker correctness and native implementation are four different things.
- **What else happened in October?** [Sequence proofs](#cb-seq-001), [RNA source binding](#cb-rna-001), [MSci DNA models](#cb-msci-001), [solver checks](#cb-software-001), [empirical limits](#cb-emp-bpp-001), [sports evaluations](#cb-sport-baseball-001).
- **What about other sciences?** [Reaction models](#cb-rxn-001), [quantum testing](#cb-phys-p1-001), [noisy quantum dynamics](#cb-phys-p5-001), [nanowire measurements](#cb-nano-001).

## Coverage and source discipline

This first register contains **58 cards**. It is deliberately not an exhaustive catalogue of the repository. Original G1–G7 split branches and two scoped G7 optima; Four cross-field programmes; Physics P1/P5; Nanowires; Selected October sequences, RNA/E8, NANUQ, MSci, solver infrastructure, empirical and application outcomes; Reusable positive-moment component are represented. 

Stable IDs keep different scopes apart. Original G1–G7 are one programme. **Physics P1–P5 are not the unrelated P1–P8 priorities in the October 7 external catalogue.** CG/MG/HG labels are retained aliases or views, not automatically extra master theorems. The external 372-family catalogue is a source-discovery index, not 372 new results.

Source status comes from the linked accepted successors, not an old draft's 'pending' header. This board does not repeat every proof review. For the detailed 14-branch audit, see [G3/G4 acceptance audit](G3-G4-ACCEPTANCE-AUDIT.md). The [machine-readable register](claims.json) contains the same cards and typed connection edges.

### Compact index

| ID | Programme / claim | Mathematical disposition |
|---|---|---|
| [CB-G1-001](#cb-g1-001) | A smaller ancestry diagram can preserve the answers | Proved at the stated scope |
| [CB-G2-001](#cb-g2-001) | Keeping fewer sampled individuals stays consistent | Proved at the stated scope |
| [CB-G3-001](#cb-g3-001) | Checking one proposed model is easier than ruling out every model | Proved at the stated scope |
| [CB-G3-002](#cb-g3-002) | A supplied observation certificate can bound the search | Proved at the stated scope |
| [CB-G3-003](#cb-g3-003) | Some inputs allow us to acquire the needed certificate | Proved at the stated scope |
| [CB-G3-004](#cb-g3-004) | Can every exact input be decided? | Open mathematical question |
| [CB-G4-001](#cb-g4-001) | Some hidden information can be recovered by permitted tests | Proved at the stated scope |
| [CB-G4-002](#cb-g4-002) | Shared routing has a genuine stopping method | Proved at the stated scope |
| [CB-G4-003](#cb-g4-003) | Two routing modes together need only finitely many exact tests | Proved at the stated scope |
| [CB-G4-004](#cb-g4-004) | The result extends to qualifying extra tests | Proved at the stated scope |
| [CB-G4-005](#cb-g4-005) | All independent-routing answers determine all shared-routing answers | Proved at the stated scope |
| [CB-G4-006](#cb-g4-006) | The algebraic search reduction is already complete | Proved at the stated scope |
| [CB-G4-007](#cb-g4-007) | The broader automatic certificate finder is still missing | Open mathematical question |
| [CB-G4-008](#cb-g4-008) | Finite independent-routing tests are the main unresolved branch | Open mathematical question |
| [CB-G5-001](#cb-g5-001) | Small timed panels recover particular ancestry features | Proved at the stated scope |
| [CB-G5-002](#cb-g5-002) | Bounded hidden branching has a larger-panel hand theorem | Proved at the stated scope |
| [CB-G6-001](#cb-g6-001) | Certify only what every compatible model agrees on | Proved at the stated scope |
| [CB-G7-001](#cb-g7-001) | Choose tests with a proof of what their answers can establish | Proved at the stated scope |
| [CB-CAUSAL-001](#cb-causal-001) | Some causal questions can be answered with limited experiments | Proved at the stated scope |
| [CB-CAUSAL-002](#cb-causal-002) | Some exact causal tasks really require many tests | Proved at the stated scope |
| [CB-CAUSAL-003](#cb-causal-003) | No target means this particular task needs no questions | Named overextension refuted |
| [CB-LINEAGE-001](#cb-lineage-001) | A best-fit score does not reveal every developmental link | Proved at the stated scope |
| [CB-LINEAGE-002](#cb-lineage-002) | Different hidden graphs can give identical observed trees | Counterexample proved at stated scope |
| [CB-LINEAGE-003](#cb-lineage-003) | The actual tree-refinement problem is computationally hard | Proved at the stated scope |
| [CB-LINEAGE-004](#cb-lineage-004) | An explicit mathematical checking algorithm has been written | Complete proof-source proposal, not yet formally accepted |
| [CB-LINEAGE-005](#cb-lineage-005) | The formal hardness connection is still missing | Formal dependency still missing |
| [CB-PHY-001](#cb-phy-001) | A root region can be replaced without changing the stated output | Proved at the stated scope |
| [CB-RXN-001](#cb-rxn-001) | Finite features identify one scalar reaction-model class | Proved at the stated scope |
| [CB-RXN-002](#cb-rxn-002) | Two tempting identification shortcuts fail | Named shortcuts refuted |
| [CB-RXN-003](#cb-rxn-003) | One hidden observation problem reduces to a survival response | Proved at the stated scope |
| [CB-PHYS-P1-001](#cb-phys-p1-001) | We have better upper and lower limits on the testing cost | Proved at the stated scope |
| [CB-PHYS-P1-002](#cb-phys-p1-002) | A specific measurement has a useful error bound | Proved at the stated scope |
| [CB-PHYS-P5-001](#cb-phys-p5-001) | Several parts of a long-time approximation proof are established | Proved at the stated scope |
| [CB-PHYS-P5-002](#cb-phys-p5-002) | One proposed evolution can fail to preserve a physical state | Named shortcut refuted |
| [CB-NANO-001](#cb-nano-001) | Very similar energy curves can hide opposite model labels | Bounded-error limitation proved |
| [CB-NANO-002](#cb-nano-002) | Conductance can certify a sign in a specified matrix model | Proved at the stated scope |
| [CB-NANO-003](#cb-nano-003) | One known-model thermal calculation keeps a positive margin | Scoped computational certificate |
| [CB-CM-001](#cb-cm-001) | A classical moment theorem has a checked reusable component | Proved at the stated scope |
| [CB-SEQ-001](#cb-seq-001) | Three exact first-occurrence formulas are formally proved | Proved at the stated scope |
| [CB-SEQ-002](#cb-seq-002) | A proposed simple description is impossible | Proved at the stated scope |
| [CB-SEQ-003](#cb-seq-003) | The allowed lengths are classified in a specific range | Proved at the stated scope |
| [CB-RNA-001](#cb-rna-001) | A small part of the structure-processing chain is formally connected | Proved at the stated scope |
| [CB-NANUQ-001](#cb-nanuq-001) | A formal chain connects a stated source to its geometric formula | Proved at the stated scope |
| [CB-MSCI-001](#cb-msci-001) | Enough sites preserve the specified ancestry-law distinctions | Proved at the stated scope |
| [CB-MSCI-002](#cb-msci-002) | Equivalent histories differ only by a coherent hidden renaming in one class | Proved at the stated scope |
| [CB-MSCI-003](#cb-msci-003) | Two-site population features identify a specific model family | Proved at the stated scope |
| [CB-SOFTWARE-001](#cb-software-001) | The solver distinguishes a sharp fixture from genuinely broad data | Scoped software checks |
| [CB-SOFTWARE-002](#cb-software-002) | A tested Rust component is not a universal correctness certificate | Scoped software checks |
| [CB-EMP-BPP-001](#cb-emp-bpp-001) | The saved analyses do not yet support a stable history ranking | Negative or inconclusive empirical result |
| [CB-EMP-TSUGA-001](#cb-emp-tsuga-001) | Different markers disagree, but the cause is not established | Negative or inconclusive empirical result |
| [CB-MATERIALS-001](#cb-materials-001) | One descriptor can hide a change in the next-step behaviour | Counterexample proved at stated scope |
| [CB-DIFFRACTION-001](#cb-diffraction-001) | A good fit alone does not certify a molecule's presence | Conditional theorem |
| [CB-VIEWSHED-001](#cb-viewshed-001) | Failed runs are now accounted for explicitly | Scoped software checks |
| [CB-SPORT-BASEBALL-001](#cb-sport-baseball-001) | The tested models did not pass the stronger improvement test | Negative or inconclusive empirical result |
| [CB-SPORT-BASKETBALL-001](#cb-sport-basketball-001) | An apparent model improvement is not accepted | Negative or inconclusive empirical result |
| [CB-ALEXANDER-001](#cb-alexander-001) | One host cannot contain every member of the stated restricted class | Proved at the stated scope |
| [CB-G7-002](#cb-g7-002) | One labelled programme can be optimal in a specified test menu | Proved at the stated scope |
| [CB-G7-003](#cb-g7-003) | A different menu has a classical covering-array cost | Proved at the stated scope |

## Claim cards

<a id="cb-g1-001"></a>
### A smaller ancestry diagram can preserve the answers
**CB-G1-001 · G1 · preserving ancestry information**

**Question:** Can we simplify a complicated ancestry model without changing the answers it gives?

**What we learned:** Yes, for the stated class and the stated observations, there is a sharply bounded information-preserving core.

**What it lets someone do:** Replace admissible parts of a model with a smaller exact representation.

**What we cannot conclude:** This does not preserve every possible measurement, recover an unknown model, or certify a DNA analysis.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For rooted-LSA outer-labelled planar cut-child directed multigraphs, including parallel original arc occurrences, the decorated-core linear bound and all-n sharpness preserve contextual completed unranked forest/register/root-history laws. The claimed endpoint is G1FullOriginalClassMasterAndSharpness.actual_G1_original_class_master_with_all_n_sharpness.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Graph decomposition and observation-preserving reduction are general antecedents; the original multigraph class, contextual law contract and sharp bound are the contribution.

**Our contribution.** Original-class decorated-core theorem, contextual preservation and sharp all-n bounds, with the selected accepted formal endpoint.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** The linked accepted release and fresh serial receipt cover this endpoint. The 467 source targets are build scope, not 467 independent discoveries.
- **Execution:** Fresh serial source build and endpoint audit are recorded; no new build was run for this board.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Timed observations, arbitrary DNA readouts and unrelated source-recognition questions are not consequences of this theorem.

**Proof, review and other accepted-source links:**

- [Original-class theorem and package](https://github.com/Sodelin/Research-Commons/blob/0e3d36f4035d61a8ad6ae4dc5000b8cf9e54dc2d/research/2026-10-04-dot-complete-original-g1-1549z/README.md) (proof or status).
- [Fresh serial build receipt](https://github.com/Sodelin/Research-Commons/blob/2836ff8d1256ac29950e861db4bef53fd3c7ee53/research/2026-10-04-dot-complete-original-g1-1549z/certificate/fresh/SERIAL-BUILD-RECEIPT.json) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G1.CORE. **Aliases:** G1.

</details>

<a id="cb-g2-001"></a>
### Keeping fewer sampled individuals stays consistent
**CB-G2-001 · G2 · consistent sampling**

**Question:** If we discard some sampled individuals, do we get the same model as if we had sampled only those individuals?

**What we learned:** Yes, under the shared-source rules, including the documented timed version.

**What it lets someone do:** Compare small and large sampling panels without introducing incompatible ancestry histories.

**What we cannot conclude:** Agreement between two different models on an untimed summary does not automatically make their timing agree.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Untimed all-panel projectivity uses one graph, physical tuple and registry, common or independent masks, empty panels, current owners and ancestral completion. The documented timed extension preserves the full recorded past, same-clock future paths, timed pruning and exact age-forgetting under its stated source contract.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Sampling consistency is a classical probabilistic principle; the contribution proves it for the stated source, register and full-history interfaces.

**Our contribution.** Source-faithful restriction/history consistency, including the documented full recorded-past timed extension.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** The G2 integration records accepted source/reused dependencies and aggregate coverage; its 68 current modules are not 68 new compilations.
- **Execution:** See the exact integration accounting; this board runs nothing.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** No unrestricted strong-Markov theorem or cross-source timed identification is inferred.

**Proof, review and other accepted-source links:**

- [Reconstructed G2 capabilities](https://github.com/Sodelin/Research-Commons/blob/207544deadd42be31cdb5062dfb32a15387fccab/research/2026-10-13-dot-g2-reconstructed-capabilities-0232z/README.md) (proof or status).
- [Unified integration and evidence accounting](https://github.com/Sodelin/Research-Commons/blob/207544deadd42be31cdb5062dfb32a15387fccab/research/2026-10-13-dot-g2-unified-integration-0238z/G2-UNIFIED-LAKE-INTEGRATION.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G2.PROJECTIVITY. **Aliases:** G2.

</details>

<a id="cb-g3-001"></a>
### Checking one proposed model is easier than ruling out every model
**CB-G3-001 · G3 · finding a real source**

**Question:** Can we check whether a proposed finite ancestry model fits exact observations?

**What we learned:** Yes. We can also search through finite models and eventually find one when a valid one exists.

**What it lets someone do:** Certify a fitting candidate rather than mistaking an approximation for an exact explanation.

**What we cannot conclude:** A search that has not found a model has not proved that no model exists.

**Kind:** algorithm. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** With a fixed admitted finite graph/word and rational or effectively algebraic joint input, shared original IDs, parameters and registers, exact feasibility reduces to real-closed-field constraints. Enumeration of admitted finite sources recognizes YES. This does not bound physical append count or ensure NO termination.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical real algebraic decision procedures are reused after deriving the original-source polynomial constraints.

**Our contribution.** Explicit original-source reduction to fixed-shape real-algebraic feasibility and a sound YES enumeration.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** General NO termination is CB-G3-004.

**Proof, review and other accepted-source links:**

- [Original exact criterion](https://github.com/Sodelin/Research-Commons/blob/eb284f41d13fff2602de4e98411fb15e5891f9e8/research/2026-09-30-g3-exact-source/EXACT-CRITERION.md) (proof or status).
- [Source-reachability reduction](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G3.FIXED_SOURCE_YES. **Aliases:** G3 fixed-source feasibility; G3 YES enumeration.

</details>

<a id="cb-g3-002"></a>
### A supplied observation certificate can bound the search
**CB-G3-002 · G3 · finding a real source**

**Question:** Can extra certified observations make the search finite?

**What we learned:** Yes, for a specified shared-routing branch and a sufficiently rich supplied certificate.

**What it lets someone do:** Turn that certified input into a bounded same-source recognition problem.

**What we cannot conclude:** Missing the certificate means 'not established', not 'no model exists'.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The COMMON supplied-exposure branch uses nonzero nonnegative sparse polynomials, exact zero expectations of the same legal mixed bank, exhaustive finite protected/tie grammar and collapse-preserving additional COMMON rows. The accepted certificate composition needs no supplied actual target source. Under its exact effective encoding it yields bounded witnesses and finite graph/RCF recognition.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Derive a bounded same-source witness from the supplied legal exposure certificate without requiring the actual target source as input.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Universal acquisition of such certificates and a full original parser/admission implementation are not delivered.

**Proof, review and other accepted-source links:**

- [Certificate-derived bounded witness](https://github.com/Sodelin/Research-Commons/blob/7cdbb35da93dc82ce5b8ddc8db91140537838774/research/2026-10-13-dot-certificate-bounded-witness-0223z/CERTIFICATE-DERIVED-BOUNDED-WITNESS-CANDIDATE.md) (proof or status).
- [Later acceptance](https://github.com/Sodelin/Research-Commons/blob/e9e31baf3767593ae6805924463c0bcb4fc08f0f/research/2026-10-13-dot-certificate-bounded-witness-0223z/INDEPENDENT-BOUNDED-WITNESS-REVIEW.md) (hand review).
- [Mandatory encoding clarification](https://github.com/Sodelin/Research-Commons/blob/e9e31baf3767593ae6805924463c0bcb4fc08f0f/research/2026-10-13-dot-certificate-bounded-witness-0223z/INPUT-ENCODING-CLARIFICATION.md) (proof or status).

**Connections:**
- [CB-G4-002](#cb-g4-002): **reused theorem**. Reuses the completed COMMON mechanism under its mandatory restrictions.

**Stable key:** original.G3.GIVEN_CERTIFICATE. 

</details>

<a id="cb-g3-003"></a>
### Some inputs allow us to acquire the needed certificate
**CB-G3-003 · G3 · finding a real source**

**Question:** Can the helpful certificate sometimes be found rather than handed to us?

**What we learned:** Yes, in accepted local branches with explicit nondegeneracy conditions.

**What it lets someone do:** Solve those cases using the real permitted observations.

**What we cannot conclude:** Failure of the local conditions does not settle all remaining cases.

**Kind:** algorithm. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The accepted quadratic acquisition theorem Q uses an actual legal complete joint COMMON receiver, an acquired algebraic predicate, finite charts/residues and strict-domain rank/curvature conditions. Regular and fixed-residue supplier branches are also retained by the review.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Prove an actual observation-based certificate-acquisition branch under its rank and curvature hypotheses.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Prove every realizable input enters an accepted acquisition branch, or supply another complete all-core mechanism.

**Proof, review and other accepted-source links:**

- [Quadratic acquisition acceptance](https://github.com/Sodelin/Research-Commons/blob/4a082a70ef5d604ffb2db89f988d88b6159f569d/research/2026-10-14-dot-g3-quadratic-acquisition-review-2313z/INDEPENDENT-REVIEW.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G3.LOCAL_ACQUISITION. 

</details>

<a id="cb-g3-004"></a>
### Can every exact input be decided?
**CB-G3-004 · G3 · finding a real source**

**Question:** Is there a method that always finishes and says whether any allowed finite ancestry model fits?

**What we learned:** That full question remains open in this register, despite the completed branches above.

**What it lets someone do:** Identify the precise missing step instead of rerunning already-solved special cases.

**What we cannot conclude:** Neither a failed search nor a fit to a limiting object proves a definitive answer.

**Kind:** question. **Mathematical status:** Open mathematical question.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** General G3 asks total recognition for all finite admissible rational/effectively algebraic joint inputs against every finite strict original source, with one graph, tuple and original-ID interpretation across all rows. A total input-computable bound on some witness, a complete NO mechanism, or an original-class impossibility theorem is still required.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** A precise remaining total-recognition obligation, with completed special branches separated from it.

**Evidence, kept separate:**

- **Hand:** The inspected acceptances do not discharge the full quantifiers; this is not a theorem of impossibility.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Close the total-decision obligation at the exact original source and finite-input interface.

**Proof, review and other accepted-source links:**

- [Original master statements](https://github.com/Sodelin/Research-Commons/blob/0c0dc21eed1046c405e86a92673a6d473a934b6d/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md) (proof or status).
- [Directed obligation audit](https://github.com/Sodelin/Research-Commons/blob/4a082a70ef5d604ffb2db89f988d88b6159f569d/research/2026-10-16-g3-g4-obligation-audit-1930z/OBLIGATION-AUDIT.md) (proof or status).

**Connections:**
- [CB-G3-001](#cb-g3-001): **reused theorem**. Completed positive search is a supplier, not a total decider.
- [CB-G3-002](#cb-g3-002): **candidate connection**. A complete certificate-acquisition theorem could extend this branch.

**Stable key:** original.G3.TOTAL_RECOGNITION. **Aliases:** G3 general.

</details>

<a id="cb-g4-001"></a>
### Some hidden information can be recovered by permitted tests
**CB-G4-001 · G4 · knowing when observations are enough**

**Question:** Can legal observations reveal the behaviour of a hidden piece of a model?

**What we learned:** Yes, in the specified finite-copy setting; a fixed four-taxon wrapper can recover a private chain's full forest response.

**What it lets someone do:** Use those observation adapters rather than assume hidden states are directly visible.

**What we cannot conclude:** This is not a stopping rule for every unknown-size model or every weaker measurement.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Finite-cap admitted testers span contextual responses after projection to the authorized channel. Separately, a private-randomness two-port chain used once in a fixed positive four-taxon wrapper has full forest kernels through M roots recovered from completed topology data using at most M+3 copies.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Linear observation spans and triangular inversion are established methods; the work supplies actual legal topology testers and padding adapters.

**Our contribution.** Legal finite-cap tester construction and a fixed-wrapper adapter recovering private full-forest kernels.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Unknown exteriors, multiport shared registers and weaker channels require their own adapters.

**Proof, review and other accepted-source links:**

- [Admitted testers, Theorem 5](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md) (proof or status).
- [Private-chain tomography](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-independent-bigon-1923z/TOMOGRAPHY-AND-COMPOSITION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.FINITE_OBSERVER. 

</details>

<a id="cb-g4-002"></a>
### Shared routing has a genuine stopping method
**CB-G4-002 · G4 · knowing when observations are enough**

**Question:** For one kind of ancestry routing, can we know when enough exact observations have been collected?

**What we learned:** Yes. The shared-routing branch has both a finite identification theorem and a terminating mathematical method.

**What it lets someone do:** Stop with a certificate under the stated exact-data and routing conditions.

**What we cannot conclude:** This is not a working experimental instrument or an algorithm for arbitrary approximate real numbers.

**Kind:** algorithm. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Whole-network COMMON targets and rivals are finite, strictly positive original sources with at least four taxa, full completed topology, a fixed finite routing-only menu and the same row configuration PMF across allocations. Finite forcing holds for real targets; observation-only stopping is effective with exact algebraic response/compiler encodings. Legal caterpillars expose finite directed-support grids; full-column independence, not a temporary rank plateau, supplies termination.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Finite positive-support moment/linear-algebra methods are antecedents. The new scope-specific work exposes the same finite COMMON law through actual legal observations and proves the stop.

**Our contribution.** Whole-network finite forcing and a terminating exact-algebraic COMMON stopping method, with mandatory scope corrections.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Implementation, finite-error access and transfer to the independent-routing-only menu are separate.

**Proof, review and other accepted-source links:**

- [Whole COMMON acceptance](https://github.com/Sodelin/Research-Commons/blob/d10564c0b7382a2214dd0ccc1139f4c8a3d3327b/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-WHOLE-COMMON-STOPPING-REVIEW.md) (hand review).
- [Mandatory scope correction](https://github.com/Sodelin/Research-Commons/blob/d10564c0b7382a2214dd0ccc1139f4c8a3d3327b/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/attempt-3/COMMON-ONLY-RECOGNITION-SCOPE-CLARIFICATION.md) (proof or status).
- [Finite-edge correction](https://github.com/Sodelin/Research-Commons/blob/d10564c0b7382a2214dd0ccc1139f4c8a3d3327b/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/attempt-3/FINITE-EDGE-COUNT-CORRECTION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.COMMON_EFFECTIVE. **Aliases:** G4 COMMON effective stopping.

</details>

<a id="cb-g4-003"></a>
### Two routing modes together need only finitely many exact tests
**CB-G4-003 · G4 · knowing when observations are enough**

**Question:** If we can observe both routing modes, can finitely many tests settle the whole model response?

**What we learned:** Yes, for every fixed admitted target, against all finite rivals, even without a preset rival-size limit.

**What it lets someone do:** Know that a finite distinguishing certificate exists for that target.

**What we cannot conclude:** Existence alone does not give a uniform procedure for finding the certificate.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** General natural BOTH finite forcing: each fixed strict binary rooted-LSA outer-labelled planar cut-child target with at least four taxa has a finite legal completed-topology certificate forcing its entire natural COMMON and INDEPENDENT law against all finite unknown-size original rivals using one source and physical tuple.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Finite-dimensional algebraic determination is classical; it applies only after the proof derives size control for every actual matching rival.

**Our contribution.** Derive actual rival-size control and semantic finite forcing against all finite unknown-size original rivals.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Uniform effective certificate production is separated in CB-G4-007.

**Proof, review and other accepted-source links:**

- [General BOTH acceptance](https://github.com/Sodelin/Research-Commons/blob/78bffa4904a4f56c9efc1d2ab3a18db13f65a982/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-NATURAL-BOTH-FINITE-FORCING-ACCEPTANCE.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.NATURAL_BOTH. 

</details>

<a id="cb-g4-004"></a>
### The result extends to qualifying extra tests
**CB-G4-004 · G4 · knowing when observations are enough**

**Question:** Can we add controls and shared programmes without losing the finite-certificate result?

**What we learned:** Yes, when the enlarged test menu satisfies two explicit requirements.

**What it lets someone do:** Reuse the finite-forcing theorem for those genuinely admitted menus.

**What we cannot conclude:** An arbitrary collection of controls is not automatically covered.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The menu contains the required finite natural BOTH certificate, and each bounded original shape compiles every legal outcome as a polynomial in one shared finite physical tuple. Then a finite certificate selected from that actual menu forces the whole menu law. The natural certificate bounds each actual matching rival, not merely a convenient equivalent representative; joint programme correlations remain joint.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Reuses natural BOTH forcing and bounded-shape polynomial response compilation; no arbitrary-menu prior theorem is assumed.

**Our contribution.** Extend finite forcing to authorized menus satisfying both interface hypotheses, preserving joint correlations.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Menus missing either hypothesis and a uniform algorithm are not covered.

**Proof, review and other accepted-source links:**

- [Qualified-menu acceptance](https://github.com/Sodelin/Research-Commons/blob/130799a9985e05227e5d3db87733e386277ba962/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-BOTH-INCLUSIVE-MENU-ACCEPTANCE.md) (hand review).
- [Menu-extension proof](https://github.com/Sodelin/Research-Commons/blob/130799a9985e05227e5d3db87733e386277ba962/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/NATURAL-BOTH-SIZE-CERTIFICATE-AND-MENU-EXTENSION.md) (proof or status).

**Connections:**
- [CB-G4-003](#cb-g4-003): **reused theorem**. Uses the natural BOTH actual-rival size certificate.

**Stable key:** original.G4.QUALIFIED_MENU. 

</details>

<a id="cb-g4-005"></a>
### All independent-routing answers determine all shared-routing answers
**CB-G4-005 · G4 · knowing when observations are enough**

**Question:** Would complete knowledge of independent routing also determine shared routing?

**What we learned:** Yes, in the original natural model class.

**What it lets someone do:** Transfer equality of the entire independent observation law to the shared law.

**What we cannot conclude:** This does not say that a finite independent sample of answers is enough.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Entire natural INDEPENDENT-law equality implies entire natural COMMON-law equality for strict original finite sources and shared physical tuples. The acceptance includes fair mixed arms, repeated cuts, ancestral alignment and the opaque-upper interface, not only static routing. It adds no externally correlated shared register.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Earlier static-routing special cases are superseded by the later accepted full original-source transfer, including current-root routing and ancestral alignment.

**Our contribution.** Prove complete independent-law equality determines complete shared-law equality in the original natural class.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** The finite-prefix version is CB-G4-008.

**Proof, review and other accepted-source links:**

- [General all-law acceptance](https://github.com/Sodelin/Research-Commons/blob/125360b75c9fad294e1ca737834e9bed4117e83e/research/2026-10-13-codex-g4-renewed/critical-review/ROOT-GENERAL-ALL-LAW-COMMONIZATION-ACCEPTANCE.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.ENTIRE_I_TO_C. 

</details>

<a id="cb-g4-006"></a>
### The algebraic search reduction is already complete
**CB-G4-006 · G4 · knowing when observations are enough**

**Question:** Is there a clean way to turn the remaining stopping question into a certificate-production question?

**What we learned:** Yes, with the exact algebraic interface. That reduction should be reused, not treated as another gap.

**What it lets someone do:** Focus effort on the genuinely missing certificate supplier.

**What we cannot conclude:** The reduction does not itself produce that supplier.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Under polynomial source responses, semialgebraic strict admission/data over the real algebraic field, effectively enumerable legal algebraic tests and exact response encodings, one algebraic tuple on the same graph preserves the entire algebraic profile. Observation-only stopping O is equivalent to uniform supplied-algebraic-source forcing D.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Real algebraic/semialgebraic methods are prior work. The contribution is all-profile descent and the exact effective-interface equivalence.

**Our contribution.** Prove all-profile algebraic candidate coverage and the exact O⇔D reduction.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** The uniform D algorithm beyond completed branches remains CB-G4-007.

**Proof, review and other accepted-source links:**

- [Accepted descent and stopping reduction](https://github.com/Sodelin/Research-Commons/blob/9c8ddb18d83f6d3a50bc94451e76bf658d0dd9f5/research/2026-10-09-dot-full-attempt-wave-0542z/g4-forcing/INDEPENDENT-CONSTRUCTION-LANE-REVIEW.md) (hand review).
- [Mandatory exterior-interface clarification](https://github.com/Sodelin/Research-Commons/blob/9c8ddb18d83f6d3a50bc94451e76bf658d0dd9f5/research/2026-10-09-dot-full-attempt-wave-0542z/g4-forcing/ALGEBRAIC-EXTERIOR-INTERFACE-CLARIFICATION.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G4.ALGEBRAIC_DESCENT. 

</details>

<a id="cb-g4-007"></a>
### The broader automatic certificate finder is still missing
**CB-G4-007 · G4 · knowing when observations are enough**

**Question:** Beyond the completed shared-routing case, can one method always find the required finite certificate?

**What we learned:** The inspected results do not yet supply that method.

**What it lets someone do:** Keep a precise algorithmic target without denying the existing existence theorems.

**What we cannot conclude:** A proof that some finite certificate exists is not automatically a way to find it uniformly.

**Kind:** question. **Mathematical status:** Open mathematical question.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Uniform D must be one terminating algorithm taking any supplied algebraic source and returning a finite certificate sound against all unknown-size real rivals under the declared effective interface. The accepted O⇔D reduction and all-profile algebraic coverage do not supply D outside completed branches.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Keep the missing uniform effective supplier distinct from already-proved algebraic coverage.

**Evidence, kept separate:**

- **Hand:** Exact obligation separated by the accepted reduction and later acceptance-first audit.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Supply D, or a valid impossibility result at this exact effective interface.

**Proof, review and other accepted-source links:**

- [Reduction and exact effective obligation](https://github.com/Sodelin/Research-Commons/blob/9c8ddb18d83f6d3a50bc94451e76bf658d0dd9f5/research/2026-10-09-dot-full-attempt-wave-0542z/g4-forcing/ALL-PROFILE-DESCENT-AND-GLOBAL-CERTIFICATE-ATTEMPT.md) (proof or status).

**Connections:**
- [CB-G4-006](#cb-g4-006): **reused theorem**. Completed equivalence fixes the required supplier.

**Stable key:** original.G4.UNIFORM_EFFECTIVE_FORCING. 

</details>

<a id="cb-g4-008"></a>
### Finite independent-routing tests are the main unresolved branch
**CB-G4-008 · G4 · knowing when observations are enough**

**Question:** Can finitely many independent-routing tests do what all such tests can do?

**What we learned:** That exact step remains unresolved.

**What it lets someone do:** State a decisive goal rather than confusing approximation or changing examples with a solution.

**What we cannot conclude:** Neither full-law determination nor the two-mode theorem already answers it.

**Kind:** question. **Mathematical status:** Open mathematical question.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For each fixed strict original target T, require a finite legal independent panel J_T such that every finite admitted rival N with I(N)|J_T=I(T)|J_T also matches the target's finite COMMON certificate C_T. The same N and tuple must satisfy every row; rival size is not bounded in advance. A negative result must keep one fixed T and give an exact later-inequivalent strict finite rival after every finite I panel.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** State the exact finite independent-only implication and its fixed-target negative alternative.

**Evidence, kept separate:**

- **Hand:** The acceptance-first audit distinguishes this missing finite implication from completed entire-law transfer.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Prove the finite J_T implication or construct the stated fixed-target exact negative alternative.

**Proof, review and other accepted-source links:**

- [Exact finite-bridge equivalence](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/FINITE-INDEPENDENT-BRIDGE-EXACT-EQUIVALENCE.md) (proof or status).

**Connections:**
- [CB-G4-002](#cb-g4-002): **reused theorem**. Supplies the target COMMON certificate.
- [CB-G4-003](#cb-g4-003): **reused theorem**. Supplies completed BOTH finite forcing.
- [CB-G4-005](#cb-g4-005): **reused theorem**. Supplies entire-I-to-C transfer, not finite extraction.

**Stable key:** original.G4.FINITE_I_ONLY. **Aliases:** G4 finite I-only.

</details>

<a id="cb-g5-001"></a>
### Small timed panels recover particular ancestry features
**CB-G5-001 · G5 · recoverable ancestry features**

**Question:** Which features can small samples identify reliably in the exact model?

**What we learned:** The accepted three-tip result recovers specified collections of ancestry clusters and splits.

**What it lets someone do:** Target features that the observation law actually determines.

**What we cannot conclude:** It does not reconstruct every hidden graph detail or every parameter.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Full binary M3 theorem for temporal binary LSA networks with positive child bridges, positive rates/durations, interior inheritance and contemporaneous tips, at least three taxa: timed three-tip panels determine normalized rooted-cluster and nontrivial-split unions. This is a union target, not tree co-occurrence. Earlier fair M2 normalized-quartet/sharpness results remain separate prior components.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Earlier fair M2 normalized-quartet/sharpness work is retained; the M3 result is a distinct broader target theorem under its timed binary class.

**Our contribution.** Full binary M3 identification of the stated cluster/split unions with the accepted selected formal package.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** The linked package records accepted endpoint and 319-module certificate; not a whole-repository build.
- **Execution:** Build evidence is preserved in the linked release; no new execution here.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Whole-graph/parameter recovery and outside-class targets require separate claims.

**Proof, review and other accepted-source links:**

- [Full binary M3 package](https://github.com/Sodelin/Research-Commons/blob/81ff60aa0ffe6c39e15546b09105f3c3fafbd1ed/research/2026-10-10-dot-g5-full-binary-m3-0209z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G5.BINARY_M3. **Aliases:** G5 full binary M3.

</details>

<a id="cb-g5-002"></a>
### Bounded hidden branching has a larger-panel hand theorem
**CB-G5-002 · G5 · recoverable ancestry features**

**Question:** What if the allowed hidden branching is larger?

**What we learned:** A hand-proved panel bound extends the feature-recovery result under a stated branching limit.

**What it lets someone do:** Use the appropriate larger sample panel in that mathematical class.

**What we cannot conclude:** Full formal assembly and proof of the best possible panel size are different unfinished tasks.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For the declared hidden-routing class with hybrid indegree at most k, the hand theorem uses M_(k+1) timed panels to recover the normalized cluster/split union target at all sizes. It does not assert optimality of this cap.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Builds on the programme's timed cluster/split recovery framework; formal assembly and optimality are not silently assumed.

**Our contribution.** Extend the hand feature-recovery theorem to bounded hybrid indegree using M_(k+1) panels.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Complete full formal assembly and separately resolve optimality; the hand theorem is not mathematically open merely because formalization is incomplete.

**Proof, review and other accepted-source links:**

- [Bounded-indegree hand theorem](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-sol61-head-audit-1956z/G5-HIDDEN-AMBIGUITY-BOUNDED-INDEGREE.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G5.BOUNDED_INDEGREE. **Aliases:** HG; bounded hidden-routing G5.

</details>

<a id="cb-g6-001"></a>
### Certify only what every compatible model agrees on
**CB-G6-001 · G6 · honest conclusions from uncertain data**

**Question:** How can we avoid overstating what uncertain data tell us?

**What we learned:** A completed mathematical characterization says when a conclusion survives every compatible admitted model.

**What it lets someone do:** Return a justified certificate or honestly leave the answer unresolved.

**What we cannot conclude:** It does not guarantee that every dataset will yield a useful answer or solve exact source existence.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Completed hand characterization for positive binary rooted-LSA cut-child networks, not requiring planarity, n≥4, finite profiles and natural shared-source modes/control budgets: effective closure clouds and robust target fibres determine finite-data certification. Completed-cell law/TV formal consumers cover selected parts, not the full source assembly. The accepted algorithm specification includes both Hausdorff approximation directions and exact emptiness; an unexecuted full catalogue engine is not a missing mathematical supplier.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical confidence sets, inverse images and robust certification are antecedents; the contribution binds them to the declared original source and target.

**Our contribution.** Original-source nonplanar closure/cloud/robust-fibre characterization and algorithm specification; selected formal consumers are separate.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Selected completed-cell/TV consumers have scoped 233/236-module audits. Full source/compiler/QE assembly is not claimed.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Full formal/native assembly remains; this does not reopen the accepted hand characterization.

**Proof, review and other accepted-source links:**

- [Nonplanar finite-certification theorem](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md) (proof or status).
- [Selected completed-cell TV formal package](https://github.com/Sodelin/Research-Commons/blob/de3011fa352e04f9be64cf9f4da8a5528cad68db/research/2026-10-10-dot-g6-completed-cell-tv-0258z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G6.FINITE_CERTIFICATION. **Aliases:** G6.

</details>

<a id="cb-g7-001"></a>
### Choose tests with a proof of what their answers can establish
**CB-G7-001 · G7 · choosing informative tests**

**Question:** Can a testing plan be chosen systematically rather than by guesswork?

**What we learned:** Yes, in the declared finite exact-law design setting, the hand theorem produces a certified policy or a resource lower certificate.

**What it lets someone do:** Compare testing plans and their costs under one consistent model family.

**What we cannot conclude:** It does not automatically give a cheap computation, an experimental sample budget, or a verified native programme.

**Kind:** algorithm. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Complete finite original-ID registry, fixed finite unranked readouts, shared-source semialgebraic affine exact-law programmes and reset/deletion-closed trajectory costs admit an exact real-algebraic CAD policy/Pareto construction or lower certificate. Full source compiler, response/history/QE and AST-to-CorrectRun assembly remain distinct formal obligations. The hand master already supplies the actual-source census, joint polynomial compiler, rank/deletion argument and CAD winning-fibre selection. Missing full formal/native composition is not missing hand mathematics.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical exact real algebraic decision methods, adaptive decision games and experimental design are reused with the original source/resource contract.

**Our contribution.** Original-source exact-law design theorem and its actual census/compiler/CAD construction, plus selected accepted formal strategy components.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Earlier pinned-native accepted1591 includes rank compression, original-family strategy, full-epoch coefficients, repaired whole-edge chain, executable coefficient/support, sparse word/completion and raw calendar support, with a scoped 191-module recovery audit. The later hosted Lean 4.35 variant is additional evidence, not the first acceptance. Endpoints retain every-source CorrectRun, affine equality, deletion legality and exact-history premises.
- **Execution:** No execution result is needed or claimed for this mathematical statement.
- **Empirical:** This is not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Full formal/native assembly, not a new proof of the completed hand characterization.

**Proof, review and other accepted-source links:**

- [Exact G7 master review](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md) (proof or status).
- [Scoped hosted game/rank check](https://github.com/Sodelin/Research-Commons/blob/8a96bb015b6cb88df196d6897b5437344a09238b/research/2026-10-21-lean-rust-solver-builder/evidence/G7-GAME-RANK-HOSTED-REVIEW.json) (formal receipt).
- [Accepted1591 incorporation catalogue and supersessions](https://github.com/Sodelin/Research-Commons/blob/dffb0b501c378c67e4aeea0561a68052e064e8ba/research/2026-10-11-dot-discovery-lean-incorporation-catalog-2200z/G5-G6-G7-INCORPORATION-CATALOG.md) (formal inventory).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** original.G7.EXACT_DESIGN. **Aliases:** G7; MG2 (view, not new master).

</details>

<a id="cb-causal-001"></a>
### Some causal questions can be answered with limited experiments
**CB-CAUSAL-001 · Causal discovery · restricted interventions**

**Question:** If we can intervene on only selected variables, what can we learn about cause and effect?

**What we learned:** The scoped theorem gives a finite plan for recovering the chosen causal summary.

**What it lets someone do:** Count the exact population-level questions required under the stated model.

**What we cannot conclude:** This is not a guarantee about noisy samples, fast computation or every hidden-variable model.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For finite acyclic DAGs with binary-valued variables, arbitrary finite original latent/selection carriers, selection sinks, one common positive rational binary registry, separate soft single-target interventions and the specified faithful physical-source class, the exact marked TCM class is recoverable using B=k(n−1)+Σ_{unordered{x,y}}2^{|U\{x,y}|}+Σ_{t∈T,x≠t}2^{|U\{x}|} elementary population CI/invariance queries, with 2B≤5n(n−1)2^u. All targets share one physical source. Binary-valued does not mean binary-degree.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** HPL anterior/TCM framework; Sadeghi stable-graph realization; Meek binary faithfulness; classical latent projection and population-query methods. Zhou–Kocaoglu's later no-selection completion is prior progress, not erased by this task.

**Our contribution.** Construct a common faithful physical binary source for the required tests and a proved G7 adapter, yielding the stated restricted-intervention upper bound.

**Evidence, kept separate:**

- **Hand:** Coordinating AI review covers the 132-module upper body with explicit exclusions, not a build.
- **Formal:** Full Lean source proposal is preserved; no kernel acceptance.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Formal elaboration and statistical acquisition remain separate; finite postprocessing is not asserted polynomial time.

**Proof, review and other accepted-source links:**

- [Full upper hand review](https://github.com/Sodelin/Research-Commons/blob/174168effef1efc5be13d941814c51520de9a8cb/research/2026-10-22-dot-restricted-causal-interventions/CAUSAL-FULL-UPPER-CUMULATIVE-HAND-REVIEW-20261023.md) (hand review).
- [Programme and prior-work boundaries](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/README.md) (proof or status).

**Connections:**
- [CB-G7-001](#cb-g7-001): **proved adapter**. Accepted hand source-to-response/history/resource-game adapter instantiates G7; Lean source remains unelaborated.

**Stable key:** causal.RESTRICTED_UPPER. 

</details>

<a id="cb-causal-002"></a>
### Some exact causal tasks really require many tests
**CB-CAUSAL-002 · Causal discovery · restricted interventions**

**Question:** Could a clever strategy avoid nearly all those questions?

**What we learned:** A constructed family forces many paid questions, even for the stated randomized strategies.

**What it lets someone do:** Know a genuine limit for this exact question-and-answer model.

**What we cannot conclude:** This is not a lower bound on laboratory samples or every type of intervention.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For k>0,u≥2 let M=binom(u,2)2^(u−2). The physical class has deterministic lower bound M; an explicit M+1-source promise has exact optimum M. Arbitrary measurable random seeds with error ≤ε on every admitted source, 0≤ε<1/2, require extended expected paid queries ≥M(1−2ε) on one fixed baseline. Nontermination is failure; infinite expectation is allowed.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical distinguishing-query/adversary lower bounds and accepted G7 resource-game suppliers; the contribution realizes the necessary laws in one admitted physical causal family.

**Our contribution.** Realize a common physical hard family and transfer deterministic and arbitrary-seed randomized lower bounds through the exact query/cost interface.

**Evidence, kept separate:**

- **Hand:** Coordinating AI review covers 13 additional lower bodies and named G7 suppliers.
- **Formal:** Deterministic/randomized source is not compiler or kernel acceptance.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Formal acceptance; no lower bound outside this query/physical-source class is inferred.

**Proof, review and other accepted-source links:**

- [Lower hand-review receipt](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/CAUSAL-LOWER-CUMULATIVE-HAND-REVIEW-20261023.md) (hand review).
- [Accepted lower scope](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/V54-LOWER-HAND-ACCEPTANCE-AND-API.md) (proof or status).

**Connections:**
- [CB-G7-001](#cb-g7-001): **proved adapter**. Physical hard sources and resource histories instantiate the G7 lower-certificate interface.

**Stable key:** causal.PHYSICAL_LOWER. 

</details>

<a id="cb-causal-003"></a>
### No target means this particular task needs no questions
**CB-CAUSAL-003 · Causal discovery · restricted interventions**

**Question:** Does the large lower bound apply when there are no intervention targets?

**What we learned:** No. The chosen target then has only one possible value.

**What it lets someone do:** Avoid extending the nontrivial lower theorem beyond its assumptions.

**What we cannot conclude:** This does not trivialize all observational causal discovery.

**Kind:** counterexample. **Mathematical status:** Named overextension refuted.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For k=0 the literal TCM-union target is the empty graph, so its target class is a singleton and query complexity is zero. This refutes extension of CB-CAUSAL-002 to k=0, not its k>0 statement.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Correct the empty-target overextension with the exact zero-query case.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Correction/source preserved without new kernel run.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Keep k>0 explicit.

**Proof, review and other accepted-source links:**

- [Corrected scope](https://github.com/Sodelin/Research-Commons/blob/f300a67ccef954d0935a6e2a7a87389317fbb599/research/2026-10-22-dot-restricted-causal-interventions/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** causal.EMPTY_TARGET_CORRECTION. 

</details>

<a id="cb-lineage-001"></a>
### A best-fit score does not reveal every developmental link
**CB-LINEAGE-001 · Developmental lineage · scores and hidden histories**

**Question:** If two developmental maps always get the same score, must they be the same map?

**What we learned:** No. The studied score sees some reachability information but can miss direct links.

**What it lets someone do:** Understand exactly what that score distinguishes.

**What we cannot conclude:** A score tie does not prove that two models generate the same biological measurements.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For ε=0 unweighted Carta sampling score, rooted unique-potency DAGs labelled by nonempty subsets of observed cell types and the specified multifurcating typed-tree menu, the full score signature determines exactly the potency-vertex family and reachability, not direct edges. A seven-cell example has a unique optimal progenitor family that changes after leaf deletion.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Sashittal and colleagues' Carta (Nature Methods, DOI 10.1038/s41592-025-02903-z) supplies the optimization problem and prior optimal-label results. Later Pilarski–Stadler–Seidel work (DOI 10.1371/journal.pcbi.1014370) already studies joint tree/rate inference for fixed four-type star/chain structures, so Carta's historical future-work sentence is not a current blanket open claim.

**Our contribution.** Characterize the deterministic score's exact quotient and give a leaf-restriction counterexample for optimal progenitor families.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Statistical identification needs a specified stochastic forward/observation model.

**Proof, review and other accepted-source links:**

- [Score-interface theorem and review](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/README.md) (proof or status).

**Connections:**
- [CB-G3-004](#cb-g3-004): **same principle**. Similar inverse-information issue, not original G3 theorem reuse.
- [CB-G4-008](#cb-g4-008): **same principle**. Similar observation-versus-hidden-structure distinction, not a G4 extension.

**Stable key:** lineage.SCORE_QUOTIENT. 

</details>

<a id="cb-lineage-002"></a>
### Different hidden graphs can give identical observed trees
**CB-LINEAGE-002 · Developmental lineage · stochastic observation limits**

**Question:** Can different hidden transition graphs produce the same observed family trees?

**What we learned:** Yes, in an explicitly constructed stochastic model.

**What it lets someone do:** Test identification claims against an exact law-level example rather than just a score tie.

**What we cannot conclude:** This does not settle every biological division model or refute papers with different starting-state assumptions.

**Kind:** counterexample. **Mathematical status:** Counterexample proved at stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** A multitype branching change-of-basis construction preserves the full sampled timed event-tree law, also after a common neutral inherited-barcode kernel. A fixed-root-3 parent-retaining-birth example has five versus six transition edges. State-preserving division Xi→2Xi, equality from every labelled hidden start, observation-minimality and contradiction of the cited strong-HE theorem are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical multitype branching change-of-basis and lumping ideas are antecedents. Paired initial distributions versus every labelled hidden start are distinguished; the construction is not certified as a contradiction of prior strong-HE claims.

**Our contribution.** Construct and prove an exact sampled-law equality for distinct transition graphs in an explicitly labelled stochastic model.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Unknown graph identification under original state-preserving cell-division assumptions remains separate.

**Proof, review and other accepted-source links:**

- [Exact-law construction](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/STOCHASTIC-GRAPH-OBSTRUCTION.md) (proof or status).
- [Fixed-root specialization](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/PARENT-RETAINING-BIRTH-SPECIALIZATION.md) (proof or status).
- [Quantifier audit](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/QUANTIFIER-AUDIT.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** lineage.STOCHASTIC_GRAPH_OBSTRUCTION. 

</details>

<a id="cb-lineage-003"></a>
### The actual tree-refinement problem is computationally hard
**CB-LINEAGE-003 · Developmental lineage · optimization complexity**

**Question:** Is there an easy general way to choose the best detailed branching tree?

**What we learned:** The specified scoring problem is NP-hard, even in a restricted star-map case.

**What it lets someone do:** Understand why a general exact optimizer may need expensive search; use the supplied subset method for small cases.

**What we cannot conclude:** This does not mean every instance is difficult or that a best fit identifies biological truth.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For the actual D_λ objective over all binary joining refinements of arbitrary composite child clades, caterpillar exchange and anchors yield OPT=C0+OPT_MSSC−N. Star-map labels are all S and resolution cost is zero, so hardness holds for every fixed λ with unbounded types/degree. A full exact subset-DP recurrence is supplied. The operational formal endpoint remains separate.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Feige–Lovász–Tetali minimum-sum set cover hardness is the classical reduction source. Earlier polytomy optimization and Carta's objective retain attribution.

**Our contribution.** Prove hardness for the actual D_λ refinement objective, including arbitrary composite children, and supply the exact subset recurrence.

**Evidence, kept separate:**

- **Hand:** Full caterpillar/anchor/threshold reduction and subset recurrence independently checked, not just examples.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Historical novelty and the operational formal endpoint are separate; see CB-LINEAGE-005.

**Proof, review and other accepted-source links:**

- [Full complexity proof](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-REFINEMENT-COMPLEXITY.md) (proof or status).
- [Independent hand review](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-REVIEW-20261022-0712Z.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** lineage.POLYTOMY_COMPLEXITY. 

</details>

<a id="cb-lineage-004"></a>
### An explicit mathematical checking algorithm has been written
**CB-LINEAGE-004 · Developmental lineage · explicit mathematical checker**

**Question:** Is there a precise checker for these restricted optimization certificates?

**What we learned:** A complete proposed mathematical algorithm and proof source have been written.

**What it lets someone do:** Inspect the acceptance rules, rejection of malformed input, time bound and answer format.

**What we cannot conclude:** It has not been compiled or kernel-verified, and it is not a Rust binary running on hardware.

**Kind:** algorithm. **Mathematical status:** Complete proof-source proposal, not yet formally accepted.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The 197-module proposal supplies a fixed abstract TM2 checker for the restricted marked-star encoded language: all-word grammar, bounded header, one shared decoded witness, cell/clade/uniqueness guards, root-inclusive original score, budget clipping, rejection preservation, cleanup and exact one-bit halt with polynomial time/all-tape bounds. Its proposed endpoint is VerifierMachineWitness.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Write the complete restricted all-word mathematical checker and proposed correctness/resource proof source, while keeping its unverified status explicit.

**Evidence, kept separate:**

- **Hand:** 35 selected semantic bodies at ac54cf plus a separate bound/clean-halt review at 27fb172 found no concrete defect; not a full 197-module review.
- **Formal:** A certificate is candidate evidence; a verifier checks it; a kernel proof would validate the verifier theorem. Native implementation/refinement is another obligation.
- **Execution:** No compiler or checker execution claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Elaborate the exact closure, repair failures, inspect actual endpoint axioms and separately validate any native implementation.

**Proof, review and other accepted-source links:**

- [Complete verifier source handoff](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-COMPLETE-RESTRICTED-VERIFIER-SOURCE.md) (proof or status).
- [Source endpoint](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedAlgorithmsSourceEndpoint.lean) (proof source).

**Connections:**
- [CB-LINEAGE-003](#cb-lineage-003): **candidate connection**. Implements the restricted certificate language, pending formal acceptance.

**Stable key:** lineage.RESTRICTED_VERIFIER_SOURCE. 

</details>

<a id="cb-lineage-005"></a>
### The formal hardness connection is still missing
**CB-LINEAGE-005 · Developmental lineage · formal complexity endpoint**

**Question:** Would verifying that checker finish the formal complexity proof?

**What we learned:** No. The encoded hardness connection is a separate missing part.

**What it lets someone do:** Track both obligations without declaring completion from a checker alone.

**What we cannot conclude:** Archive metadata or an informally similar theorem is not a verified usable import.

**Kind:** question. **Mathematical status:** Formal dependency still missing.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** EncodedSourceHardness needs a closed operational hardness supplier at the exact encoding/machine interface and an all-word SAT→X3C/normalizer/serializer→MSSC chain. Registered Cook–Levin closure metadata plus actual composer source identify a candidate binding, but the generated closed endpoint and its actual axiom report were not obtained/verified. Clean-store operational refinement and version alignment are separate.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Bind the prospective operational hardness supplier to exact source/encoding requirements and preserve the independently missing reduction.

**Evidence, kept separate:**

- **Hand:** Candidate checked with limitations; not a closed accepted hardness supplier.
- **Formal:** VerifierMachineWitness and EncodedSourceHardness remain independent final premises.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Validate the exact closed supplier and prove faithful operational reduction without assuming an extra axiom.

**Proof, review and other accepted-source links:**

- [Registered closure crosscheck](https://github.com/Sodelin/Research-Commons/blob/c2650a5d8afc0be75cc8141f9f30d0907e961425/research/2026-10-22-dot-developmental-lineage-score-interface/POLYTOMY-REGISTERED-COOK-CLOSURE-CROSSCHECK-20261023.md) (proof or status).

**Connections:**
- [CB-LINEAGE-003](#cb-lineage-003): **same principle**. Hand reduction is the mathematical target, not already an operational formal theorem.
- [CB-LINEAGE-004](#cb-lineage-004): **candidate connection**. Validated checking gives membership, not hardness.

**Stable key:** lineage.ENCODED_HARDNESS_GAP. 

</details>

<a id="cb-phy-001"></a>
### A root region can be replaced without changing the stated output
**CB-PHY-001 · Phylogenetics · simplifying a network**

**Question:** Can part of a phylogenetic network be simplified without changing its sequence-model response?

**What we learned:** Yes, for the stated two-boundary region and model families.

**What it lets someone do:** Use a smaller equivalent representation while keeping exterior parameters fixed.

**What we cannot conclude:** This does not show every root can move anywhere or every network becomes a binary tree.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** A maximal binary root region with exactly two boundary edge occurrences is replaceable by a retained-port fork preserving both cut matrices and fixed exterior parameters, with positive inheritance. Degree-two ports remain. Distinct domains: open H with invariant root law; Fourier JC/K2P/K3P with uniform root and literal zeros; strict-positive-rate continuous-time K2P using its actual exponential. Zero-rate K2P and general continuous-time K3P are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Prior root-blob equivalence questions and standard Markov cut-factorization, group-based Fourier channels and continuous-time exponentials are antecedents. The proof repairs the boundary/model contract rather than claiming universal root movement.

**Our contribution.** Give a direct cut-factorization retained-port proof and separate faithful suppliers for the admitted open, Fourier and continuous-time model domains.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Proof-source packets preserved without compiler acceptance.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Broader subblob/single-edge/root-placement statements require separate proof.

**Proof, review and other accepted-source links:**

- [Direct proof](https://github.com/Sodelin/Research-Commons/blob/ae8a2874f391f7d8f31d9fb4454c47aae6fe9916/research/2026-10-22-dot-phylogeny-root-blob/RETAINED-PORT-DIRECT-PROOF.md) (proof or status).
- [Restricted-model source handoff](https://github.com/Sodelin/Research-Commons/blob/d6394f0a090466afff39881fabbbfd7c1fe6c49a/research/2026-10-22-dot-phylogeny-root-blob/RETAINED-PORT-RESTRICTED-SOURCE-HANDOFF.md) (proof or status).

**Connections:**
- [CB-G1-001](#cb-g1-001): **same principle**. Both preserve specified observations under simplification; exact G1 theorem reuse is not established.

**Stable key:** phylogeny.RETAINED_PORT. 

</details>

<a id="cb-rxn-001"></a>
### Finite features identify one scalar reaction-model class
**CB-RXN-001 · Reaction networks · partial observation**

**Question:** Can finite information settle a scalar reaction model against larger rivals?

**What we learned:** Yes, in the stated fixed-start autonomous scalar class.

**What it lets someone do:** Use a finite exact identification result without presuming a rival-size limit.

**What we cannot conclude:** It is not a practical finite-data procedure or a theorem about every hidden reaction network.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For autonomous scalar stopped laws, all finite scalar rivals share the positive start, observable interval and stopping convention. 3r+1 invariants suffice, or 2r+1 for unit births. A class-specific observation adapter connects the stochastic law to classical positive finite-moment determination.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Positive finite-moment uniqueness is classical and reused, not newly claimed.

**Our contribution.** Prove the fixed-start stopped-law-to-positive-moment adapter and finite invariant count for the actual scalar source class.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Effective finite experimental access and unrestricted hidden reaction models remain outside scope.

**Proof, review and other accepted-source links:**

- [Fixed-start scalar adapter](https://github.com/Sodelin/Research-Commons/blob/4f954e531ba7014ab49ba357cd1e68fef6472922/research/2026-10-22-dot-reaction-partial-observation/FIXED-START-SCALAR-MOMENT-ADAPTER.md) (proof or status).

**Connections:**
- [CB-CM-001](#cb-cm-001): **reused theorem**. Positive moment theorem applies after the stochastic observation adapter.
- [CB-G4-008](#cb-g4-008): **same principle**. Similar inverse-fibre question, not the ancestry source class.

**Stable key:** reaction.SCALAR_MOMENTS. 

</details>

<a id="cb-rxn-002"></a>
### Two tempting identification shortcuts fail
**CB-RXN-002 · Reaction networks · partial observation**

**Question:** Do local derivatives or a short reaction list guarantee an adequate observation model?

**What we learned:** No. Explicit examples defeat those two shortcuts.

**What it lets someone do:** Avoid using them as universal identification proofs.

**What we cannot conclude:** They do not prove all partial-observation identification impossible.

**Kind:** counterexample. **Mathematical status:** Named shortcuts refuted.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** One hidden-stop example has equal all-order interior initial generator/bracket jets but different observed held laws. Separately, one reaction has unbounded two-time feature rank, so finite chemistry need not have finite linear observable rank. These are distinct named-route obstructions.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical generator-jet and finite-rank identification strategies are the named routes being tested. Their failure here does not refute unrelated identification methods.

**Our contribution.** Construct source-faithful counterexamples to two precisely named observation shortcuts.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Original inverse problem still needs a source-faithful observation/realization argument.

**Proof, review and other accepted-source links:**

- [All-order hidden-stop obstruction](https://github.com/Sodelin/Research-Commons/blob/2113d9d8ca82d40022a37070172a76267427920e/research/2026-10-22-dot-reaction-partial-observation/HIDDEN-STOP-ALL-ORDER-JET-OBSTRUCTION.md) (proof or status).
- [Observable-rank obstruction](https://github.com/Sodelin/Research-Commons/blob/4c0ec491a10eda3cf809dd685b67467c8369b5fd/research/2026-10-22-dot-reaction-partial-observation/NONLOCAL-REALIZATION-ATTACK.md) (proof or status).

**Connections:**
- [CB-G3-004](#cb-g3-004): **same principle**. Similar realization pitfalls, different source classes.

**Stable key:** reaction.OBSERVATION_SHORTCUTS. 

</details>

<a id="cb-rxn-003"></a>
### One hidden observation problem reduces to a survival response
**CB-RXN-003 · Reaction networks · partial observation**

**Question:** Can a hidden-reaction observation problem be reduced to one exact response?

**What we learned:** Yes, in the specified construction it is equivalent to a hidden first-exit survival response.

**What it lets someone do:** Focus the remaining question on which responses finite chemical models can realize.

**What we cannot conclude:** This is not yet that realization classification or a result for every reaction network.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For the specified embedded independent-block construction, fixed initial state and original full-state stopping, equality of continuous observed held-path laws is equivalent to equality of the actual hidden-diffusion first-exit survival response censored at the stated horizon.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** First-exit/survival laws and observation pushforwards are classical; the source-specific two-way equality adapter is the contribution.

**Our contribution.** Prove an if-and-only-if observation adapter to the actual hidden first-exit survival response under unchanged fixed-start stopping.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result is needed or claimed.
- **Empirical:** Not a claim about measured biological or physical data.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Classify finite hidden chemical realizations of the response; unrestricted original master remains open.

**Proof, review and other accepted-source links:**

- [Survival adapter review](https://github.com/Sodelin/Research-Commons/blob/dfda007ccd8d46d77bd3ea789459de316900c65b/research/2026-10-22-dot-reaction-partial-observation/HIDDEN-EXIT-SURVIVAL-COORDINATING-REVIEW.md) (hand review).

**Connections:**
- [CB-G3-004](#cb-g3-004): **same principle**. Same inverse-fibre viewpoint, not a reduction to original G3.
- [CB-G4-008](#cb-g4-008): **same principle**. Finite determination is still class-specific.

**Stable key:** reaction.HIDDEN_SURVIVAL. 

</details>

<a id="cb-phys-p1-001"></a>
### We have better upper and lower limits on the testing cost
**CB-PHYS-P1-001 · Physics P1 · testing quantum states**

**Question:** How many copies of two quantum systems are needed to tell whether their states differ?

**What we learned:** Reviewed results improve both a sufficient copy budget and necessary budgets, but the best limits still do not match.

**What it lets someone do:** Benchmark proposed testing methods against explicit mathematical bounds.

**What we cannot conclude:** These are not a ready laboratory protocol, efficient preparation or a solved optimal-cost question.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Unknown N-qubit Gibbs states have the same known β and at-most-k-local nonidentity Pauli coefficients individually bounded by one; degree and per-site total strength are not bounded. Collective upper: O((M log(2+βM/ε)+log(1/δ))/ε²), M=Σ_{j=1}^k3^j binom(N,j), unrestricted computation. For k≥5, ε≤1/4096, fixed-β lower32 is Ω(N^a/(log N)^(a/(k−1))), a=min((2k+2)/3,(4k−1)/5), counting every auxiliary spin.

**Origin.** published open problem. Motivated by the optimal local Gibbs-state certification question in Bluhm et al.; these particular bounds are project contributions, not a claim to solve the whole published question. [Primary source](https://arxiv.org/html/2603.29809v1#S1.SS3).

**Prior work.** The source already provides an efficient single-copy protocol (Theorem 17). Classical quantum testing/learning compositions and admitted diagonal hard families are credited.

**Our contribution.** Compose an improved collective upper bound and construct admitted lower-bound families with all physical auxiliary copies counted.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Close the gap between upper/lower bounds at the original parameter, measurement and copy-cost contract.

**Proof, review and other accepted-source links:**

- [Collective upper](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md) (proof or status).
- [Upper review](https://github.com/Sodelin/Research-Commons/blob/bf1d9a0e98b99eaf0a7d229de640a345210b78d4/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-UPPER-13-INDEPENDENT-REVIEW.md) (hand review).
- [Lower32](https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md) (proof or status).

**Connections:**
- [CB-G6-001](#cb-g6-001): **same principle**. Similar certification viewpoint, not an established theorem transfer from biological G6.

**Stable key:** physics.P1.BOUNDS. 

</details>

<a id="cb-phys-p1-002"></a>
### A specific measurement has a useful error bound
**CB-PHYS-P1-002 · Physics P1 · testing quantum states**

**Question:** Can a concrete quantum measurement be related to how much information another copy adds?

**What we learned:** Yes. The actual pretty-good measurement has the stated error bound without taking an extra unknown copy.

**What it lets someone do:** Use that exact measurement-to-error link in a larger testing proof.

**What we cannot conclude:** The remaining information bound is not proved merely by naming this link.

**Kind:** lemma. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For the actual n-copy PGM, squared Bures risk≤2δ_n and squared full-trace risk≤8δ_n, δ_n=χ(n+1)−χ(n). No extra unknown copy is used. This is not an identity between measured Umegaki risk and that increment.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Pretty-good measurements, quantum information increments and distance inequalities are classical antecedents; exact composition is scoped in the packet.

**Our contribution.** Prove the actual n-copy PGM risk/information-increment inequality without consuming an extra unknown copy.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Uniform full-Gibbs δ_n=O(M/n), a suitable dyadic bound or an equally strong direct tester is still missing.

**Proof, review and other accepted-source links:**

- [Measurement theorem and review](https://github.com/Sodelin/Research-Commons/blob/43cebb410eed5fbf6764b000f0b2e40d77090e25/research/2026-10-20-p1-pgm-information-increment/README.md) (proof or status).

**Connections:**
- [CB-PHYS-P1-001](#cb-phys-p1-001): **candidate connection**. Could improve the upper benchmark if the missing information bound is supplied.

**Stable key:** physics.P1.PGM. 

</details>

<a id="cb-phys-p5-001"></a>
### Several parts of a long-time approximation proof are established
**CB-PHYS-P5-001 · Physics P5 · noisy quantum dynamics**

**Question:** When can a simpler noisy-quantum model faithfully replace the original evolution?

**What we learned:** Several scoped comparison and influence estimates are proved, but the full requested comparison is not.

**What it lets someone do:** Reuse valid building blocks without restarting those proofs.

**What we cannot conclude:** Auxiliary models or finite time windows are not the original all-time result.

**Kind:** lemma. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Reviewed components include commuting-Pauli comparison, noncommuting finite-window support decomposition, signed-energy identities, auxiliary interacting-noise influence estimates and general-operator incidence velocity 3kh. Their hypotheses remain separate from the actual same-H infinite-filter Redfield versus original square-window GKSL plus triangular Lamb-shift comparison.

**Origin.** published open problem. Motivated by the time- and system-size-uniform many-body coarse-graining direction in Ikeuchi–Mori; the selected project contract is explicit. [Primary source](https://arxiv.org/html/2604.21366v2).

**Prior work.** Published finite-dimensional time-uniform results have dimension-dependent constants. Their existence is not erased by this programme.

**Our contribution.** Derive and review the listed comparison, energy and influence components without replacing the original target equation.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Uniform comparison over all volumes/times and all initial density matrices at fixed observable support; homogeneous term 2q I2 remains uncontrolled.

**Proof, review and other accepted-source links:**

- [Initial component review](https://github.com/Sodelin/Research-Commons/blob/d855ab1267d2e29719ff7e865aac7df85ef7c6a0/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-INDEPENDENT-REVIEW-01.md) (hand review).
- [Signed-energy identities](https://github.com/Sodelin/Research-Commons/blob/4aaa07e7497cab2515a1ba2e5c28392e22f9c84c/research/2026-10-16-p5-strong-noise-coarse-graining/signed-energy-drift-25/README.md) (proof or status).
- [Operator-incidence supplier](https://github.com/Sodelin/Research-Commons/blob/04c9808f1fc4ec3c1c57cdbca200e91e82d32d5d/research/2026-10-20-p5-operator-incidence/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** physics.P5.COMPARISON_COMPONENTS. 

</details>

<a id="cb-phys-p5-002"></a>
### One proposed evolution can fail to preserve a physical state
**CB-PHYS-P5-002 · Physics P5 · noisy quantum dynamics**

**Question:** Can the Redfield approximation always be treated as a valid physical-state evolution?

**What we learned:** No. An explicit two-qubit example loses positivity.

**What it lets someone do:** Avoid using positivity as an unsupported step in the approximation proof.

**What we cannot conclude:** This example does not by itself disprove the full requested approximation-error bound.

**Kind:** counterexample. **Mathematical status:** Named shortcut refuted.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The reviewed initial packet includes an actual two-qubit Redfield nonpositivity example under its stated generator and initial state. Its target is the unconditional positivity shortcut, not every uniform Redfield/GKSL comparison.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Provide an explicit two-qubit counterexample to unconditional positivity of the stated Redfield evolution.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Do not turn this or a growing-support example into a disproof of the original fixed-support error question.

**Proof, review and other accepted-source links:**

- [Two-qubit example and review](https://github.com/Sodelin/Research-Commons/blob/d855ab1267d2e29719ff7e865aac7df85ef7c6a0/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-INDEPENDENT-REVIEW-01.md) (hand review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** physics.P5.NONPOSITIVITY. 

</details>

<a id="cb-nano-001"></a>
### Very similar energy curves can hide opposite model labels
**CB-NANO-001 · Nanowires · what an energy curve reveals**

**Question:** Can an energy curve alone reliably distinguish the two target labels?

**What we learned:** Not at fixed nonzero error in the declared model class: opposite labels can have arbitrarily close full curves.

**What it lets someone do:** Recognize a precise limitation of this measurement and model.

**What we cannot conclude:** This is not an equal-noiseless-spectrum pair, a fabricated device or proof about every experimental setup.

**Kind:** counterexample. **Mathematical status:** Bounded-error limitation proved.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** In a fixed 60-site known-lead class with unrestricted finite potentials and zero internal loss, opposite reflection-visibility margins have arbitrarily close complete lowest-energy curves. An independently replayed rational example certifies opposite determinant intervals and whole-field energy difference≤0.09999 μeV; zero-temperature conductance separates that particular pair.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Prove fixed-lead bounded-error nonseparation and preserve an independently replayed finite rational pair.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Stored rational pair and intervals independently replayed; not a new run for this board.
- **Empirical:** Extreme barriers are mathematical parameters, not fabrication evidence.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Bounded-potential exact opposite-margin equal-curve existence is unresolved; a near-equal saved pair is not exactly equal.

**Proof, review and other accepted-source links:**

- [Fixed-lead theorem](https://github.com/Sodelin/Research-Commons/blob/caf7d4531c3027d19d0e899bee7129f672d1f342/research/2026-10-16-nanowire-fixed-lead-nonseparation/README.md) (proof or status).
- [Finite rational example](https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** nanowire.ENERGY_NONSEPARATION. 

</details>

<a id="cb-nano-002"></a>
### Conductance can certify a sign in a specified matrix model
**CB-NANO-002 · Nanowires · a model-level conductance certificate**

**Question:** Can another measurement give a definite answer that the energy curve cannot?

**What we learned:** In the stated reflection-matrix class, a sharp inequality certifies a sign when conductance is below a threshold.

**What it lets someone do:** Use an exact algebraic test after checking that the device model fits its assumptions.

**What we cannot conclude:** This is not automatically a certificate of a protected Majorana device or a microscopic realization.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For contractive particle-hole-symmetric reflection matrices with N channels, the sharp attainable region is 0≤g≤2N, |Q|≤1, Q≥1−g, and (−1)^NQ≥g−(2N−1). Thus g<1 implies Q>0. Algebraic attainment does not prove realization by every physical Hamiltonian class.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical matrix/scattering results are antecedents; no historical priority is established.

**Our contribution.** Derive the sharp attainable reflection-matrix region and its sign-certification consequence.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Matrix Lean work is source-only, not a kernel certificate.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A concrete unknown device needs a justified measurement/model/error adapter.

**Proof, review and other accepted-source links:**

- [All-channel theorem](https://github.com/Sodelin/Research-Commons/blob/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** nanowire.REFLECTION_REGION. 

</details>

<a id="cb-nano-003"></a>
### One known-model thermal calculation keeps a positive margin
**CB-NANO-003 · Nanowires · thermal error budgets**

**Question:** Does the certificate survive a small specified temperature and measurement error?

**What we learned:** For the same known model and explicit budget, the archived calculation retains a positive margin.

**What it lets someone do:** Check that particular forward-model budget.

**What we cannot conclude:** It does not establish an unknown device's label or a usable operating temperature.

**Kind:** software check. **Mathematical status:** Scoped computational certificate.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The known-device thermal certificate at 1 mK, conductance error 0.001 and zero Hamiltonian drift yields Q lower approximately 0.05925 under the saved forward-model enclosure.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Compute the stated known-device thermal/error margin with preserved enclosure evidence.

**Evidence, kept separate:**

- **Hand:** Use the exact publication evidence and model budget.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Forward calculation and enclosure evidence are recorded, not rerun here.
- **Empirical:** No unknown-device observation or operating guarantee.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Nonzero drift, unknown calibration and actual device admission require additional evidence.

**Proof, review and other accepted-source links:**

- [Thermal execution and scope](https://github.com/Sodelin/Research-Commons/blob/5055e470b32c17bdf93c55e09a891969be9ea23f/research/2026-10-16-nanowire-fixed-lead-nonseparation/thermal-model-budgets/refined-thermal-execution/PUBLICATION-README.md) (proof or status).

**Connections:**
- [CB-NANO-002](#cb-nano-002): **reused theorem**. Applies the matrix inequality through this particular model/error budget.

**Stable key:** nanowire.THERMAL_BUDGET. 

</details>

<a id="cb-cm-001"></a>
### A classical moment theorem has a checked reusable component
**CB-CM-001 · Shared mathematics · finite positive moments**

**Question:** When can finitely many exact summaries identify a finite positive distribution?

**What we learned:** A scoped classical theorem is packaged as a checked component.

**What it lets someone do:** Reuse it once the actual observation really is the required distribution's moment sequence.

**What we cannot conclude:** It cannot manufacture a missing link from biological observations to moments.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** CM-T02 is the selected four-module positive finite-moment component. Applications must use one fixed pushforward law with the correct grouped equal values and positive masses; the source/observation adapter is not supplied automatically.

**Origin.** classical prior. Positive finite-moment determination is established mathematics; the contribution is a scoped checked reusable component.

**Prior work.** Classical finite positive moment/Hankel determination.

**Our contribution.** Package and verify the classical positive-moment component with explicit application prerequisites.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Four-module certificate only, not all downstream applications.
- **Execution:** Exact receipt preserved.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** No new mathematical priority claimed for the classical theorem.

**Remaining obligation:** Each application must prove its own faithful observation adapter.

**Proof, review and other accepted-source links:**

- [CM-T02 certificate](https://github.com/Sodelin/Research-Commons/blob/514648b697aeed8f46582109cfeefcd7707cd738/research/2026-10-15-common-moment-checked-component/CM-T02-CERTIFICATE-001.json) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** common.CM_T02. 

</details>

<a id="cb-seq-001"></a>
### Three exact first-occurrence formulas are formally proved
**CB-SEQ-001 · Sequences · Thue–Morse**

**Question:** Where do the longest same-colour arithmetic patterns first appear in this sequence?

**What we learned:** Three specified families have exact first-location formulas, with checked formal proofs.

**What it lets someone do:** Use exact answers for those families, including their small-index exceptions.

**What we cannot conclude:** This does not settle every pattern question about the sequence.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For digit-parity Thue–Morse t, maximum monochromatic progression length A(d) and earliest maximum start i(d): d=2^n+1,n≥2 gives A=2^n+2,i=3·2^(2n)−2^n−1; d=2^(2n)−1,n≥1 gives A=2^(2n)+4,i=3·2^(4n)−2^(2n)+1; d=2^(2n+1)−1,n≥0 gives A=2^(2n+1),i=2^(2n+1)−1. Stronger all-start classifications are also proved. The first formula excludes n=1, since i(3)=45.

**Origin.** published open problem. Three families of Joshi–Rust Conjecture 3.8, with explicit small-index ranges. [Primary source](https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2).

**Prior work.** Maximal lengths and block-recognition ideas due to Parshina and Aedo–Grimm–Nagai–Staynova are rederived/credited. The contribution adds all-start analysis and formal first-occurrence proof.

**Our contribution.** Prove the first-occurrence formulas and stronger all-start classifications in the actual digit-parity sequence, with a complete selected formal audit.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Fresh seven-source replay and all 323 owned declarations audited; only propext, Classical.choice and Quot.sound permitted; no custom axioms.
- **Execution:** Pinned Lean 4.33.1/mathlib release and semantic correspondence review recorded.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** No whole automatic-sequence classification or historical-priority certification.

**Proof, review and other accepted-source links:**

- [Exact formulas, proof and receipt](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-04-dot-thue-morse-first-occurrence-lean-0550z/package/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SEQ.001. 

</details>

<a id="cb-seq-002"></a>
### A proposed simple description is impossible
**CB-SEQ-002 · Sequences · period doubling**

**Question:** Can the number of palindrome pieces in these prefixes follow the proposed finite-state pattern?

**What we learned:** No. The specified non-regularity statement has a reviewed all-length computer-assisted proof.

**What it lets someone do:** Resolve this precise conjecture without extrapolating from a long finite table.

**What we cannot conclude:** This is not a complete formula or a solution to the separate Fibonacci question.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Let u be the fixed point beginning 0 of 0→01,1→00; P(n) is minimum nonempty-palindrome factor count of its length-n prefix, P(0)=0. Then d(n)=P(n+1)−P(n) is not 2-automatic and P is not 2-regular. The computational lemma is an all-length inclusion over a closed reachable finite-state system.

**Origin.** published open problem. Frid–Laborde–Peltomäki, preprint Conjecture 17 / published Conjecture 2. [Primary source](https://doi.org/10.1016/j.tcs.2021.08.016).

**Prior work.** The source conjecture, regularity/difference equivalence, palindrome structure and finite-state distinguishability antecedents are credited.

**Our contribution.** Supply the all-length argument and independently implemented closed-state inclusion certificate for the exact period-doubling conjecture.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Independent AI hand review and exhaustive closed-state certificate, not Lean verification or external expert endorsement.
- **Execution:** Author closed system: 2460 states/3092 transitions. Separate representation: 1593 states/2050 transitions per starting colour. No word-length cutoff; exact inventories retained.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Formal kernel treatment and historical priority are separate; no extrapolation claim.

**Proof, review and other accepted-source links:**

- [Theorem, independent review and exact state certificates](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-04-dot-period-doubling-nonregularity-1150z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SEQ.002. 

</details>

<a id="cb-seq-003"></a>
### The allowed lengths are classified in a specific range
**CB-SEQ-003 · Sequences · repetition-avoiding substitutions**

**Question:** Which fixed-length binary substitutions preserve a stated repetition limit?

**What we learned:** Throughout the specified range, every positive length except 3 and 6 is possible.

**What it lets someone do:** Use an exact all-input length classification in that range.

**What we cannot conclude:** It does not classify every substitution or cover the lower threshold range.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For every avoidance threshold from (8/3)^+ up to but excluding 3, positive lengths of binary uniform morphisms preserving that threshold on every admissible input are exactly all lengths except 3,6; complementary morphisms realize every admitted length. Strict 8/3 differs: length 5 is impossible there.

**Origin.** published open problem. Source-posed direction in Shallit–Shur–Zorcic, Power-free complementary binary morphisms. [Primary source](https://arxiv.org/html/2310.15064v3).

**Prior work.** Their odd-length construction, exceptional-length impossibility and Kobayashi criterion are reused; the endpoint-marker construction is strengthened.

**Our contribution.** Strengthen the endpoint-marker construction to the stated all-length/all-input threshold interval.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Separate exact verification of the fixed length-12 seed and 22 required inputs supports the hand proof; finite screens are not the all-input theorem.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** No classification of all preserving morphisms or the interval (7/3)^+ through 8/3.

**Proof, review and other accepted-source links:**

- [Stability theorem and review](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-04-dot-complementary-avoidance-stability-0954z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SEQ.003. 

</details>

<a id="cb-rna-001"></a>
### A small part of the structure-processing chain is formally connected
**CB-RNA-001 · RNA / E8 / PRISM · source binding**

**Question:** Does the mathematical representation match the stated structure-processing steps?

**What we learned:** A selected checked component connects a balanced scaffold to the specified parser and pair observable.

**What it lets someone do:** Reuse that precise source-level link in a larger RNA verification effort.

**What we cannot conclude:** It does not certify the original C++ programme, physical energies or total probability of a structural class.

**Kind:** lemma. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Three accepted Lean modules bind the independently encoded balanced scaffold to literal character/stack processing, bounded close actions, partner-table filter and a fixed generated-pair observable. A separate normalized root-carrier theorem excludes two auxiliary constructors from decoded root-W parent events. Exact sources are within the selected 301-module guarded/full-declaration record.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Weighted grammars, RNAshapes/ADP, exact sampling and confidence methods are prior work. Class inverse-image probability requires SUM, not maximum score.

**Our contribution.** Bind the encoded scaffold to specified literal processing and pair readout, without claiming full executable extraction.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Scoped modules and reused dependencies are accepted; not executable extraction or full physical-model verification.
- **Execution:** Selected formal build record, not new C++ execution.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Original carrier, multiplicities, weights, emitted structures, L5/L6 inverse-image SUM, traceback, executable numerics/RNG and selected-class confidence remain separate.

**Proof, review and other accepted-source links:**

- [Scaffold source package](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-02-dot-e8-scaffold-source-1441z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.RNA.001. 

</details>

<a id="cb-nanuq-001"></a>
### A formal chain connects a stated source to its geometric formula
**CB-NANUQ-001 · NANUQ / BIO-1 · phylogenetic geometry**

**Question:** Does the displayed mathematical formula really come from the chosen network construction?

**What we learned:** The selected source-to-formula and geometric-preparation chain is checked.

**What it lets someone do:** Reuse that chain without treating its formula as an unexplained assumption.

**What we cannot conclude:** It is not a full DNA likelihood or an end-to-end biological recovery guarantee.

**Kind:** lemma. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The 53-source chain derives actual rooted-cap switching/readout, repeated-label anchor, weighted formula, opened-tree and selected-choice correspondence, faithful opened drawings and source-cycle AddCircle maps including parallel bigons. It concerns distinct displayed resolution sets and arithmetic means, not switching multiplicity, NMSC concordance factors or sequence likelihood.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** The all-level hand construction and supplied-order/statistical interfaces predate October; recovering them is not a new discovery.

**Our contribution.** Extend the selected formal chain from actual rooted-cap readout to faithful opened drawings and source-cycle maps.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** Exact dependency reuse, owned audits and six repeated final guards recorded for the 53-source packet.
- **Execution:** No new execution for this board.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Full raw-source embedding/ports, Jordan/face/contour transport, adjacent tips, circular positive support and global composition; do not downgrade inherited hand results.

**Proof, review and other accepted-source links:**

- [Source-to-geometry endpoint](https://github.com/Sodelin/Research-Commons/blob/4e8ea9f05a9716ccdabf2b2197e8699ad6e4bf4f/research/2026-10-05-dot-nanuq-actual-curve-geometry-0806z/README.md) (formal receipt).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.NANUQ.001. 

</details>

<a id="cb-msci-001"></a>
### Enough sites preserve the specified ancestry-law distinctions
**CB-MSCI-001 · MSci · DNA and ancestry-law equivalence**

**Question:** Can DNA observations distinguish everything the selected genealogy model distinguishes?

**What we learned:** For the stated fixed model and mutation assumptions, sufficiently long finite loci have exactly the same equality groups.

**What it lets someone do:** Know which demographic ambiguities remain even with those exact DNA laws.

**What we cannot conclude:** It does not promise useful sample sizes or cover relaxed clocks and arbitrary mutation models.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For each fixed finite admitted MSci model and its same complete contemporaneous labelled haploid panel, sufficiently long finite homogeneous stationary clock-JC loci have exactly the equality fibres of route-marginal timed genealogy laws.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Published MSci identifiability questions and classical polynomial-family determination/pair-law methods retain attribution.

**Our contribution.** Prove the exact clock-JC observation-equivalence statement for each fixed admitted MSci model.

**Evidence, kept separate:**

- **Hand:** Two written mathematical/source reviews recorded.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 1395 rational compiler controls independently reproduced, not a universal proof by testing.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Unknown rate mixtures, unphased genotype coarsening, relaxed clocks, other channels and useful locus counts are outside scope.

**Proof, review and other accepted-source links:**

- [Observation-equivalence theorem](https://github.com/Sodelin/Research-Commons/blob/f96399576168328322aab80f1193afaaf4312fef/research/2026-10-05-dot-flouri-clock-jc-conjecture-resolution-0908z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MSCI.001. 

</details>

<a id="cb-msci-002"></a>
### Equivalent histories differ only by a coherent hidden renaming in one class
**CB-MSCI-002 · MSci · global history alignment**

**Question:** When do two specified histories make exactly the same genealogy predictions?

**What we learned:** In the admitted class, equality is characterized by one consistent renaming of hidden populations.

**What it lets someone do:** Separate genuine ambiguity from arbitrary changes of labels.

**What we cannot conclude:** This does not include every possible migration, event or hidden-routing mechanism.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** In the reachable positive finite-epoch class, equality of all finite-sample metric genealogy laws is equivalent to one coherent hidden-population renaming across epochs. Coincident rates, rank deficiency and backward expansion are allowed; a computable finite copy cap is supplied. Silent boundaries, hidden initial routing, continuous migration, instantaneous mergers and alternative biological event factorizations are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Classify full-law equality by coherent hidden-population renaming in the stated finite-epoch class.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** No claim for excluded biological histories or a practical small cap.

**Proof, review and other accepted-source links:**

- [Global alignment theorem](https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-05-dot-global-alignment-classification-1007z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MSCI.002. 

</details>

<a id="cb-msci-003"></a>
### Two-site population features identify a specific model family
**CB-MSCI-003 · MSci · a fixed nine-parameter family**

**Question:** Can a small collection of exact DNA summary features identify the parameters of this fixed family?

**What we learned:** Yes. Nine means from the stated two-site experiment identify all nine parameters, including equal-rate cases.

**What it lets someone do:** Build exact identification and interval-validation tools for that family.

**What we cannot conclude:** Two sites does not mean two observed bases or certainty from one locus.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Global identification for the fixed tree/pulse direction, shared B/C rates, clock and current-block routing uses two homologous columns across six phased labelled haploid sequences per locus and nine means. It improves a valid 55-site sufficient bound. The later Jacobian is everywhere nonsingular and supports joint uncertain-target Krawczyk inclusion, without uniform conditioning or guaranteed numerical contraction.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical moment/tensor and interval methods are antecedents; the contribution is the specified family's global identification and exact derivatives.

**Our contribution.** Reduce the fixed-family sufficient observation to two sites/nine means and derive the exact Jacobian/contractor suppliers.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Empirical accuracy, useful locus counts and broader model classes require separate evidence.

**Proof, review and other accepted-source links:**

- [Two-site theorem](https://github.com/Sodelin/Research-Commons/blob/8b4c6508a81dc4c2c146a811adaa0cc01067db60/research/2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/README.md) (proof or status).
- [Jacobian and interval contractor](https://github.com/Sodelin/Research-Commons/blob/ebcb33d435eb82f8f18e7f586d8c1f92fe4f32af/research/2026-10-05-dot-msci-joint-jacobian-contractor-1257z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MSCI.003. 

</details>

<a id="cb-software-001"></a>
### The solver distinguishes a sharp fixture from genuinely broad data
**CB-SOFTWARE-001 · Practical biological solver**

**Question:** Does the software always return a narrow parameter estimate?

**What we learned:** No. It narrows near-exact fixtures but correctly leaves the archived finite-data case unresolved.

**What it lets someone do:** Use honest unresolved outputs rather than force a precise-looking estimate.

**What we cannot conclude:** A mathematically identifiable model need not be accurately estimable from this dataset.

**Kind:** software check. **Mathematical status:** Scoped software checks.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The integrated release records 43 application cases, a 17-frame informative replay, 50-frame finite-data UNKNOWN replay and Rust compatibility controls. Original-domain complete-cover localization succeeded on two near-exact fixtures; archived 1024-locus bands admit incompatible rA values beyond the requested width.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Implement and review the scoped release, including meaningful unresolved outputs on broad finite-data bands.

**Evidence, kept separate:**

- **Hand:** Release review distinguishes arithmetic, source existence, statistical bands and biological adequacy.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 43 application cases and recorded informative/UNKNOWN replays; no rerun here.
- **Empirical:** The archived 1024-locus observation bands do not yield the requested accuracy.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Useful whole-domain nine-parameter empirical accuracy and full native refinement.

**Proof, review and other accepted-source links:**

- [Independent release review](https://github.com/Sodelin/Research-Commons/blob/1c166276d1f0b037a402f01e3b6deaf370c864e3/research/2026-10-09-codex-practical-release-0207z/validation/INDEPENDENT-REVIEW.md) (execution review).

**Connections:**
- [CB-MSCI-003](#cb-msci-003): **reused theorem**. Uses the fixed-family exact identification mathematics; uncertainty still depends on actual data.

**Stable key:** october.SOFTWARE.001. 

</details>

<a id="cb-software-002"></a>
### A tested Rust component is not a universal correctness certificate
**CB-SOFTWARE-002 · Solver infrastructure · count calculations**

**Question:** What does the Rust count pilot actually establish?

**What we learned:** The saved component passed its specified tests and differential checks.

**What it lets someone do:** Reuse the tested bounded calculation while preserving unsupported-input handling.

**What we cannot conclude:** It is not a universal proof that native Rust implements every Lean theorem.

**Kind:** software check. **Mathematical status:** Scoped software checks.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The Rust count pilot uses a normalized Poisson prefix, not residual lumping. The release records 10 tests, 1693 differential cases, 22 invalid inputs and five boundary controls. Resource overflow/unsupported input returns UNKNOWN, not mathematical NO. A separate authenticated native-transfer review records locked offline rebuild evidence.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Implement and test the bounded count component, preserve differential/native rebuild evidence and fail-closed unsupported cases.

**Evidence, kept separate:**

- **Hand:** The linked report/review supports the stated implementation or empirical outcome, not a universal mathematical theorem.
- **Formal:** Tests and scoped transfer evidence are not a proof for all inputs or arbitrary extracted programs.
- **Execution:** Exact checks/rebuild receipts preserved, not newly executed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A universal end-to-end Lean-to-native refinement needs its own theorem and interface.

**Proof, review and other accepted-source links:**

- [Rust count pilot](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-07-rust-count-pilot/README.md) (software evidence).
- [Native transfer rebuild review](https://github.com/Sodelin/Research-Commons/blob/6dbcf5dae2c38dc7b5da162d271ce3faca082ad2/research/2026-10-07-cloud-independent-auditor-1616z/NATIVE-RUST-COUNT-TRANSFER-REBUILD-REVIEW.md) (execution review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SOFTWARE.002. 

</details>

<a id="cb-emp-bpp-001"></a>
### The saved analyses do not yet support a stable history ranking
**CB-EMP-BPP-001 · Empirical phylogenetics · BPP diagnostics**

**Question:** Did the completed runs settle the competing biological histories?

**What we learned:** No. Matched-layout chains still disagree materially.

**What it lets someone do:** Withhold recommendations until the evidence passes the convergence gate.

**What we cannot conclude:** More archived output is not the same as a supported biological conclusion.

**Kind:** software check. **Mathematical status:** Negative or inconclusive empirical result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Official-BPP frog/synthetic runs, controls and matched-layout diagnostics were performed and reviewed. Completed matched-layout chains remain CONVERGENCE_UNRESOLVED. The fail-closed prototype withholds ranked/recommended histories and rejects unknown/tampered evidence.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Perform and review the recorded diagnostics, then withhold a ranking because the convergence gate is not met.

**Evidence, kept separate:**

- **Hand:** Review supports the stated unresolved status, not a new biological theorem.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Actual recorded runs and instrumentation, not new execution.
- **Empirical:** Material chain disagreement prevents accepted ranked history.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Resolve convergence/admission before a biological recommendation.

**Proof, review and other accepted-source links:**

- [Completed diagnostic](https://github.com/Sodelin/Research-Commons/blob/647baeb1907387e9046eba815f3470475bf65872/research/2026-10-05-dot-bpp-matched-layout-completed-diagnostic-0815z/README.md) (proof or status).
- [Fail-closed release](https://github.com/Sodelin/Research-Commons/blob/b09b051471985ad9e24246700bf998d8ae526078/research/2026-10-05-dot-bpp-fail-closed-release-prototype-0825z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.EMP.BPP.001. 

</details>

<a id="cb-emp-tsuga-001"></a>
### Different markers disagree, but the cause is not established
**CB-EMP-TSUGA-001 · Empirical phylogenetics · Tsuga**

**Question:** Does marker disagreement prove a particular capture history?

**What we learned:** No. The small comparison reproduces disagreement but does not establish its cause or timing.

**What it lets someone do:** Keep the observation without overinterpreting it.

**What we cannot conclude:** This is not a capture probability, direction or dated biological event.

**Kind:** software check. **Mathematical status:** Negative or inconclusive empirical result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The four-specimen public nuclear/plastid comparison reproduces marker discordance. Orthology, specimen identity, linked plastid units and sequence-to-source calibration remain unresolved: NOT_ADMITTED / capture UNKNOWN. Later accession recovery does not restore missing original matrices.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Reproduce the small marker disagreement while explicitly refusing an unadmitted capture inference.

**Evidence, kept separate:**

- **Hand:** Observation and source-admission limits explicitly recorded.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Selected public comparison preserved.
- **Empirical:** No source-admitted capture inference.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Resolve source admission and calibration before causal/directional/timing claims.

**Proof, review and other accepted-source links:**

- [Empirical integration milestones](https://github.com/Sodelin/Research-Commons/blob/8ede352cfa00f9c7e115da1f82d1e5772544a21f/research/2026-10-08-codex-integration-0825z/g6/EMPIRICAL-INTEGRATION-MILESTONES.md) (proof or status).

**Connections:**
- [CB-G6-001](#cb-g6-001): **candidate connection**. G6-style certification would require the missing empirical-to-source admission.

**Stable key:** october.EMP.TSUGA.001. 

</details>

<a id="cb-materials-001"></a>
### One descriptor can hide a change in the next-step behaviour
**CB-MATERIALS-001 · Materials · what a descriptor leaves out**

**Question:** Does the recorded descriptor contain everything needed for the next update?

**What we learned:** Not for the specified one-attempt model: two states share the descriptor but have different transition probabilities.

**What it lets someone do:** Avoid treating that descriptor as a complete state description.

**What we cannot conclude:** This does not yet prove failure at the actual sparse recording cadence or describe synthesis kinetics.

**Kind:** counterexample. **Mathematical status:** Counterexample proved at stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** A reviewed exact one-attempt lattice descriptor collision changes transition mass. The later fixed-initializer, actual-cadence history determinant has positive conditioning probabilities, but its nonzero value remains unproved.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Classical state aggregation and Markov sufficiency are antecedents; the claim binds a collision to this actual one-attempt lattice update.

**Our contribution.** Construct the exact descriptor collision for the actual one-attempt transition.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Prove the actual sparse-cadence determinant nonzero or another source-faithful result; equilibrium Monte Carlo is not synthesis kinetics.

**Proof, review and other accepted-source links:**

- [Exact one-attempt obstruction](https://github.com/Sodelin/Research-Commons/blob/ab80109bcaf0edec8bc3eb58aea2fd369d824fa6/research/2026-10-15-codex-materials-exact-obstruction-2052z/MATERIALS-EXACT-MIXTURE-OBSTRUCTION-01.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.MATERIALS.001. 

</details>

<a id="cb-diffraction-001"></a>
### A good fit alone does not certify a molecule's presence
**CB-DIFFRACTION-001 · Diffraction · selected fits versus physical presence**

**Question:** What would turn a fitted diffraction structure into a defensible physical conclusion?

**What we learned:** A conditional set-based certificate specifies the required uncertainty and alternative-model checks.

**What it lets someone do:** Know what evidence is needed before interpreting a selected fit.

**What we cannot conclude:** The available labels alone do not produce that physical certificate.

**Kind:** theorem. **Mathematical status:** Conditional theorem.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** The conditional nuisance/set-membership certificate separates selected fit, physical molecular presence, exact boundary attainment and E/I geometry provenance. Thirty-two structure labels were recovered, but numeric profiles/templates, fit registry and calibrated errors were not, so no empirical fit or physical certificate was produced.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Elementary inverse-set/set-membership mathematics is established prior work. The contribution is the source-specific conditions and evidence audit.

**Our contribution.** Specify the source-specific conditional certificate and audit the missing numeric evidence.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** No calibrated physical inference was produced.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Acquire justified numeric profiles, templates, registry and uncertainty model.

**Proof, review and other accepted-source links:**

- [Conditional certificate](https://github.com/Sodelin/Research-Commons/blob/6a7d50f699245c87727961f59808c1ec0c9adfe5/research/2026-10-16-ge-diffraction-certification/CONDITIONAL-CERTIFICATE-01.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.DIFFRACTION.001. 

</details>

<a id="cb-viewshed-001"></a>
### Failed runs are now accounted for explicitly
**CB-VIEWSHED-001 · Geospatial software · reliable viewshed runs**

**Question:** Can a runner accidentally count incomplete or failed calculations as successful?

**What we learned:** The source-preserving repair checks outputs, restarts and failure accounting explicitly.

**What it lets someone do:** Make the recorded computational workflow more reliable.

**What we cannot conclude:** Injected failures do not show that a published geographic conclusion was wrong.

**Kind:** software check. **Mathematical status:** Scoped software checks.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Quinn runner repair validates subprocess/raster outcomes, exact restart row identity and failure accounting. Contributor evidence records 18 tests, 12 paired plus two repair-only controls; two successful pairs have identical raster arrays. Independent review read source and complete stored JSON, not a new GDAL replay.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Detailed antecedent attribution has not yet been independently indexed for this card. Consult the linked proof/source register; no new historical-priority claim is inferred.

**Our contribution.** Repair source-level failure/restart checks and preserve paired execution evidence.

**Evidence, kept separate:**

- **Hand:** Actual source and stored evidence inspected, not independently rerun GDAL.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 18 tests and paired controls are reported with their stored evidence.
- **Empirical:** No claim about prevalence of failure or published Washington findings.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** NoData, historical-platform and original-input reproduction remain open.

**Proof, review and other accepted-source links:**

- [Scoped runner review](https://github.com/Sodelin/Research-Commons/blob/6197a000949b7c977cd34aa3ae529bf481d7ebf1/research/2026-10-16-quinn-reliable-runner-review/INDEPENDENT-REVIEW-03.md) (execution review).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.VIEWSHED.001. 

</details>

<a id="cb-sport-baseball-001"></a>
### The tested models did not pass the stronger improvement test
**CB-SPORT-BASEBALL-001 · Sports · baseball model evaluation**

**Question:** Did the new baseball calculation beat the relevant alternatives?

**What we learned:** Not at the stated acceptance threshold: the tested improvements failed the stronger comparison.

**What it lets someone do:** Keep a negative result rather than advertise an unearned predictive advantage.

**What we cannot conclude:** These outputs are not complete WAR, causal player value or current forecasts.

**Kind:** software check. **Mathematical status:** Negative or inconclusive empirical result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** Six 2020–25 seasons, 979855 completed plate appearances and 738 historical September 2025 records were processed. Handedness-standardized change failed its comparison; component ridge improved over weak persistence but failed the stronger shrinkage-improvement gate. Independent numerical refits reproduced the outcomes. Missing components are not zero.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Standard component models, shrinkage and out-of-sample comparison are established methods; no new statistical method priority claimed.

**Our contribution.** Build the historical partial-component evaluation and independently reproduce its negative stronger-comparison result.

**Evidence, kept separate:**

- **Hand:** The linked report/review supports the stated implementation or empirical outcome, not a universal mathematical theorem.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** Saved evaluations independently reproduced.
- **Empirical:** Historical supported partial subtotals only; no current 2026 recommendation.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A model that clears the declared stronger evaluation and complete target accounting.

**Proof, review and other accepted-source links:**

- [Integration and evaluation report](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-21-dot-baseball-integration-report-1948z/BASEBALL-REPORT.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SPORT.BASEBALL.001. 

</details>

<a id="cb-sport-basketball-001"></a>
### An apparent model improvement is not accepted
**CB-SPORT-BASKETBALL-001 · Sports · basketball data validation**

**Question:** Can we trust the fitted basketball comparison yet?

**What we learned:** No. Score and duration reconciliation failed, so the fitted comparison is withheld.

**What it lets someone do:** Separate tested software from trustworthy predictive evidence.

**What we cannot conclude:** A lower fitted error on unreconciled data is not an accepted improvement.

**Kind:** software check. **Mathematical status:** Negative or inconclusive empirical result.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** A conditional offense/defense/context/exposure pipeline and 20 implementation tests exist. Real fitted comparison is quarantined because external score/duration reconciliation failed. Opponent exposure was reconstructible and is not the decisive missing input; publisher-reference calculations are separate.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Conditional rate modelling and exposure accounting are established methods, not evidence of a new superior statistic.

**Our contribution.** Build/test the conditional pipeline and quarantine the fitted comparison when data reconciliation fails.

**Evidence, kept separate:**

- **Hand:** The linked report/review supports the stated implementation or empirical outcome, not a universal mathematical theorem.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** 20 implementation tests do not validate the unreconciled empirical comparison.
- **Empirical:** No predictive improvement accepted.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** A permitted correctly reconciled possession/lineup corpus and fresh declared evaluation.

**Proof, review and other accepted-source links:**

- [Pipeline and evidence gate](https://github.com/Sodelin/Research-Commons/blob/2468dc1151c5e9a9dd870024a4fbeff8d4910e4e/research/2026-10-21-dot-basketball-pipeline-audit-1941z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.SPORT.BASKETBALL.001. 

</details>

<a id="cb-alexander-001"></a>
### One host cannot contain every member of the stated restricted class
**CB-ALEXANDER-001 · Alexander structures · restricted universality**

**Question:** Can a single allowed structure contain every example in this restricted family?

**What we learned:** No, under the stated branching cap and way of embedding one structure into another.

**What it lets someone do:** Rule out that precise universal-host proposal.

**What we cannot conclude:** This does not rule out unrestricted hosts or a different notion of embedding.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For each nonempty fixed-word-avoiding class with the declared balanced-child cap, no single universal host exists under the stated injective adjacency embeddings. Changed caps, unrestricted host classes and edge-to-path embeddings are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Prior Alexander-structure and word-avoidance framework is retained in the proof; this card claims only the capped embedding obstruction.

**Our contribution.** Prove the fixed-word-avoiding balanced-cap obstruction under the exact injective-adjacency embedding contract.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Unrestricted universality remains a different question.

**Proof, review and other accepted-source links:**

- [Capped-universality theorem](https://github.com/Sodelin/Research-Commons/blob/7206e66a8de0b04725924e32df822eca530b1143/research/2026-10-09-dot-alexander-capped-universality-2055z/README.md) (proof or status).

**Connections:**
- No theorem-dependency edge asserted in this first register.

**Stable key:** october.ALEXANDER.001. 

</details>

<a id="cb-g7-002"></a>
### One labelled programme can be optimal in a specified test menu
**CB-G7-002 · G7 · exact marker costs**

**Question:** How many controlled settings are really needed in this particular menu?

**What we learned:** The stated natural-plus-marker task has a sharp worst-case cost.

**What it lets someone do:** Use an exact benchmark for that authorised testing setup.

**What we cannot conclude:** It does not apply to noisy finite data or unknown control labels.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For r≥1 original hybrid sites and n≥4 in the specified original model, natural plus labelled forced-marker observations with known INDEPENDENT mode or unknown COMMON/INDEPENDENT mode have sharp worst-case site union r, two positive-support configurations and one labelled exact-law programme when support cap L≥2; programme count is ceil(2/L). Known COMMON alone has passive cost 0 sites/1 configuration/1 programme.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Reuses the programme's original-ID intervention semantics and exact natural observation results; labelled support is part of the experiment, not a free additional measurement.

**Our contribution.** Prove the matching upper construction and worst-case lower cost for this exact marker menu.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** No located specific Lean realization of these optimum formulas is claimed.

**Proof, review and other accepted-source links:**

- [Natural-marker theorem](https://github.com/Sodelin/Research-Commons/blob/b74ff892402f5d842bb19178a3243f7ef0c0c481/research/2026-10-01-sol61-head-audit-1956z/NATURAL-MARKER-OPTIMUM.md) (proof or status).
- [Independent acceptance](https://github.com/Sodelin/Research-Commons/blob/b74ff892402f5d842bb19178a3243f7ef0c0c481/research/2026-10-01-sol61-head-audit-1956z/NATURAL-MARKER-REVIEW.md) (hand review).

**Connections:**
- [CB-G7-001](#cb-g7-001): **reused theorem**. A scoped cost benchmark within the complete exact-law design framework.

**Stable key:** original.G7.NATURAL_MARKER_OPTIMUM. 

</details>

<a id="cb-g7-003"></a>
### A different menu has a classical covering-array cost
**CB-G7-003 · G7 · static full-forcing costs**

**Question:** What if every allowed setting fully forces the routing and is chosen in advance?

**What we learned:** The exact numerical-law task has a sharp cost expressed by a covering-array quantity.

**What it lets someone do:** Use the right benchmark for this different static menu.

**What we cannot conclude:** It is not an adaptive-policy lower bound or a result for arbitrary randomized decisions.

**Kind:** theorem. **Mathematical status:** Proved at the stated scope.

<details>
<summary>Exact scope, prior work, evidence and remaining obligation</summary>

**Exact statement and assumptions.** For r≥2 in the stated STATIC full-forcing-only numerical-law menu, parameter-oblivious support optimum is D=C(r), with K=ceil(C(r)/L) programmes at support cap L. The proof uses classical covering-array capacity and an actual-source matching numerical collision. Unknown IDs, finite-data confidence and adaptive full-forcing optima are excluded.

**Origin.** project posed. A claim formulated within this programme; motivation by prior literature is not a claim that this exact statement was a published open problem.

**Prior work.** Covering-array capacity is classical; it is not a new combinatorial discovery. The source-valid numerical collision justifies applying that lower benchmark here.

**Our contribution.** Bind the classical support optimum to this actual static original-source observation/cost model.

**Evidence, kept separate:**

- **Hand:** Accepted mathematical review recorded in the linked artifact; this board is an index, not a new independent proof review.
- **Formal:** No complete kernel-checked proof of this claim is asserted by this card.
- **Execution:** No execution result claimed.
- **Empirical:** Not a measured physical or biological claim.

**Novelty:** Unresolved; correctness or project acceptance does not establish novelty.

**Remaining obligation:** Adaptive or differently labelled/observed menus need separate proofs; no specific Lean optimum package is asserted.

**Proof, review and other accepted-source links:**

- [Full-forcing numerical optimum](https://github.com/Sodelin/Research-Commons/blob/e07e0ebefe80ca75b794551021df84998bb072a0/research/2026-10-01-sol61-head-audit-1956z/FULL-FORCING-NUMERICAL-OPTIMUM.md) (proof or status).
- [Later master acceptance, section 6](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md) (hand review).

**Connections:**
- [CB-G7-001](#cb-g7-001): **same principle**. A distinct declared-menu optimum, not the general master or arbitrary adaptive extension.

**Stable key:** original.G7.STATIC_FULL_FORCING_OPTIMUM. 

</details>

## What the connection labels mean

- **Proved adapter:** a proved link that preserves the needed assumptions and observations. Its hand/formal evidence level still matters.
- **Reused theorem:** an actual mathematical supplier, applied after its hypotheses have been met.
- **Same principle:** related reasoning only. No theorem implication is asserted.
- **Candidate connection:** a possible or incomplete route, not an established implication.

## Coverage gaps and next indexing pass

- Not claimed: Exhaustive indexing of every research directory.
- Not claimed: Independent new proof audit of every linked theorem.
- Not claimed: Whole-repository kernel verification.
- Not claimed: Novelty or priority certification.
- This is 58 selected claims, not a file-by-file audit of the complete October corpus or a count of independent novel theorems.
- Physics P2–P4 remain source-question entries in the prior register; no completed project solution is asserted here.
- Earlier fair-M2, rare-hybrid matched-cost, HiddenC4 and several finite-cap return/obstruction branches are preserved in the original ledgers but are not individually expanded here.
- Sequence reading editions, general p,q companions, Thue–Morse LCS growth and the lower repetition-threshold interval require separate cards; missing original proof bytes must not be replaced by invented acceptance.
- Pre-October Samuel/infinite-ancestry/genome/SoftSciences programmes, exploratory biological/psychological/social domains, and the full external catalogue are not re-audited by this board.
- Selected solver caches, quantum-oracle applicability audits, source-repaired molecular workbench mocks and further application diagnostics remain in the October source map rather than separate first-version cards.
- Some exact antecedent attributions are not yet independently indexed at card level. These are labelled rather than converted into novelty claims.
- Formal counts belong to exact snapshots and receipts. Selected 1611, public 1613, recovered 1614 and older 1615 inventories are not interchangeable whole-repository verification claims.

## Registers reconciled rather than replaced

- [Original master statements](https://github.com/Sodelin/Research-Commons/blob/0c0dc21eed1046c405e86a92673a6d473a934b6d/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md).
- [Dependency/alias ledger](https://github.com/Sodelin/Research-Commons/blob/4f39707b9834744611af3262e97305bc75d8397a/research/2026-10-05-dot-original-g-master-priority-1913z/DEPENDENCY-ALIAS-LEDGER.md).
- [Current accepted-results register](https://github.com/Sodelin/Research-Commons/blob/4f39707b9834744611af3262e97305bc75d8397a/docs/ACCEPTED-RESULTS-AND-REMAINING-WORK.md).
- [October source map](https://github.com/Sodelin/Research-Commons/blob/d32d85ea056360d66fa7cde76094bc824f24702f/docs/OCTOBER-2026-RESEARCH-MAP.md).

No new theorem, compiler execution or empirical experiment was performed to generate this board. Counts describe catalogue coverage, not the number of novel discoveries.
