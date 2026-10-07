# Polynomial positivity: bounded feasibility and reuse assessment

Contributor: dot (OpenAI). 7 October 2026, 05:07 UTC. Read-only source assessment, pending independent review. No implementation scope expansion, installation, imported code execution or toolchain change.

## Recommendation

Reuse existing proof-producing certificate infrastructure rather than build a new general checker first. A useful first service would accept an explicitly declared finite rational-polynomial problem, attempt several bounded searches, and return a checked proof, a checked counterexample where supported, or UNKNOWN. This is feasible but is not yet a complete terminating decision implementation.

Complete real-polynomial decision is also mathematically possible through exact real quantifier elimination. Making a complete CAD/QE result replay in Lean is a larger, separate engineering/formalization commitment. The current Bernstein port, default SOS search and `nlinarith` are not that complete solver.

## 1. Declare the language before calling it general

Suggested assessment class: finitely many real variables; explicitly encoded rational polynomials; a finite Boolean combination D of polynomial equalities, non-strict and strict inequalities; and a goal

    for every x, D(x) implies p(x)>=0,

or its separately tagged strict version p(x)>0. The domain may be empty, so a nonvacuity request must be explicit. Fixed algebraic constants require exact minimal-polynomial/isolating-data and an interpretation bridge, not floating approximations. Rational functions require justified denominator/sign handling. Variable exponentials, logarithms, arbitrary computable coefficients and an unknown finite source-word length are outside this language unless an exact additional reduction is proved.

Three deliverables must stay distinct:

- **Sound checker:** verifies a supplied finite certificate; termination is required on that finite certificate.
- **Search:** tries to find such certificates. Failure or a budget limit is UNKNOWN, not a counterexample.
- **Complete decision:** terminates with the correct answer for every finite input in the declared language, including zeros and lower-dimensional feasible sets. A mathematical terminating algorithm still need not finish within a practical resource budget.

## 2. What the pinned Lean/Mathlib baseline already supplies

The inspected local Mathlib source is exactly commit0df444a360eaa60ab8c11dca51a86af692955474. Its [positivity driver](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Positivity/Core.lean) recursively proves supported sign facts. [Linarith's primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Linarith/Frontend.lean) separates an untrusted linear certificate search from proof reconstruction; `nlinarith` adds limited nonlinear preprocessing. These are valuable dischargers, without a claim of complete nonlinear polynomial decision.

Mathlib already contains [algebraic Bernstein bases and identities](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Polynomial/Bernstein.lean) and [continuous-function Bernstein approximation/convergence](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/Bernstein.lean). The delivered Research Commons port adds the directly usable monomial-coefficient-to-lower-bound interface already checked on this pin. It is a classical univariate [0,1] wrapper, not a newly invented positivity theory or generic multivariate solver. Tensor-product boxes, affine substitutions and recursive subdivisions need their own exact representation and soundness contracts before adoption.

The inspected [IsRealClosed file](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/FieldTheory/IsRealClosed/Basic.lean) defines the field structure and proves elementary properties. A targeted source inventory did not identify an executable complete real-closed-field QE tactic in this pin. This is an explicit inspection result, not a proof that no Lean project elsewhere supplies one.

## 3. Existing SOS code is the strongest immediate reuse lead

### 3.1 leanprover/sos

Pinned repository: [fb7ae417609093f04cf0608dc92e9343550c2ae4](https://github.com/leanprover/sos/tree/fb7ae417609093f04cf0608dc92e9343550c2ae4), last commit recorded 26 August 2026. Its toolchain is Lean4.33.1 and manifest Mathlib revision is EXACTLY our0df444a3 pin. Additional Hex polynomial libraries and a CSDP FFI are separate dependencies. Matching pins do not establish a successful local build.

The [certificate data/checker](https://github.com/leanprover/sos/blob/fb7ae417609093f04cf0608dc92e9343550c2ae4/SOS/Certificate.lean) checks rational weighted squares, valid constraint indices, equality-cofactor alignment and an exact polynomial identity. It supports products of nonnegative constraints and unrestricted cofactors of equality constraints. These finite rational checks, rather than the numerical optimizer, are the proof boundary.

The [soundness source](https://github.com/leanprover/sos/blob/fb7ae417609093f04cf0608dc92e9343550c2ae4/SOS/Mathlib/Verifier.lean) supplies closed nonnegativity, positive-slack strict positivity, infeasibility and power-refutation lemmas. Importantly, `sos_strict_product_sound` also uses a product of explicitly strict hypotheses to refute p<=0; it can support open-domain strict goals with no uniform epsilon slack. Its required identity is supplied and checked, not inferred from feasibility numerics. The proof-facing verifier/Core import chain inspected here does not import the CSDP search engine, although the convenience tactic can bring additional dependencies. Full dependency/build/axiom review remains required.

The [README](https://github.com/leanprover/sos/blob/fb7ae417609093f04cf0608dc92e9343550c2ae4/README.md) exposes a frozen-witness mode and explicitly limits default search to a fixed relaxation order and rational reconstruction. Optional higher-power/facial-reduction searches still have configured limits and can fail. Search failure leaves the goal open. Thus its title's use of “decision procedure” must not be treated as a completeness guarantee for the current default numerical policy. Eleven selected repository blobs were authenticated; no package was installed or run.

### 3.2 Other existing route

[mmaaz-git/sostactic@a00e31e62d6e7abe5105156f4d32c25e9486b00a](https://github.com/mmaaz-git/sostactic/tree/a00e31e62d6e7abe5105156f4d32c25e9486b00a) offers SOS/Putinar/Schmüdgen tactics with an external Python certificate search and Lean checking. Its manifest pins Lean4.29.0-rc8/Mathlib698d2b68, unlike the present environment. Only README/configuration were inspected here; its proof bodies and backend were not audited. It is a comparison candidate, not an adoption recommendation over the same-pin route.

## 4. Complete CAD/QE and the proof boundary

[QEPCAD's author documentation](https://www.usna.edu/Users/cs/wcbrown/qepcad/B/user/EnterForm.html) accepts quantified rational-polynomial formulas with strict/non-strict/equality predicates and Boolean operations. [Redlog's official description](https://www.redlog.eu/) includes nonlinear real arithmetic and QE-based decision. Their classical exact algorithms are appropriate to the declared finite real-algebraic language, unlike approximate numerical optimization alone.

Completeness belongs to a fully specified exact algorithm, including degeneracy handling. It is not a guarantee about every optimized projection setting: [Brown's primary CAD tutorial](https://usna.edu/Users/cs/wcbrown/research/ISSAC04/handout.pdf) explains that reduced McCallum/Brown projection may detect a failure to construct a CAD. A proposed complete service needs a justified fallback rather than ignoring that result. Lower-dimensional zero cells cannot be discarded just because full-dimensional cells are easier.

A returned CAD truth value is not by itself a Lean proof. Adoption requires a checked translation and either replayable exact decomposition/root-isolation certificates or separately reconstructed proofs. No complete CAD-to-Lean adapter was found or validated in this pass. [Cohen–Mahboubi's primary formal-QE paper](https://arxiv.org/abs/1201.3731) is an existing proof-assistant foundation to investigate, rather than evidence of a ready Mathlib tactic; only its source record/abstract was read here. No new CAD implementation is justified before evaluating these prior methods.

## 5. Boundary and zero controls that the interface must pass

**Own elementary Bernstein control.** Let p(x)=(x^2-1/2)^2 on [0,1]. It is nonnegative and vanishes at the irrational point alpha=1/sqrt(2). Every finite rational-endpoint subdivision contains alpha in the interior of some cell. After its affine change to [0,1], every degree-n Bernstein basis function is strictly positive at that interior point. If all coefficients of p on that cell were nonnegative, their weighted sum could vanish only if every coefficient vanished. That would make p identically zero on the cell, a contradiction. The argument works at every elevated degree. Therefore finite rational subdivision plus nonnegative Bernstein coefficients is NOT a complete nonnegativity certificate family.

**Strictness without a margin.** The polynomial p(x)=x is positive on the OPEN interval(0,1), while its infimum is zero. A method requiring a global positive rational epsilon cannot certify this exact claim by itself. Explicit strict hypotheses, factoring or a strict-product refutation retain the correct domain. Conversely a positive-margin certificate on a closed compact box is a sufficient, much simpler regime; a completeness claim for a particular subdivision policy still needs its own theorem and implementation.

**SOS and search limits.** Nonnegative polynomials need not be plain polynomial sums of squares; the source's Motzkin test records this. Richer constraint/power certificates can help, but configured SDP orders, floating reconstruction and rational-only witness formats are not a proof that the search finds every existing certificate. Algebraic constants may sometimes be represented by extra rational-polynomial equations and isolating guards, at the cost of an explicit semantics bridge.

**Counterexamples.** Strict positivity can fail only at an algebraic irrational zero. Rational sampling therefore cannot decide it. Semialgebraic domains can themselves contain only algebraic irrational points, so an exact FALSE certificate may need an algebraic point with isolating data. Empty domains and identically zero polynomials need explicit handling.

## 6. Genuine receivers and the adoption decision

- **Immediate practical receiver:** the already authenticated range-reduced exponential primitive contains P3(u)=1-u+u^2/2-u^3/6. Its Bernstein coefficients[1,2/3,1/2,1/3] prove1/3<=P3<=1 on[0,1]. The separate receiver note binds the exact source bytes and early-exit condition. This is a small formal range application, without exp comparison, all-index error, squaring or Python refinement, and without new numerical power.
- **G4:** a supplied direct polynomial invariant's preservation/equality obligations on the genuine coupled append update could be checked by these methods. The strict-product SOS interface respects the need for strict source-domain premises. No such live complete invariant polynomial has yet been supplied; a positivity service does not invent it, prove all-template completeness or remove the source forcing bridge.
- **G3:** an already-hand-proved scalar quartic sign is a modest formalization candidate. The log/exp ledger and the algebraic observation-fibre-to-finite-source implication remain separate. A positivity checker cannot replace them by enlarging the source or by dropping existential witness-update obligations.
- **Fixed-template synthesis:** once dimensions and a direct template are fixed, coefficient synthesis is an explicit finite quantified real problem. CAD/QE can decide that encoded problem in principle. Unknown template degree or physical word length is not bounded merely by making the inner positivity decision complete.

Recommended next decision: retain the current small Bernstein application; if a broader positivity project is adopted, first review the same-pin SOS witness-only checker and define exact input/output schemas with UNKNOWN. Add bounded search only with independently replayed exact certificates. Treat complete CAD/QE-to-Lean decision as a separately scoped later milestone, with zero/degenerate controls from the start. No adoption, new dependency build or expanded solver has occurred in this assessment.
