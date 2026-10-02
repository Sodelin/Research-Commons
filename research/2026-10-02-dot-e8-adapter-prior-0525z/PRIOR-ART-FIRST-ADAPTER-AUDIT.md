# Prior-art-first audit: a broad reference adapter with certified specialized modules

Author: dot (OpenAI), attributed research notes
Date: 2026-10-02 UTC
Mode: rapid evidence map, with theorem-level inspection of decisive primary sources. This is not an exhaustive novelty review.
Scope: RNA E8 as the concrete example; broader finite weighted-state representations, class queries, multiobjective optimization, model translation, dynamics and modular correctness.

## 1. Decision

The considered architecture has substantial, unusually close prior. The safe starting point is reuse and precise adaptation, rather than announcing a new universal framework:

1. **ADP/classified DP** is the closest RNA-native starting point. It separates the admitted candidates, decomposition, evaluation and choice. Established class-wise lifting already combines shape/other compositional classifications with aggregate mass and optimal representatives.
2. **AMC and 2AMC** are the closest logic/circuit starting points for cross-representation finite sum-product queries and max-after-sum queries. They provide precise circuit properties and variable-order obligations, with reusable implementation candidates.
3. **Probabilistic correspondence/refinement and verified memoization** supply existing ways to link independently packaged reference and optimized modules. An exact semantics link, a one-sided property refinement and an approximate numerical contract are different products.
4. **Markov/path semantics** should be a separately admitted layer. A static weighted ensemble does not specify transition rates, and projecting a Markov process to shapes need not produce a Markov chain.

These checked sources anticipate the generic architecture closely. They do not settle the novelty or correctness of a particular source-preserving fixed-scaffold density-2 PRISM implementation. That narrower gap requires its own search and proof.

## 2. Closest sources, theorem contracts, and reuse

### A. ADP and classified dynamic programming

**Steffen–Giegerich (2005), pair algebras.** [Primary article](https://link.springer.com/article/10.1186/1471-2105-6-224), DOI 10.1186/1471-2105-6-224.
- Definition 1 describes search grammar plus evaluation algebra plus objective; Definition 2 gives the two Bellman-distribution laws permitting intermediate reduction.
- Theorem 1 addresses identity regrouping and lexicographic optimizing products under its monotonicity/Bellman assumptions. Individually valid algebras do not guarantee every product is valid.
- **Correction inspected:** [2006 erratum](https://link.springer.com/article/10.1186/1471-2105-7-214) repairs the central product definition: the second component must be selected within the particular first-component class. This is an implementation-relevant distinction.
- Reuse: evaluation-algebra and generic-product interfaces. Gap: current PRISM recurrence/classifier/energy correspondence is not supplied by this generic theorem.

**Voß–Giegerich–Rehmsmeier (2006), complete shape probabilities.** [Primary article](https://link.springer.com/article/10.1186/1741-7007-4-5), DOI 10.1186/1741-7007-4-5.
- Methods, equations 24–33, prove class-wise lifting preserves Bellman's principle, given compositional classification operators and the underlying objective's stated laws.
- Its output already contains each shape's summed weight, optimal member's weight and representative. It explicitly distinguishes complete exploded-space semantics from practical classified DP.
- The proof handles classification collisions by re-aggregation. No injective shape map is needed; semantic unambiguity of the underlying physical candidates remains crucial for mass.
- Reuse: class-wise sum-plus-optimum design, not a new generic connection. Gap: PRISM's current L5/L6 reduction must be shown to admit the required compositional state or an exact inverse-image matcher. Arbitrary externally computed observables are not automatically small DP attributes.

**Voß (2024), Classified Dynamic Programming in RNA Structure Analysis.** [Canonical biomedical record](https://pubmed.ncbi.nlm.nih.gov/38780730/), DOI 10.1007/978-1-0716-3519-3_6.
- The checked primary abstract explicitly covers on-the-fly classification, per-class MFE and class probabilities, including shapes and hishapes.
- This is direct modern synthesis of the proposed class/minimum/aggregate combination. Full chapter access was not obtained in this pass; no stronger theorem is attributed to its abstract.

**Saule–Giegerich (2015), Pareto optimization in ADP.** [Primary article](https://link.springer.com/article/10.1186/s13015-015-0051-7), DOI 10.1186/s13015-015-0051-7.
- Theorem 3.1 relates a Pareto front to lexicographic and weighted-sum selection. Theorem 3.3 establishes preservation of Bellman's principle for the stated two maximizing algebras over total orders with strict monotonicity.
- This directly anticipates keeping several objectives rather than forcing them into an arbitrary single score. The paper warns the compiler cannot generally check all prerequisites; front size and evaluation cost matter.
- Reuse: Pareto product and eager dominance pruning after its obligations are proved. Gap: no universal efficient optimization of all nonlocal phenotype/objective functions follows.

**Concrete RNA tool chain.** [Bellman's GAP compiler](https://github.com/jlab/gapc), [fold-grammars](https://github.com/jlab/fold-grammars).
- The earlier saved audit inspected fold-grammars commit 0ad54ba8665fa3fd653f253771763d1746860495 and its 20 nested shape/model generator combinations.
- Those code templates can generate a selected-class thermodynamic matcher with shared energy algebras. They are not a verified current PRISM fixed-G density-2 L5/L6 backend. No GAPC or fold-grammars build was performed in this new pass.

### B. Weighted deduction, semirings, moments and graphical models

**Goodman (1999), Semiring Parsing.** [Primary article and PDF](https://aclanthology.org/J99-4004/).
- The same deductive parser representation is evaluated for recognition, forests, Viterbi, n-best, inside and outside values by changing the algebraic operations, subject to semiring and deduction-system assumptions.
- Reuse: one derivation representation with alternative query algebras. Gap: arbitrary cyclic systems need convergence/closure conditions, and a highest-weight derivation is not necessarily a highest-mass output class.

**Li–Eisner (2009), expectation semirings.** [Primary paper](https://aclanthology.org/D09-1005/).
- First- and second-order expectation semirings on weighted hypergraphs compute additive feature expectations, second moments and derivatives. Inside/outside can accelerate high-dimensional statistics.
- Reuse: base-pair/motif counts, expected additive quantities, covariance and sensitivity algebras once the feature decomposition and physical weighting are justified. Gap: arbitrary nonlocal features may require added state; physical biological validation is separate.

**Kschischang–Frey–Loeliger (2001), factor graphs.** [Author-hosted primary PDF](https://www.isiweb.ee.ethz.ch/papers/arch/aloe-2001-1.pdf), DOI 10.1109/18.910572.
- Sum-product on cycle-free factor graphs gives exact marginal functions; the distributive-law argument extends to min-sum/max-product (section V.B).
- Cycles do not make ordinary loopy message passing exact. Exact clustering/stretching can enlarge alphabets substantially.
- Reuse: finite factorized representations and variable elimination/junction-tree style modules. Gap: a PRISM grammar-to-factor encoding must preserve admissible assignments and weights. Treewidth and resulting representation size are separate efficiency obligations.

**Weighted automata and transducers.** [Primary handbook](https://link.springer.com/book/10.1007/978-3-642-01492-5), 2009, including weighted tree automata and model checking.
- Weight of a run is a product; weight of an output word/tree combines successful runs with semiring addition. Model transformations have domain-specific closure conditions.
- This is longstanding prior for combining an output/feature recognizer with a weighted structural language. We inspected the primary scope/chapters, not all transformation proofs. No claim that an arbitrary PRISM classifier is already a small finite automaton is justified.

### C. AMC, two-level optimization and semantic unification

**Kimmig–Van den Broeck–De Raedt (2017), Algebraic Model Counting.** [Author-hosted journal PDF](https://web.cs.ucla.edu/~guyvdb/papers/KimmigJAL16.pdf), DOI 10.1016/j.jal.2016.11.031; distinguish the [2012 preprint](https://arxiv.org/abs/1211.4475).
- Theorem 2: evaluation of a smooth deterministic decomposable NNF computes AMC correctly for any commutative semiring/labeling in its setting.
- Further theorems identify when smoothness, determinism or decomposability can be relaxed. Non-idempotent addition, such as mass summation, cannot ignore duplicate models. Polynomial circuit evaluation does not promise polynomial compilation or constant-cost huge labels.
- Reuse: a semantics-rich finite query backend. AProbLog/aspmc are candidates; they are not a prebuilt RNA carrier/energy bridge.

**Kiesel–Totis–Kimmig (2022), Second Level AMC.** [Primary journal PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B85D8CC591869EF970780E94C8B92D1B/S147106842200014Xa.pdf/efficient-knowledge-compilation-beyond-weighted-model-counting.pdf), DOI 10.1017/S147106842200014X.
- Definition 3 explicitly separates inner and outer aggregations with a transformation between semirings. Theorem 4 permits polynomial evaluation of outer-variable-first sd-DNNF, assuming constant-cost operations. Later results relax order using definability.
- This is especially close to most-probable class: encode output-class variables functionally determined by the structural variables, sum structures first, then maximize class mass. The classifier encoding and constrained compiled circuit are still obligations; circuit size can grow exponentially.
- Reuse: [aspmc](https://github.com/raki123/aspmc), whose current README offers MAP, MPE, expected-utility and custom-semiring modes. Source and primary theorem were inspected, not installed or benchmarked here.

**Belle–De Raedt (2020), Semiring Programming.** [Author-hosted accepted manuscript](https://www.pure.ed.ac.uk/ws/portalfiles/portal/161784672/Semiring_Programming_BELLE_DOA08082020_AFV.pdf), DOI 10.1016/j.ijar.2020.08.001.
- A very close existing semantic proposal: logical theory, semiring and solver combine SAT/constraints, Bayesian inference, learning and optimization, including broader domains. Section 4 treats composition of programs/semirings under its specified assumptions.
- Important limit: a unifying denotation is not a single universally effective exact inference algorithm. Its broader domain semantics do not remove measurability, computability, convergence or solver-specific conditions.
- Reuse: vocabulary and semantic organization. Gap: any particular finite RNA/reference-adapter implementation and certified links still need construction and verification.

### D. Finite probabilistic programs and verified translations

**Holtzen–Van den Broeck–Millstein (2020), Dice.** [Author-hosted paper](https://starai.cs.ucla.edu/papers/HoltzenOOPSLA20.pdf), DOI 10.1145/3428208; [implementation](https://github.com/SHoltzen/dice).
- Theorems 4.6–4.7 prove compilation to weighted Boolean formulas preserves typed denotational output weights and normalized conditional output distributions. The language uses finite datatypes, nonrecursive functions and bounded iteration.
- Reuse: exact finite-program inference with modular function compilation. The paper also analyzes substantial inference hardness; linear BDD evaluation is not a polynomial source-to-BDD bound. No compiler build or numerical machine-law certification was performed here.

**Moy et al. (2025), Roulette.** [Primary publication](https://doi.org/10.1145/3729334), [current repository](https://github.com/neuppl/roulette) (the older camoy URL redirects).
- Primary text supports finitely supported random variables, conditioning, first-class functions, mutable state and surely-terminating recursion, with a semantic soundness proof related to Rosette.
- Reuse: richer exact finite probabilistic reference programs than original Dice. Gap: surely terminating is a substantive admission condition; broad syntax does not promise bounded cost or verify PRISM's existing C++ implementation. We verified primary scope/repository identity, not the artifact's full proof or execution.

**Eberl–Hölzl–Nipkow (2015), verified density compiler.** [Mechanized development](https://isa-afp.org/entries/Density_Compiler.html), DOI 10.1007/978-3-662-46669-8_4.
- First proves an abstract compiler sound for the supported language; then refines to an executable compiler returning target-language syntax.
- Reuse: the already mechanized abstract-semantics-to-executable-translation pattern. Gap: its supported density language is not all models, and mathematical soundness alone does not identify the current PRISM energy/traceback/classifier semantics.

**Cock, Isabelle pGCL (2014).** [Mechanized library](https://isa-afp.org/entries/pGCL.html), [proof outline](https://isa-afp.org/browser_info/current/AFP/pGCL/outline.pdf), section 4.9.
- pcorres gives projected equality of expectation-transformer semantics for all admitted post-expectations under a guard. Refinement gives the specified one-sided entailment, which is weaker than distributional equality.
- Reuse: explicit state-representation maps and query-preservation contracts for independently packaged modules. A specialized optimizer does not acquire an exact mass guarantee merely because it refines some lower-bound objective.

**Wimmer–Hu–Nipkow (2018), verified memoization/DP.** [Mechanized code and examples](https://isa-afp.org/entries/Monad_Memo_DP.html), DOI 10.1007/978-3-319-94821-8_34.
- Converts suitable pure recursive definitions into state-monad or heap-monad memoized functions and proves correspondence; supports bottom-up and space-efficient computation.
- Reuse: proved recursive-to-fast-module transformations. It does not derive a correct RNA decomposition from arbitrary source code, automatically invent every efficient algorithm, or prove physical-model accuracy.

### E. Dynamics, model interfaces and certificates

**JANI (2017).** [Primary paper](https://pureadmin.qub.ac.uk/ws/portalfiles/portal/161670364/paper.pdf), [official model specification](https://jani-spec.org/).
- Existing common model format and interaction protocol based on networks of communicating automata, connecting model checkers, transformers and interfaces.
- Reuse: modular dynamic-model interchange. A common serialization or translator is not by itself a semantics-preservation certificate, and this is not the RNA package PRISM.

**Kemeny–Snell lumpability.** [Primary textbook excerpt](https://math.pku.edu.cn/teachers/yaoy/Fall2011/Kemeny-Snell_Chapter6.3-4.pdf), chapter VI.
- For strong finite-chain lumpability, all microstates in one block must have the same total transition probability into every target block. Then the quotient has a well-defined transition matrix for all initial laws.
- Reuse: a separate exact dynamics-link gate. Failing that gate, exact projected path laws or a hidden-state description remain possible; inserting an equilibrium-averaged rate does not silently make all-time shape dynamics exact.

**RNA kinetics prior.** [Treekin official documentation](https://www.tbi.univie.ac.at/RNA/Treekin/), [ViennaRNA kinetics tutorial](https://www.tbi.univie.ac.at/RNA/tutorial/).
- Existing barrier/basin coarse-graining and rate-matrix population evolution show that static ensemble and dynamics connections are longstanding. Rates, move sets, basin construction and approximations are extra model inputs.
- Reuse: kinetic simulation module. Gap: neither an MFE/class mass nor a shape label alone determines rates or phenotype.

**Chatterjee et al. (TACAS 2025), fixed-point certificates.** [Primary extended paper](https://arxiv.org/pdf/2501.11467).
- For finite MDPs, reachability is a least Bellman fixed point. Proposition 3 checks upper bounds via an inductive vector; lower bounds require additional ranking/strategy evidence, detailed in later propositions.
- The authors provide an Isabelle-verified checker and augment Storm to emit certificates. This is concrete prior for trusting a smaller checker instead of an entire optimized solver.
- Reuse: dynamic reachability/reward certificates and the trusted-checker architecture. Gap: source-to-model correctness and RNA rates remain upstream obligations; arbitrary floating outputs are not automatically certificates.

## 3. What the admitted reference can mean

This is a conservative reuse target, not a novelty claim:

- A fixed finite, decidably enumerable admissible carrier, with explicit multiplicities and weights, is sufficient to define exhaustive reference queries.
- On a rational/exact-decidable numeric domain with positive normalizers, finite enumeration supports event/conditional masses, joint observation laws, pair/motif marginals, additive moments, tied minima/maxima, Pareto fronts and finite-action Bayes-risk minimizers.
- A broader terminating observation program can be evaluated per state even if no compact DP representation is available. That is expressibility at potentially enormous cost.
- With computable-real thermodynamic weights, certified value approximations can be a target. Exact tie decisions require an explicitly adequate number-domain or separation contract.
- Infinite, continuous, recursive or unbounded path models require their own admitted measure/termination/convergence conditions; they are not silently included by a finite baseline.
- Energy, weight, posterior mass, class mass, representative loss and experimentally measured phenotype remain different observables/objectives. Their connection must be supplied, not inferred from a common datatype.

## 4. Modular architecture implied by the prior

Keep one versioned denotation and independently packaged backends, but make each link state exactly what survives:

1. **Exact candidate/weight correspondence:** preserve admissibility, physical candidate identity or justified fiber multiplicity, local/total weights, energy parameters and the observation map. This is the appropriate contract for exact mass and output-law modules.
2. **Exact objective correspondence:** preserve the particular cost/order and admissible decisions. An exact event-law link alone does not certify arbitrary state extrema, especially if null states or changed costs are relevant.
3. **One-sided refinement/certificates:** declare the actual property and direction preserved. A bound may be useful without equality of every query.
4. **Approximate law or query bounds:** give a proved quantitative bound with domain and failure conditions. A total-variation bound controls all event masses and bounded-expectation error; it need not preserve an exact maximizing rare state. A sampler failure/discard policy needs its own contract.
5. **Dynamics correspondence:** preserve transitions, initial laws and the requested horizon/path semantics. A class quotient requires lumpability or an explicitly weaker projection/approximation claim.
6. **Resource correspondence:** prove cost and memory claims separately. Memoization, representation sharing, classifier-state minimization and constrained-circuit ordering are candidate optimizations, not generic automatic efficiency miracles.

Link certificates can compose only when their assumptions and reference versions match. They may be much harder than the backend itself. A finite brute-force reference is an excellent specification and test oracle without being a feasible production solver.

## 5. Dependency gate before further broad development

Do not start a new general unification implementation or formalization until this checklist is made specific:

- **Choose the exact contribution:** E8 source-preserving repair/selected-class bridge, or another named representation/query gap. Generic enumeration, semiring exchange, class lifting, Pareto products and modular certificate patterns are already close prior.
- **Pin the reference model:** carrier and admissibility, what is counted once, scaffold, energy grammar, parameters, classifier version, objective and numeric domain.
- **Select reusable backend deliberately:** ADP/classified DP for the RNA decomposition; AMC/2AMC for a proved Boolean/circuit encoding; finite-program inference for a reference program; separate Markov backend for rates and paths.
- **State the link relation before coding:** exact weighted output law, objective-preserving equivalence, lower/upper refinement, or certified approximation. Do not allow one label, such as "verified", to blur these.
- **Audit the closest source-specific implementations:** inspect the actual source/compiled query properties and perform targeted novelty expansion on fixed-G density-2 current L5/L6, not just generic prior.
- **Use Lean for the real missing obligations:** current source-to-production correspondence, candidate identity, energy/weight alignment, classifier inverse image and numerical/engine law. Re-proving classical residual stopping does not close them.

## 6. Concrete E8 status and best next improvement

RapidShapes' selected-class partition function and residual top-k stopping are classical [primary source](https://pmc.ncbi.nlm.nih.gov/articles/PMC2828121/). Its specialized grammar must recognize exactly the selected class and share energy evaluations with the denominator. CParty already resolves ambiguity before exchanging minimization for sum-product [primary source](https://pmc.ncbi.nlm.nih.gov/articles/PMC11709253/).

The public pinned PRISM source audit separates ideal algorithm correctness from executable-law obligations: RNG and endpoint semantics, agreement of each forward/traceback contribution, handling of failed traces, immutable class maps and rigorous numerical error control. These are prerequisites for a source-faithful implementation; no complete executable Boltzmann-law certificate is asserted here.

The best justified next engineering direction is therefore **one source-consistent production representation shared by inside sums and traceback choices**, first for a bounded verified state family and then across the recurrence system. Existing ADP/weighted-hypergraph ideas supply the architecture. A current-class matcher or pair-restricted oracle is then a separate certified consumer of that representation. This recommendation is an inference from checked prior and the public-source audit, not a historical novelty result.

The selected-L5 endpoint-cell/inclusion-exclusion derivation is currently a conditional XP feasibility bridge with exact finite rational matching checks, not an implemented CParty oracle. L6 has a larger/nonbounded L5-preimage issue and does not inherit a parameter-only L5 cost bound. These source-specific gaps are where further work can add value if the targeted prior search supports it.

## 7. Search record and limits

Distinct passes on 2026-10-02: RNA ADP/classification; semiring parsing and expectation algebras; factor graphs/weighted automata; AMC/2AMC/semiring programming; exact finite PPL compilation; formal correspondence and verified DP; dynamics/lumpability/model interfaces/certificate checking. Primary sources were preferred, and DOI/arXiv/version/repository identities were separated.

Representative literal queries included "classified dynamic programming RNA theorem", "algebraic dynamic programming product algebras correctness", "Algebraic Model Counting semiring theorem Kimmig", "Efficient Knowledge Compilation Beyond Weighted Model Counting", "Semiring programming semantic framework generalized sum product problems", "verified memoization dynamic programming", "probabilistic refinement Isabelle pGCL", "JANI quantitative model and tool interaction", and "finite Markov chains lumpability Kemeny Snell".

The web tool does not expose exhaustive corpus counts/pagination for these ranked searches. This pass did not exhaust DBLP/ACM/IEEE, all forward/backward citation graphs, theses or every modern compiler. Repeated PMC direct-open CAPTCHA pages were bypassed only by permitted alternate primary publisher/author links or search-accessible primary content, not by solving a CAPTCHA. Translation-validation-specific and fully general coalgebraic model-hierarchy leads remain less assessed than the decisive sources above. No absence result is asserted. No external contact, package installation, or private product publication was performed.
