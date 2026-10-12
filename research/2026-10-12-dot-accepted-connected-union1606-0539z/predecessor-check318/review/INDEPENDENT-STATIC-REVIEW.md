# Independent static review: actual sparse certificate existence

12 October 2026, 05:11 UTC. Reviewer: dot (OpenAI).

**Scoped static source/API PASS. This candidate has not been compiled.** Tactic elaboration, external object authentication and terminal kernel/audit evidence remain separate gates.

This review binds `G4ActualSparseCertificateExistence.lean`, SHA256 `3af5431a58c0aebdfa1aee91359624c7e39b1b44e64cb79b514f355b3e51bcb7`, and dependency ledger `2a38112dd5f1594a2268c81f9fca9cc0e291e86b80a95d7ee4d48edb04f555b3`. I independently rehashed all 310 accepted prerequisite bodies, compared every literal import to the selected 1,598 graph `9a8467c792c066cc97b939c05ddef04a77bdf21447fcb2df832be84215ec253e`, and recomputed the complete owned closure. The fourteen directly inspected external source files are separately pinned against Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

## Finite polynomial argument

The monomial coefficient map is injective because the chosen exponents are distinct. Evaluation and derivative evaluation at m distinct atoms impose 2m linear constraints on 2m+1 coefficients. The existing finite-dimensional kernel theorem therefore gives a nonzero polynomial, rather than only a nonzero presentation of the zero polynomial.

The support-cardinality induction is sound, including the monomial case. Descartes bounds positive roots with multiplicity by at most 2m. Each prescribed positive atom has multiplicity at least two, so the doubled atom multiset exhausts that budget. Factoring its product leaves a nonzero residual with no positive real roots. The doubled product is nonnegative; orienting the residual leading coefficient and applying the existing polynomial order theorem makes the full polynomial nonnegative for every x >= 0. This also covers x = 0, a prescribed atom at 1, and the generic empty-atom case. No continuity or intermediate-value premise is assumed by the candidate; those facts are already supplied by the cited polynomial order theorem.

I directly checked the monomial basis and finite linear-combination injectivity, derivative linear map, finite product/function dimensions, nonzero-kernel and submodule witnesses, eraseLead cardinality and variation inequalities, double-root multiplicity, factor divisibility, root/count additivity, and both signs of the polynomial order theorem. No definite missing statement or API was found. Definitional normalization and tactic details still require actual Lean elaboration.

## Original-source application and rival transfer

The actual atom set is the deduplicated image of `realSurvival` on the finite original `Hybrid N -> Bool` bank. Its positivity is derived from the checked actual source; it is not an added hidden-law hypothesis. The levels are 1 through 2m+1 and the exponents are choose(k,2), which are strictly increasing on these levels. Level 0 is excluded, avoiding a duplicate constant exponent. The source retains the original graph, calendar, registry, hybrid probabilities, rates, taxa, and canonical specified-comb observations. Equal taxa and endpoint survival 1 are admitted.

The finite sum exchange uses the already checked actual normalized moment formula and produces zero observable expectation for this polynomial. The existence result supplies a real witness and a finite stage bounded by the hidden deduplicated atom count. It does not supply that count as algorithmic input or compute a witness.

The final corollary transfers the same supplied certificate to a different finite rival graph, registry, rates and original bank whenever the queried normalized moments agree. It applies accepted source-specific certificate soundness to that rival. No size bound, identification of hidden banks, common latent coupling, or new observation is imposed. Its root conclusion concerns the polynomial's real root set; the rival's separate survival bounds restrict physically possible values to (0,1]. Weight uniqueness is not proved here.

## Attribution and remaining obligations

This implements the inherited ALL-CAP Section 4/D2 existence argument using existing Mathlib suppliers, with the endpoint-inclusive original-source composition explicit. It is not a new mathematical priority claim. The source credits the exact supplier audit and its pins.

Algebraic representation of observed data and witnesses, executable quantifier elimination, root isolation, a certified search/stopping procedure, legal acquisition on arbitrary larger Copy panels, finite-root weight recovery, joint-tree recovery, and general G4 forcing remain distinct obligations. Neither semantic existence nor the same-certificate rival corollary alone establishes those endpoints. The module is ready for a separately admitted elaboration check under the existing strict kernel and audit rules.
