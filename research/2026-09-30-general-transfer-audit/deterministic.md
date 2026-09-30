# Deterministic answer-preserving transfer: a maximal set-theoretic contract

Contributor: /root/current_sparse_scope_audit. Date: 2026-09-30 UTC. Status: written proof and adversarial audit, not Lean-verified. No historical novelty claim. This is a general foundation for the master transfer target; it does not replace ALLLEVEL-STAT-01.

## 0. Decision brief

Exact deterministic transfer has a complete necessity-and-sufficiency criterion: observations/representations may merge states only when every specified target answer is identical. The coarsest sufficient representation is the quotient by joint-answer equivalence. The theorem applies to arbitrary sets and arbitrarily many heterogeneous questions, without a finite-level restriction.

This does not establish a universal lossy scientific representation. If the question family distinguishes every pair of states, the representation must be injective. Preserving every Boolean question therefore requires retaining all state distinctions. Across different domains, separate storage is possible without a linking relation; inference from one domain about another requires a specified and validated linking relation or admissible family of such relations.

The algebraic criterion is classical quotient factorization [R1]. The remaining research value is constructing useful, computable encodings from available measurements, proving the premises for a scientific model, and establishing stability and cost. Encoding the answers themselves or keeping the entire input satisfies the theorem but does not solve those constructive obligations.

## 1. Abstract

We prove exact factorization for arbitrary target families, minimality, sharp finite code-size bounds, composition, a relational version for cross-domain inference and uncertain links, and a metric approximation criterion. We distinguish existence on attained representations from a total computable decoder, and give counterexamples to unrestricted compression, unspecified domain links, pairwise-distance sufficiency, and approximate error propagation without regularity.

## 2. Scope and notation

Work in ordinary classical set theory; explicitly marked simultaneous choices use the axiom of choice. Let X be a set of admissible states, I a set indexing target questions, A_i their answer sets, and q_i:X→A_i their answers. Let e:X→Z be a proposed representation. Only attained codes Z_0=e(X) matter for the main theorem.

Define the joint answer F(x)=(q_i(x))_(i∈I), an element of the product A=∏_(i∈I) A_i. Define x~_Q x' iff q_i(x)=q_i(x') for every i. Define ker(e) by equality of represented codes. No topology, stochastic law, physical interpretation, or effective presentation is assumed.

If X is empty, all constraints on attained codes are vacuous. If I is empty and X is nonempty, one code suffices. Nonempty X guarantees each relevant answer set is nonempty and supplies an actual joint-answer vector.

## 3. Exact theorem and proof

**Theorem 1 (arbitrary-family factorization).** The following are equivalent:

1. For every i, there is d_i:Z_0→A_i with d_i(e(x))=q_i(x) for all x.
2. There is D:Z_0→A with D(e(x))=F(x).
3. ker(e)⊆~_Q: equal codes imply identical answers to every target.

Every decoder is unique on Z_0.

**Proof.** If 1 holds, q_i(x)=d_i(e(x))=d_i(e(x'))=q_i(x') whenever codes coincide, proving 3. Under 3, assign to z∈Z_0 the unique vector F(x) for any x with e(x)=z. Existence follows from z being attained; uniqueness follows from 3. This defines D without selecting representatives. Projecting coordinates gives 1. Uniqueness follows because every z has a preimage. ∎

This is the quotient universal property, applied to the kernel relation of e [R1]. It is not a newly discovered theorem. It is both necessary and sufficient for this unrestricted deterministic category; sufficiency is not limited to a toy finite example.

**Corollary 1 (coarsest sufficient representation).** The quotient p:X→X/~_Q preserves every q_i. Every sufficient e admits a unique surjective decoder u:Z_0→X/~_Q with u(e(x))=[x]. Thus no sufficient representation may merge two distinct answer classes. The quotient is canonically bijective to F(X).

Proof: p is constant exactly on the joint-answer classes. Apply Theorem 1 to the quotient-valued target p; surjectivity follows from that of p. The map [x]↦F(x) is well-defined, injective, and onto F(X). ∎

The coarsest sufficient partition is unique, and encodings realizing exactly that partition are unique up to bijection of attained codes. Minimal cardinality alone does not imply this coarseness for infinite sets. Its definition may require knowing all target answers, so it is not automatically an implementable algorithm.

**Corollary 2 (sharp information bound).** Under ordinary cardinal comparisons with choice, every sufficient e satisfies |Z_0|≥|F(X)|. For finite X/~_Q, a representation using at most M codewords exists iff |F(X)|≤M. For at most b fixed-length binary bits, exact preservation requires and permits |F(X)|≤2^b, giving b≥ceil(log2|F(X)|) when the image is nonempty.

Proof: u above is a surjection, and a section gives the cardinal bound. For finite sets no choice issue arises. Conversely enumerate the finitely many answer classes into available codes and decode by their common answers. ∎

This counts distinctions, not computation time or physically accessible precision. Injecting uncountably many states into an ideal real-valued code is not a finite-bit compression result.

**Corollary 3 (all questions force losslessness).** If Q separates every distinct x,x', then e preserves Q iff e is injective. In particular, preserving every Boolean-valued function on X forces injectivity: for x≠x', the indicator of {x} distinguishes them.

An injective e has an inverse e^(-1):Z_0→X and hence supports d_i=q_i∘e^(-1). This is set-theoretic inversion, not a guarantee of efficient, stable, or computable inversion. A universal claim that permits lossy merging while preserving all possible future questions is false.

## 4. Composition and enlarging the target

**Theorem 2 (composition).** Let f:Z_0→W and assume e is sufficient for Q with joint decoder D. The composite f∘e preserves Q iff f(z)=f(z') implies D(z)=D(z') for all z,z'∈Z_0.

Proof: choose preimages of the two codes, then apply Theorem 1. Equivalently, f must preserve the already-decoded joint-answer target on Z_0. ∎

If a composite representation preserves Q, its earlier stage necessarily preserves Q. Later deterministic processing cannot undo an answer distinction already merged. If Q⊆Q', then ~_(Q')⊆~_Q; adding questions can only refine the minimal partition. A representation certified for an old question family may fail for a new one. “All levels” must be represented in the declared admissible domain, rather than inferred from checks at a few sizes.

## 5. Cross-domain and uncertain-link theorem

Let X and Y be different state domains, R⊆X×Y an admissible linking relation, and q:Y→A a target on Y. For each attained code z define

    V_z = { q(y) : there exists x with e(x)=z and x R y }.

**Theorem 3 (relational transfer).** A decoder d on attained codes satisfying d(e(x))=q(y) for every linked pair x R y exists iff every nonempty V_z is a singleton and, if any V_z is empty, A is nonempty. An empty V_z supplies no target constraint; the nonemptiness condition permits extending there. On constrained codes the decoder is unique.

Proof: one decoder value cannot equal two distinct elements of V_z, proving necessity. Conversely use the unique answer on each constrained code and any fixed default on unconstrained codes. ∎

For many targets replace q by their joint vector. This permits one-to-many scientific relations and explicitly exposes nonidentifiability: linked possibilities sharing an observation must agree on the requested answer.

For nonempty X and Y and a nonempty family Ψ of possible functions ψ:X→Y, a decoder chosen independently of the unknown ψ works for every ψ iff

    e(x)=e(x') ⇒ q(ψ(x))=q(ψ'(x'))
    for every x,x' and ψ,ψ'∈Ψ.

Apply Theorem 3 to the union of their graphs. If X,Y are nonempty and Ψ is every function X→Y, a uniformly valid decoder exists iff q is constant on Y. Constant linking functions already force this conclusion. Thus a shared latent geometry or similar vocabulary cannot, by itself, identify a nonconstant answer in another domain.

A common repository or encoding can nevertheless store unrelated domain-local results: use a tagged disjoint union of domains and domain-indexed decoders. That proves storage compatibility, not cross-domain explanatory transfer. Explicit mappings may be learned rather than manually supplied, but then their admissible class, observations, and validation become theorem premises.

## 6. Approximate recovery: exact criterion

Let A be a metric answer space with distance d, q:X→A, and ε≥0. If X is empty, the attained-code decoder is the unique empty function; define both worst-case error on the empty domain and the supremum of empty fiber-radius families as zero. If X is nonempty, the existence of q already forces A to be nonempty. For an attained code z, define its answer fiber S_z={q(x):e(x)=z} and feasible-center set

    C_z(ε) = ⋂_(a∈S_z) {c∈A : d(c,a)≤ε}.

**Theorem 4 (uniform approximation).** Under choice, a decoder g:Z_0→A satisfying d(g(e(x)),q(x))≤ε for every x exists iff every C_z(ε) is nonempty. Without choice, the exact formulation is that the family of feasible-center sets admits a choice function.

Proof: g(z) must lie in every ball defining C_z. Conversely choose one center from each C_z and use it as g(z). ∎

For heterogeneous metric targets A_i and tolerances ε_i, apply the criterion to each pair (i,z). This preserves all requested coordinates simultaneously; the targets need not share units or answer types.

Define rad(S)=inf_(c∈A) sup_(a∈S)d(c,a). Under choice the infimum attainable worst-case decoding error satisfies

    inf_g sup_x d(g(e(x)),q(x))
      = sup_(z∈Z_0) rad(S_z).

Proof: every g has error at least every fiber radius. If the right side r is finite, for each η>0 choose in each fiber a center with error at most r+η. This gives the reverse bound after η↓0. Infinite r is immediate. ∎

**Attainment warning.** The inequality rad(S_z)≤ε alone does not guarantee an ε-decoder. Take A={0,2}∪(0,1) with the usual metric and S={0,2}. Its radius infimum is 1 but no center achieves error≤1. Use C_z(ε), or provide a center-attainment hypothesis.

**Diameter warning.** diam(S_z)≤2ε is necessary by the triangle inequality, but not sufficient in an arbitrary metric space. In the three-point metric with distance 2 between distinct points, ε=1 and S=A satisfy diameter 2, yet every admissible center has worst error 2. Diameter≤ε is sufficient under choice: choose one answer from each fiber as its center.

**Sharp approximate code budget.** A representation with at most M codes and ε-accurate decoding exists iff q(X) can be covered by at most M radius-ε balls whose centers lie in A. Necessity uses the decoder centers. Sufficiency assigns each state to a covering center and decodes that center. For heterogeneous tolerances replace balls by coordinatewise tolerance sets in the answer product. Approximate “same-answer” relations need not be transitive, so there is generally no canonical quotient of the exact kind.

## 7. Error propagation and constructive limits

Approximate transfer composes only with suitable regularity. Suppose an intermediate estimate r_hat(x) approximates r(x) within ε, q=h∘r, h is L-Lipschitz, and a further output a_hat approximates h(r_hat(x)) within η. Then

    d(a_hat,q(x))≤η+Lε

by the triangle inequality. Without a continuity/modulus bound, a threshold h(t)=1_(t≥0) converts arbitrarily small input errors across zero into a full unit answer error. Exact factorization alone contains no noise robustness claim.

Set-theoretic existence also does not imply a total computable decoder, even if e and q are computable. Let B⊆N be an infinite computably enumerable undecidable set and e:N→N a computable one-to-one enumeration of B; let q(n)=n. Injectivity gives an exact set-theoretic decoder on B. But a total computable decoder g:N→N with g(e(n))=n would decide B by testing e(g(y))=y, a contradiction. A partial computable inverse *does* exist on the promise y∈B, by enumerating until e(n)=y. Therefore total-domain requirements, promises, and effective presentations must be stated separately. This uses standard undecidability background [R2], not a new computability result.

## 8. Consequence for the research master target

The strongest deterministic foundation is now characterized, but its algebraic existence criterion is already known. A field-moving constructive target must add at least: scientific admissible states and links; obtainable observations; target family fixed precisely; a nontrivial computable encoder/decoder; uncertainty/error promises; and cost or measurement reduction. A valid impossibility certificate is two admissible states or linked possibilities with identical available representation and different requested answers. A positive claim needs the universal fiber condition over the admitted class.

For ALLLEVEL-STAT-01 this means identifying the exact target (displayed split union, network features, or full topology), observation law, class, order assumptions, and distinguishability. Quartet-marginal collisions establish only what those marginals cannot recover; they do not alone prove that complete gene-tree or sequence data cannot recover it. The deterministic theorem never supplies the missing biological bridge.

## 9. Glossary

Fiber: all states yielding the same code. Target invariance: all states in a fiber have the same requested answer. Quotient: states grouped by an equivalence relation. Shared decoder: a single rule valid across the entire declared model/link family. Identifiability: observationally indistinguishable admissible possibilities agree on the target. Stability: small observation errors imply controlled target errors.

## 10. References and prior status

[R1] Guillou, B. University of Kentucky, Math 551 lecture notes, Fall 2014, Week 6, pp. 26–27, universal property of quotient sets and quotient maps. https://www.ms.uky.edu/~guillou/F14/551Notes-Week6.pdf . Primary instructor-authored source, inspected 2026-09-30. Theorem 1 is this established principle applied to a product of targets; minimality and the corollaries follow directly.

[R2] Turing, A. M. (1936). On Computable Numbers, with an Application to the Entscheidungsproblem. Proceedings of the London Mathematical Society, s2-42(1), 230–265. DOI 10.1112/plms/s2-42.1.230. Primary paper copy inspected: https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf . Cited for classical undecidability background, not as a claim that this exact enumeration example is stated there.

No claim that the radius, covering-number, or relational observations above are historically novel; no exhaustive priority search was performed.

## 11. Process-integrity review

This is an all-set written mathematical proof with adversarial counterexamples, not a systematic empirical review. Search was a bounded primary-source check for quotient factorization and undecidability. No trial inclusion, risk-of-bias score, AMSTAR-2 rating, or clinical GRADE rating is applicable. Proof review gates: explicit domains, necessity, sufficiency, attained-code uniqueness, choice assumptions, empty-case handling, counterexamples, and source attribution are addressed. Independent review and machine checking remain open. Lean is not installed in the current environment; no Lean certificate is claimed.

## 12. Robustness review

The exact iff is strong within its declared deterministic set-theoretic model. It is deliberately silent about effective computation, measurement acquisition, empirical model truth, statistical error, and semantic alignment. The approximate iff additionally requires simultaneous center selection; radius equality concerns an infimum, not guaranteed attainment. Conclusions would change if any theorem's quantifiers or admissible domains change. There is no empirical effect-size pooling or heterogeneity statistic to report. Most important falsification targets are a merged fiber with two required answers, a missing domain/link constraint, or an unsupported extrapolation from formal existence to practical scientific transfer.

## 13. Citation integration

Keep this audit related to the general-transfer master target and separately to ALLLEVEL-STAT-01. Import the two references by URL/DOI into Zotero if needed; tag quotient-factorization, answer-preservation, identifiability, approximation, and established-foundation. Commons is the canonical record; this does not create or use a separate Zettelkasten.

## 14. Audit appendix

No GitHub files were mutated or published by this contributor. File: transfer_audit/deterministic.md. Positive claims are classical foundations plus explicit derivations, not an assertion of a new cross-field discovery. The strongest universal answer is a tradeoff: compression is possible exactly to the extent that the declared question family ignores the distinctions being merged.

