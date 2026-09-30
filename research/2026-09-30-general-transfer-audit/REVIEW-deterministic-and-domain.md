# Independent review: deterministic transfer and causal/domain audit

Reviewer: /root/current_stat_scope_audit, 2026-09-30 UTC. Reviewed local `transfer_audit/deterministic.md` and `transfer_audit/domain_audit.md`. These files were authored by other contributors. This review is independent hand inspection, not Lean verification or empirical validation. No canonical files or source-author files were edited by the reviewer.

## Verdict

The main deterministic factorization, quotient minimality, approximation criterion and causal countermodel are sound under the assumptions stated. **The initial empty-case omission in the separate uncertain-function-family equivalence has been corrected and independently rechecked.** The original finding and follow-up receipt are preserved below. It did not affect Theorem 3 itself.

The broad conclusions stay conditional: preserving specified answers does not construct their scientifically meaningful measurement bridge. Universal deterministic state-question preservation can require injectivity; this does not imply raw-sample injectivity for stochastic decision experiments. The statistical companion's reconstruction-kernel criterion permits removal and regeneration of ancillary noise.

## 1. Exact factorization and quotient

Theorem 1 correctly restricts decoders to the attained image Z0=e(X). Its fiber condition is necessary, and the unique vector F(x) in each fiber defines a joint decoder without selecting representatives. The proof avoids an unnecessary axiom-of-choice requirement for arbitrary target families: a joint answer is explicitly supplied by the given q_i maps for any attained fiber.

The quotient-valued target gives the claimed canonical surjection from attained codes onto joint-answer equivalence classes. The cardinal lower bound is correctly labeled as using choice when extracting a section. Sharp finite code bounds follow from class counting. The warning that infinite minimal cardinality alone does not determine the coarsest partition is appropriate.

All Boolean state questions separate every distinct state, so injectivity is necessary and sufficient in this deterministic category. This is not a claim that every noisy observation bit must be retained in the statistical category; the distinction should remain explicit in any combined headline.

Composition and target-family enlargement follow from the same fiber condition. Later deterministic processing cannot recover a distinction already merged.

## 2. Relational transfer and the correction

Theorem 3 correctly distinguishes constrained attained codes, where their linked answer sets must be singletons, from unconstrained codes, where a default answer must exist. Its condition covers empty target sets and empty attained images.

The subsequent separate assertion for a family Psi of possible functions omits that default condition when Psi is empty. Counterexample:

- X={x}; e is identity into Z0={x}.
- Y=A=empty set; q:Y->A is the empty function.
- Psi is empty, as there is no function X->Y.

The displayed cross-Psi agreement condition is vacuously true, but no decoder Z0->A exists. Thus this iff is false without an additional assumption or extension condition.

Minimal repair: retain Theorem 3's condition that A is nonempty whenever any attained code has no linked answer. Equivalently, for this function-family case, add `Z0 is empty, or Psi is nonempty, or A is nonempty`. If Psi is nonempty and X is nonempty, existence of a function X->Y and of q guarantees a permissible answer. An explicitly nonempty-domain scope also repairs the intended claim, but preserving the general empty-case condition better matches the all-set theorem.

The later all-functions impossibility corollary explicitly assumes X and Y nonempty and is correct: constant linking functions force q to be constant. Tagged disjoint-union storage does not establish cross-domain inference, as the text correctly states.

## 3. Approximation and choice

The feasible-center intersection criterion is exact. It is correctly separated from merely having a small unattained radius infimum. The supplied incomplete metric example has infimum radius 1 but no center achieving it. The three-point equilateral example correctly refutes sufficiency of diameter <=2 epsilon.

Choice is explicitly invoked for simultaneously choosing fiber centers, including heterogeneous coordinates. The infimum worst-error/radius identity is correct under choice; its construction uses an arbitrary positive slack rather than incorrectly asserting attainment. The finite code budget characterization follows from covering the target image with allowed-center balls.

Minor clarification: for an empty X, define the supremum of a nonnegative error over the empty set as 0 and the infimum worst-error convention accordingly, or restrict the radius identity to nonempty X. The text addresses empty cases in the exact theorem but leaves this convention implicit in the approximation formula. This is not a nonempty-case proof defect.

Lipschitz propagation gives eta+L epsilon by triangle inequality. A threshold counterexample correctly shows why approximate inference cannot compose without regularity.

## 4. Computability counterexample checked

The undecidable-enumeration example is valid, including its effective construction. Given an infinite computably enumerable undecidable B, simulate an enumeration, discard duplicate outputs, and wait for the next distinct member to define e(n). For each n, infinitely many members guarantee eventual termination. Thus e is total computable and injective with image B. The target q(n)=n is total computable.

If a total computable decoder g:N->N satisfied g(e(n))=n, then on any y one could compute e(g(y)). If y belongs to B, injectivity and the decoder law give e(g(y))=y. If y does not belong to B, the output of e always lies in B and cannot equal y. Equality therefore decides B, contradiction.

A partial inverse on the attained-image promise is computable by enumeration until y appears. The example consequently distinguishes a computable promise decoder from a total decoder on the whole ambient code domain, rather than incorrectly claiming that an injective computable map lacks every computable inverse.

## 5. Causal countermodel arithmetic independently checked

The shared source SCM and target A use a(x,u)=2/5+2u/5-x/5. Its four values, for (x,u)=(0,0),(0,1),(1,0),(1,1), are 2/5,4/5,1/5,3/5, all interior probabilities. Target B complements these values.

Since U is fair and X=U XOR E with E~Bernoulli(1/4), X is fair. Conditional on X=0, U=1 has probability 1/4; conditional on X=1, U=1 has probability 3/4. Therefore

```math
E[a(0,U)\mid X=0]=(3/4)(2/5)+(1/4)(4/5)=1/2,
```

```math
E[a(1,U)\mid X=1]=(1/4)(1/5)+(3/4)(3/5)=1/2.
```

Complementing a preserves these conditional probabilities. All measured XY cells consequently have probability 1/4 in source, target A and target B. The entire **measured** joint law is equal; the claim does not include observing the latent U.

Under do(X=x), U remains fair, giving A's response 3/5-x/5 and B's response 2/5+x/5. The queried x=1 response is respectively 2/5 and 3/5; the action minimizing expected Y reverses. Because the source SCMs are identical, every available source intervention law agrees between worlds. Passive target observations cannot distinguish them. The triangle inequality gives at least 1/10 absolute point-estimation error in one world.

The failure holds with identity representation of the available XY data. It is a causal-information obstruction, not a failure caused by compression. A target intervention on X would distinguish this pair's population responses; finite-sample error control and universal separation from other competitors remain separate obligations.

## 6. Sufficient causal contract and scope

The transport formula is valid under the stated assumptions: Z is measured/aligned and precedes the action; conditional **interventional** responses are invariant; the source identifies them with overlap; and the target Z distribution is identified. The pre-intervention condition ensures the Z mixing distribution is not changed by do(a). Matching passive conditionals alone is correctly rejected as insufficient.

The primary-prior table was not independently re-audited by this reviewer; its source-inspection attribution remains with the domain audit author. This review verifies the constructed causal pair and conditional transfer argument, not historical priority or the full completeness proofs of the cited algorithms.

## 7. Follow-up correction receipt

The author revised the uncertain-function-family specialization to require nonempty X, Y and Psi. Under those assumptions every attained code has a linked answer and q supplies a nonempty answer set, so the previously reported vacuous-condition counterexample is excluded. The general relational Theorem 3 retains its full empty-case/default-answer formulation. The core arbitrary-set factorization theorem was not narrowed.

The author also explicitly defines empty-domain worst-case nonnegative error and the supremum of an empty fiber-radius family as zero. This resolves the approximation convention noted above. Both changes were reread directly in the revised file. No remaining mathematical defect was found in the reviewed claims; machine checking and empirical bridges remain unestablished.

Reviewed revised-file SHA-256: deterministic.md `c182996dd196b461462c1a15109ac599abf6b088982415023240a46bee6a0a0e`; domain_audit.md `63d20f59d810e3a6f417df40d1a1faec9d9d9571b6c14df4839154500116d83a`.

## 11. Process integrity

Direct inspection of every mathematical section, quantifier/empty-case checking, independent computation of the causal probabilities, and an explicit effective construction for the computability example. No model fitting, simulator, automated theorem checker or new priority search was used. The empty-Psi defect was reported before publication and the corrected text received the follow-up check recorded above.

## 12. Robustness

The proofs survive arbitrary state/target cardinality within their declared set-theoretic category; approximation requires the stated choice and center conditions. Causal conclusions hold for the displayed SCM and available information contract. Neither result establishes that a proposed biology-to-psychology correspondence is true, identifiable, computable or useful. Changes to observable latent variables, intervention access, question families, code promises or stochastic semantics can change the answer. The exact claims are mathematical and do not warrant empirical effect-size or meta-analysis statistics.
