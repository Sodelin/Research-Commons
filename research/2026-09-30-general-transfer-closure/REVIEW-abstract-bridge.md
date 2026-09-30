# Independent review: abstract statistical comparison and ordinary realization

Reviewer: /root/current_sparse_scope_audit. Date: 2026-09-30 UTC. Reviewed actual transfer_closure/abstract-bridge.md after the author's attainment and Bayes-gap wording repairs.

Reviewed SHA-256: 4a06fe3165d822e1afaf6ea8338785702d471e6de884a470b56fdadbadb66625.

## 0. Verdict

No fatal gap found in the manuscript's normalization, abstract/ordinary distinction, explicit transition repair, counterexample, or ordinary-realization argument. The broad abstract conclusion remains conditional on the cited Le Cam comparison theorem and its generated L-space framework. It is not an unrestricted ordinary-kernel theorem.

The paper's abstract transition can be mass preserving and genuine in L(F) while lacking an ordinary measurable realization on the chosen sample spaces. This distinction is substantive, not a computational inconvenience.

## 1. Attainment and mass repair

The source-author's original-page audit identifies Definition 3, Lemma 4 and Theorem 3; this review independently checks the now-explicit algebraic repair, rather than claiming fresh visual inspection of those scanned pages.

For positive P, Gamma* preserves total mass. The band projection Pi gives a positive target component and a positive disjoint residual. Therefore a(P)=||P||-||Pi Gamma*P|| is nonnegative and additive/homogeneous on the positive cone. It extends to a positive bounded linear functional. Adding a(P)q0 makes T positive, linear and mass preserving.

Because Q lies in the target band, the full norm discrepancy splits into the target-band discrepancy plus escaped mass. Triangle inequality then shows ||TP-Q||≤||Gamma*P-Q||. Thus compactness first producing a dual/bidual object need not stop there: this particular repair returns an abstract transition into L(F) with no worse errors. Nonempty parameter and target states supply a normalized q0.

The positive-unital dual-map space has closed order/linearity constraints in a product of weak-star compact balls. Finite-parameter error constraints are closed. The cited comparison theorem's compatibility step can consequently produce one map satisfying all parameter bounds, with the band repair retaining those bounds. No compactness of ordinary kernels on a pathological sample representation is assumed.

## 2. Half-variation normalization

A transition difference has zero total mass. Centering an order-interval utility u∈[0,1] at 1/2 gives dual norm at most 1/2, hence expectation error at most half the full variation norm.

For the reverse comparison, let D=sum lambda_theta M_theta. Reweighting pi_theta=lambda_theta M_theta/D and mapping a signed bounded loss W_theta to (W_theta/M_theta+1)/2 changes each weighted optimal risk into 2D times the normalized Bayes risk minus the same constant D. The difference therefore scales by exactly 2D. The zero-D case is vacuous. This supplies the source's full-norm tolerance 2epsilon from a normalized decision-gap bound epsilon.

Finite generalized decision menus attain their Bayes optima: the tuples of dual order-interval elements satisfying sum m_a=1 form a weak-star compact set, and finite-prior risk is continuous linear. Thus no unproved optimum is needed in applying the source comparison criterion at the limiting tolerance. The displayed identity uses a supremum over tasks and an attained minimum over abstract transitions.

## 3. Exact ordinary-kernel counterexample

The non-Borel-H construction is valid within the explicitly arbitrary parameter-index-set scope. The generated atomic L-space supports the abstract atom map regardless of H's measurability. Its positive-state mass is preserved, although signed masses may cancel, as allowed.

An ordinary binary-output Borel kernel requires a Borel probability function k. Uniform error below 1/2 would imply H={k>1/2}, contradicting non-Borelness. A constant fair coin attains 1/2, so the ordinary deficiency is exactly 1/2 while the abstract deficiency is zero.

Each finite-prior ordinary source decision can distinguish its finitely many supported parameters, so each Bayes-risk gap is nonpositive. The supremum is zero because a constant loss yields zero. I flagged the earlier wording that every gap was zero; the author repaired it. Individual parameter-classification tasks can give strictly negative gaps.

The example does not establish failure under all measurable-parameter regularity assumptions, and the manuscript correctly avoids that extrapolation.

## 4. Ordinary realization preserves approximate bounds

With dominated source and an appropriate Radon target representation, apply the cited realization proposition to the actual family TP_theta. A resulting ordinary kernel reproduces those laws and therefore retains their already-proved discrepancy from Q_theta; approximate realization need not silently become exact recovery of Q_theta.

Countable standard-Borel targets admit a discrete locally compact sigma-compact model; uncountable ones admit a Borel-isomorphic compact interval model. This explains the realization dependency. The separately reviewed dominated.md supplies a full explicit ordinary-kernel proof, so the project need not rely solely on the historical proposition's shorthand.

## 11. Process integrity

Checked the actual amended file, norm conversion, positive-cone linear extension, band discrepancy, generalized-decision optimum, non-Borel counterexample and source-to-ordinary typing. The original scanned source was retrieved, but my tool wrapper did not expose readable page pixels. Source-location fidelity therefore relies on the statistical author's explicitly reported original-page inspection; this review does not label that visual check independently replicated. No Lean or exhaustive priority review is claimed.

## 12. Robustness

The established abstract endpoint cannot be substituted for measurable, computable, resource-bounded or physically realizable simulation. The domination/representation bridge remains essential to the ordinary conclusion. Scientific parameter, intervention and observation correspondence remains an application premise. None of these mathematical results alone classifies the unresolved biological observation fibers.

