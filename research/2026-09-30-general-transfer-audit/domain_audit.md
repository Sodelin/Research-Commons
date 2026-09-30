# GENERAL-TRANSFER-01: domain and causal audit

Assessment: 2026-09-30 UTC. Read-only primary-source comparison and an exact constructed countermodel; no novelty, empirical validity, or universal positive-transfer claim. Prepared as an adversarial component of the coordinating agent's target review.

## Conclusion

A domain-general **conditional characterization of when a requested response transfers** is coherent. A theorem guaranteeing useful positive transfer across unrestricted domains is false. Deterministic factorization establishes response preservation only when the response is already constant on the observation fibers. Blackwell comparison compares experiments for a common state/decision specification; it does not establish that two scientific domains have the same causal response, aligned states, or valid measurement semantics. Those are premises to justify, not consequences of the comparison.

Register the strongest target as a family-wide identification/measurement problem: given a declared cross-domain model grammar, observation and intervention contracts, allowed mechanism shifts and sampling budget, determine the target response set, certify when a proposed transfer is sound, and establish attainable information/cost boundaries or explicit impossibility. The theorem can quantify over all models and domain labels in that grammar. It cannot manufacture an applicable grammar for every scientific field or guarantee that every target is identifiable.

## One exact impossibility pair, despite full observational agreement

This is an audit construction using standard SCM semantics, not a claimed new theorem.

Let independent exogenous variables satisfy

\[
U\sim\operatorname{Bernoulli}(1/2),\quad
E\sim\operatorname{Bernoulli}(1/4),\quad
V\sim\operatorname{Uniform}[0,1],\quad X=U\mathbin\oplus E.
\]

Define

\[
a(x,u)=\tfrac25+\tfrac25u-\tfrac15x.
\]

In both candidate worlds, the **source** mechanism is
\(Y=\mathbf1\{V<a(X,U)\}\). In target world A it remains unchanged; in target world B it becomes \(Y=\mathbf1\{V<1-a(X,U)\}\). All Bernoulli outcome probabilities lie strictly between zero and one. Both worlds use the same causal graph \(U\to X, U\to Y, X\to Y\), with a permitted domain change at the Y mechanism.

Since \(P(U=X\mid X)=3/4\), both target worlds have

\[
P^*(X=x,Y=y)=\tfrac14\qquad(x,y\in\{0,1\}).
\]

The source has this same observational law. Thus the complete measured joint distributions agree, not merely feature marginals. Every source intervention law agrees between worlds because their source SCMs are identical. Use the identity measurement map: no compression is needed for the failure.

Nevertheless,

\[
P_A^*(Y=1\mid\operatorname{do}(X=x))=\tfrac35-\tfrac15x,
\qquad
P_B^*(Y=1\mid\operatorname{do}(X=x))=\tfrac25+\tfrac15x.
\]

Consequently the response \(q=P^*(Y=1\mid\operatorname{do}(X=1))\) is 2/5 or 3/5. The action minimizing expected Y also reverses. A procedure supplied unlimited source observations/experiments and unlimited passive target observations receives identical information in the two worlds. It cannot identify q or the target action ranking. Any shared point estimate has absolute error at least 1/10 in one world. Conditional observational invariance \(P_S(Y\mid X)=P_T(Y\mid X)\) therefore does **not** establish causal-effect invariance.

An additional target experiment on X, or a justified restriction excluding the Y-mechanism change, can separate this pair. A target experiment is a different information contract; finite noisy experiments additionally require statistical error control.

## Exact sufficient assumptions: an illustrative causal transfer contract

For a bounded outcome and fixed action a, let Z be an aligned, measured, pre-intervention covariate. The following assumptions suffice:

1. Source and target interventions implement the same action and outcome definitions, with consistency and the declared interference/unit structure.
2. The conditional **interventional** response is invariant: \(P_T(Y\mid\operatorname{do}(a),Z)=P_S(Y\mid\operatorname{do}(a),Z)\). A defended selection diagram can justify this through S-admissibility; matching passive conditionals alone cannot.
3. Source experimental identification holds within Z strata, and every target-supported stratum/action is supported by the source experiment.
4. Target Z measurements identify the intended target population distribution, with selection/mismeasurement either absent or explicitly corrected.

Then

\[
P_T(Y\mid\operatorname{do}(a))
=\sum_z P_S(Y\mid\operatorname{do}(a),z)P_T(z).
\]

This is established standardization/transportability prior art, not a new GENERAL-TRANSFER-01 result. For finite data one must additionally specify independent or dependent sampling, exposure counts, boundedness/noise, overlap lower bounds and simultaneous error control for adaptively selected queries. Population identification is not a finite-sample stopping guarantee. For sequential systems, transfer must preserve the relevant action/transition/observation law through the declared horizon; one passive snapshot cannot establish that premise.

## Primary comparison and consequence for novelty

| Primary result | What it establishes | Obligation it leaves for this target |
|---|---|---|
| Bareinboim–Pearl (2013), Definitions 3–4, Lemma 2, Sections 4–5 | Causal transportability relative to a defended selection diagram, with a complete decision/formula procedure; paired models can certify failure | Do not recreate generic graph-based transportability as new. Justify scientific mechanism correspondences and the available data contract. |
| Zhao et al. (2019), Section 4.1/Figure 1, Theorem 4.1 | Equal representation marginals plus zero source error can yield target error one; labeling/conditional disagreement matters | Alignment and source fit cannot replace a response-preserving conditional contract. |
| Ben-David et al. (2010), Theorems 1–2 | Labeled-source/unlabeled-target adaptation can fail under covariate shift combined with individually insufficient additional conditions | Include support/coverage and hypothesis-class assumptions. Their closeness is hypothesis-dependent divergence, not equality of full marginals. |

The scientific contribution must lie beyond these interfaces: a substantive model-specific sharp boundary, efficient adaptive measurement rule with defended noise/cost guarantees, or a source-faithful stronger characterization that existing transportability results do not cover. A generic theorem's field-neutral notation establishes neither every field's causal premises nor novelty in any field. Each application needs its own model-to-response and measurement correspondence. Preserve the phylogenetic master scope and import its existing arbitrary-level identifiability results on their actual class/data intersection.

## Primary evidence

- Bareinboim and Pearl, *A General Algorithm for Deciding Transportability of Experimental Results*, Journal of Causal Inference 1(1), 107–134 (2013), DOI 10.1515/jci-2012-0004. [Primary PDF](https://arxiv.org/pdf/1312.7485), printed pp. 108–113 (examples, definitions and paired-model test), Sections 4–5 (criterion and complete algorithm). Reopened full PDF text; no complete proof re-audit.
- Zhao, Tachet des Combes, Zhang and Gordon, *On Learning Invariant Representations for Domain Adaptation*, ICML/PMLR 97 (2019). [Primary PDF](https://proceedings.mlr.press/v97/zhao19a/zhao19a.pdf), Section 4.1/Figure 1, PDF pp. 4–5; Theorem 4.1, PDF p. 5. Primary text independently inspected.
- Ben-David, Lu, Luu and Pál, *Impossibility Theorems for Domain Adaptation*, AISTATS/PMLR 9, 129–136 (2010). [Primary PDF](https://proceedings.mlr.press/v9/david10a/david10a.pdf), Theorems 1–2, printed pp. 134–135. Primary PDF reopened; exact theorem restrictions checked by a delegated source reviewer.

No broad literature review, canon edits, coordination posts, or commit were made.
