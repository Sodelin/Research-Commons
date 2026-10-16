# From observable redundancy to a training objective: prior and admission boundary

16 October 2026. Attributed research assessment by dot for Nolan. Status: source audit and elementary countercontrol, scoped hand-reviewed by the coordinating dot on 16 October 2026. The review checked the quadratic calculation and its stated scope, and the distinction between prior reuse and missing calibration. It is not an independent full audit of the cited literature or a training-improvement claim. No training, model queries, execution validation, or new field-level theorem claim.

## Executive conclusion

The useful next endpoint is not another collision estimator. It is a certified relation between a proposed deduplication rule and the actual training-gradient error on the states the optimizer visits. Established coreset methods already supply important parts of that endpoint. The currently reviewed G6 application certifies a redundancy statistic under its observation assumptions; it does not certify preserved training quality.

There is a directly stated contemporary practical need, but no verified narrowly posed mathematical conjecture to claim solved: Scale Dependent Data Duplication, Appendix B, asks for validation on large models trained on semantically deduplicated data, because its controlled experiments used exact repeats. This is partly experimental/model-validation work. A theoretical guarantee requires additional, explicitly admitted model assumptions. The unrestricted static-similarity guarantee is false, as the elementary example below demonstrates.

## Primary prior boundary

1. [SemDeDup v3](https://arxiv.org/html/2303.09540v3), section 6.5, chooses the threshold to obtain a desired retained size using sampled clusters. Its limitations acknowledge broader informative-data and data-quality questions. This is not a theorem that a chosen threshold preserves a target loss.

2. [GRAD-MATCH, ICML 2021](https://proceedings.mlr.press/v139/killamsetty21a/killamsetty21a.pdf), section 2, Theorem 1 and Appendix B, analyzes a weighted subset's gradient residual relative to training or validation loss. Its convergence claims have optimization regularity/domain assumptions; its introductory scope explicitly includes convex objectives. The established residual-to-objective direction should be reused, not renamed as a G-theorem or transferred to arbitrary transformers without its assumptions.

3. [BRIEF, PVLDB 19](https://www.vldb.org/pvldb/vol19/p1264-chai.pdf), equations 2–3, 18–19 and section 5.3, formulates instruction-tuning coresets through gradient approximation over a parameter domain, with separate knowledge and instruction-following components. Its pair distances are suprema over that domain, rather than static embedding cosine scores. This is substantial existing 2026 progress. Only the relevant formulation and source arguments were inspected here, not an independent audit of every theorem or empirical result.

4. [Scale Dependent Data Duplication v1](https://arxiv.org/html/2603.06603v1), Definition 5.1 and Appendix B, connects model-dependent similarity to duplication and explicitly retains the exact-versus-semantic validation limitation. The literal author-stated need includes: “Future work could validate our findings on large models by training on semantically deduplicated datasets.” Our operational threshold relation is a measurement target; resolving its collision probability does not discharge that need.

5. [NVIDIA NeMo Curator issue 1758](https://github.com/NVIDIA-NeMo/Curator/issues/1758), opened 7 April 2026, remained visibly open when inspected on 16 October. It requests scale-aware threshold adjustment and a collision-audit utility. This is a software request. Its stronger scientific assertions are not accepted here as established facts or as a formal conjecture. The bounded later-work check above does not prove the absence of all other progress.

## Exact countercontrol: identical initial gradients do not determine training preservation

For M>1, let theta be a real parameter and define nonnegative, smooth, strongly convex losses

    l1(theta) = (theta+1)^2/2,
    l2(theta) = M(theta+1/M)^2/2.

At theta=0 both gradients equal 1. Consequently their gradient norms, cosine similarity, and every threshold relation based on that initial cosine agree exactly with the duplicate-loss model having l1=l2=(theta+1)^2/2. Identical arbitrary external embeddings can also be supplied in both models if no relationship between embeddings and losses is required.

Retain the first example with total normalized mass one. The retained objective is l1 and has minimizer theta_C=-1. The full averaged objective F=(l1+l2)/2 has

    F'(theta) = (M+1)theta/2 + 1,
    theta_F = -2/(M+1),
    F(theta_C)-F(theta_F) = (M-1)^2/[4(M+1)].

Proof: differentiating gives the displayed affine derivative. A quadratic of curvature (M+1)/2 has excess equal to (M+1)(theta-theta_F)^2/4; substitution proves the last identity. The excess is unbounded as M grows, whereas in the duplicate-loss model it is zero.

Moreover the normalized full-minus-retained gradient at any theta is (M-1)theta/2. At the common first gradient-descent update theta=-eta, its magnitude is (M-1)eta/2. Thus perfect initial gradient matching does not imply later matching.

Scope: this rules out a uniform guarantee from that initial observation alone over this smooth-loss class with no common curvature bound. It does not contradict a theorem that supplies common smoothness constants, a bounded parameter domain, subsequent gradient measurements, an embedding-to-gradient modulus, or other identifying restrictions. It is a classical insufficiency example, not a counterexample to a particular transformer or evidence that semantic deduplication fails empirically. It does not address an optimal gradient-aware weight choice with additional information.

## What a useful admissible bridge would actually require

Fix the tokenizer, example/sequence objective, optimizer state, weighting rule, sampling law and parameter domain Theta. For a retained representative map pi and original normalized masses a_i, a sufficient source contract is a certified bound

    sup_{theta in Theta} ||g_i(theta)-g_pi(i)(theta)|| <= Delta_i.

With retained mass b_j=sum_{i:pi(i)=j}a_i, the triangle inequality gives

    sup_Theta ||sum_i a_i g_i - sum_j b_j g_j|| <= sum_i a_i Delta_i.

This is established coreset reasoning, not a new theorem. A static threshold relation alone does not provide the Delta_i. If the similarity is gradient cosine at one state, both magnitude discrepancy and movement away from that state need control. If it is an embedding similarity, an additional encoder-to-gradient calibration is required. Bounds over training gradients also do not alone establish population generalization or downstream-task improvement.

A G6-style contribution could be an honest finite decision, such as whether a declared residual budget is met, using simultaneous confidence sets over an actually specified calibration model and abstaining on mixed-target fibres. Its missing supplier is the scientifically justified observation-to-uniform-gradient-error model, including optimizer/domain coverage and data dependence. G2 exact path-law compression applies only when the per-example update kernels really coincide under the retained full state and sampling scheme. Neither supplier makes these premises true from semantic resemblance.

The smallest decisive next input is therefore an accessible, specified calibration/model contract that relates a particular encoder's observable pair distances to training gradients over the intended states. A proof or source-valid counterexample for that contract would be substantive. Without it, continuing to derive generic concentration or gradient-residual bounds would duplicate established methods while leaving the actual bridge unchanged.

## Prior reviewed work and navigation

- [Occupancy and calibration certificate 01](https://github.com/Sodelin/Research-Commons/blob/7010e36754590c8c820e7b5acfb683e6ea9312e5/research/2026-10-16-llm-redundancy-certificate/OCCUPANCY-AND-CALIBRATION-01.md).
- [Collision observability and operational-target adapter 02](https://github.com/Sodelin/Research-Commons/blob/a7aaf12c6238687ca950a145d6eeecfa4ae8c3cc/research/2026-10-16-llm-redundancy-certificate/COLLISION-OBSERVABILITY-02.md).
- [Original LLM/Thue–Morse connection audit](https://github.com/Sodelin/Research-Commons/blob/5244f8d76f54f5502534278b46a60952ac168ca8/research/2026-10-15-connection-dossiers/llm-training-data-and-thue-morse.md).

No general LLM training problem is closed by this audit. No additional Thue–Morse-to-training guarantee is inferred from the existing exact-label benchmark.
