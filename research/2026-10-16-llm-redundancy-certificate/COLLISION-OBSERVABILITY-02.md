# Observed collisions versus embedding-only redundancy: next adapter boundary

16 October 2026. dot (OpenAI). Scoped coordinating hand-reviewed follow-on argument. No new estimator-optimality or novelty claim.

## 1. An empirical variance certificate when true classes are observed

Assume the actual finite positive mixture model from [certificate01](./OCCUPANCY-AND-CALIBRATION-01.md), and assume reliable equality of true semantic class labels is observed. Keep the class relation fixed across all samples. Draw independent pairs and independent triples from the same population, using disjoint iid document draws. Let

A_j=1{Z_(j,1)=Z_(j,2)}, j=1,...,B_2,
B_j=1{Z_(j,1)=Z_(j,2)=Z_(j,3)}, j=1,...,B_3.

Then E A_j=p_2=Σw_i² and E B_j=p_3=Σw_i³. For δ_2,δ_3 in(0,1), define

r_k=sqrt(log(2/δ_k)/(2B_k)), k=2,3,

and clipped intervals [L_k,U_k]=[max(0,mean_k−r_k),min(1,mean_k+r_k)].

Hoeffding and a union bound imply simultaneous coverage at least1−δ_2−δ_3. On that event,

Var(W)=p_3−p_2²≤U_3−L_2².

Therefore the nonnegative bound v_bar=max(0,U_3−L_2²) covers the variance on the same event. If U_3<L_2², no actual mixture fits both confidence intervals: flag confidence/model inconsistency and return no scientific label. Do not silently interpret that contradictory region as proof of zero variance.

To plug this into certificate01, intersect its observation/calibration coverage event with this event and sum the failure budgets. Independence between these coverage events is not required, although each individual Hoeffding statement retains its own independent-draw premise. If the later statistic or model is adaptively selected using these samples, its confidence guarantee must account for that selection.

This supplies the requested variance premise conditionally on true observable classes. It does not establish that an embedding threshold or hand-labelled transformation pair is an error-free class oracle.

## 2. Direct estimation is simpler for the stated target

The pair interval already certifies p_2 directly; K_eff=1/p_2 lies in[1/U_2,1/L_2], using an infinite upper endpoint if L_2=0. To certify K_eff≥K_0 use U_2≤1/K_0; for K_eff<K_0 use L_2>1/K_0; otherwise abstain.

Thus, if pair equality is reliably observable, the whole q_N/nearest-neighbor inversion and its variance requirement are unnecessary for this target. The triple estimate may diagnose heterogeneity or validate a chosen approximation, but it is not a prerequisite for direct diversity estimation.

This disjoint-block baseline is not claimed sample-optimal. Collision U-statistics exploit all observed repetitions and have established theory. [Acharya et al.](https://arxiv.org/abs/1408.1000), [Obremski–Skorski2017](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.APPROX-RANDOM.2017.20), and the introduction of [Wang2026v1](https://arxiv.org/html/2610.10389v1) establish the relevant prior boundary. No new general diversity estimator is proposed here.

## 3. Exact embedding-only obstruction under an unrestricted latent observation model

**Proposition.** If the admissible model allows distinct latent classes to have the same embedding distribution, neither unlimited embedding observations nor zero size-biased weight variance identifies K_eff.

**Construction and proof.** Fix M≥2 distinct unit embedding vectors e_1,...,e_M, and let the observed embedding E be uniform over them.

Model A has latent class Z in{1,...,M}, uniformly distributed, and E=e_Z. Then p_2=1/M and K_eff=M.

For any integer R≥2, Model B has latent class Z=(J,V), uniform over{1,...,M}×{1,...,R}, and E=e_J. Then p_2=1/(MR) and K_eff=MR.

Both models give exactly the same law for every finite iid embedding sample, hence for every measurable nearest-neighbor statistic computed from it. In each model all class weights are equal, so Var(W)=0. Every class has positive weight. Increasing M makes all weights arbitrarily small without changing the observational equivalence. ∎

For any threshold strictly between M and MR, a randomized test based only on these embedding samples has worst-case error at least1/2: the output distribution is identical while the correct labels are opposite. This remains true for any procedure observing the entire infinite iid embedding sequence; both product laws are the same.

**Precise scope.** This is an identifiability counterexample for an unrestricted latent-to-embedding channel. It is not a claim that the paper's empirically chosen encoder has these components, nor that every semantically justified source model admits the refinement. A restriction making semantic labels identifiable from the observable channel, or trustworthy external calibration that distinguishes these cases, can exclude the construction. Such a restriction must be stated and validated. Artificial latent splitting need not correspond to a scientifically meaningful new semantic class.

This construction also explains why a variance bound alone cannot replace semantic calibration. The two models need not share the same admitted calibration constants/discrepancy promise in certificate01, so they do not contradict that theorem.

## 4. Exact scientific conclusion and next admission gate

There are three distinct cases:

1. **True class equality observed:** use established collision estimators directly. G6 offers reusable target/coverage bookkeeping; no new open mathematical estimation problem was established.
2. **Only embeddings observed and latent observation channel unrestricted:** exact target identifiability fails by the construction above.
3. **Embeddings with a restricted validated semantic observation model:** certificate01 offers a conditional useful interface. The remaining scientific work is to specify and validate this middle model. Neither these notes nor the underlying LLM paper supplies a complete quantitative calibration/transport guarantee for arbitrary corpora.

A practical admission packet would name the semantic equivalence relation, encoder and population, sampling unit, calibration sampling design, label-error/transport assumptions and numerical discrepancy guarantee. Where classifications are inconsistent or nontransitive, the finite latent-partition model itself needs revision. No training run, data collection or classifier oracle is fabricated here.

This completes the requested pair/triple theorem attempt and gives a decisive obstruction for the unrestrained embedding-only alternative. It does not close a general LLM problem or assert that all useful intermediate models are impossible.


## 5. A different observable target using the paper's threshold relation

The paper's Definition5.1 declares effective duplication by a model-dependent similarity threshold. Such a relation need not be transitive. For example unit vectors at angles0,π/6,π/3 have adjacent cosine√3/2>4/5 but endpoint cosine1/2<4/5. Therefore thresholding alone does not supply the partition in Sections1–3.

There is nevertheless a direct operational version of the certificate. Let R(x,y) be any fixed measurable binary relation on iid documents, and let d(x)=P(R(x,X′)=1), where X′ is an independent document. Define p_R=E d(X), and q_R,N as the chance a designated document relates to at least one of N−1 fresh documents. Conditional independence given the designated document yields exactly

q_R,N=E[1−(1−d(X))^(N−1)].

The proof of Proposition2 in certificate01 applies verbatim with d(X) replacing W. Thus a bound on Var(d(X)) gives the same interval for p_R. Moreover independent pair blocks estimate p_R, while independent three-document blocks with indicator R(X1,X2)R(X1,X3) estimate s_R=E d(X)². Hence Var(d(X))=s_R−p_R² has the same simultaneous-confidence bound as Section1. The triple event is a shared-anchor two-edge star; requiring all three pairwise relations would be a different statistic when R is not transitive.

This is an elementary conditioning/graph-density identity, not a new graphon theorem. For symmetric R it is the edge/star moment identity from classical graphon theory; see [Lovász, Large Networks and Graph Limits](https://lovasz.web.elte.hu/bookxx/hombook-almost.final.pdf), Chapter7 homomorphism densities. Our proof above gives the complete required identity directly.

The operational target 1/p_R must be labelled reciprocal pair-redundancy, not latent Simpson size, unless R is independently known to be equality of the admitted latent classes. It may be infinite if p_R=0. Fix the model, score, threshold, tokenizer and zero-vector convention before sampling. For gradient-cosine R, computing gradients is additional model access and is not supplied by stored embedding vectors. For embedding-cosine R, the result certifies that encoder's geometry only. No experiment is executed here.

This operational application removes semantic-label calibration only by explicitly changing the target. It does not solve semantic recovery, guarantee training improvement or replace the original latent-target certificate. Direct pair estimation again remains the simpler baseline when pair scores can be observed.

## Review record

16 October 2026: the coordinating reviewer read the complete note including Section5 and checked the pair/triple identities, latent refinement construction and nontransitive threshold example under the stated premises. Scoped hand acceptance only; no novelty, execution or solved-open-problem claim.
