# Statistical transfer: universal decision guarantees and their limits

Contributor: current_stat_scope_audit, 2026-09-30 UTC. For GENERAL-TRANSFER-01. This is a hand-written proof and targeted primary-source audit. No Lean execution, empirical bridge validation or historical novelty claim.

## Verdict and strongest scope

There is an existing universal mathematical answer to whether one observation system can replace another for **every statistical decision task**: Blackwell comparison and Le Cam deficiency. The key object is one parameter-independent simulator, not visual similarity between models. The exact finite-alphabet characterization below covers an **arbitrary parameter class**, including uncountably many scientific models, and all bounded finite-action decision tasks simultaneously. It is not restricted to a finite candidate-model toy.

For arbitrary measurable observations, the forward risk guarantees, composition and impossibility statements remain valid whenever the stated kernels exist. A necessity theorem needs additional regularity or altered quantifiers: prior-dependent almost-sure simulators are generally weaker than one simulator valid at every parameter. Neither version discovers or empirically validates the relationship between biological, psychological or other scientific models.

## 1. Declare the relationship before claiming transfer

An experiment E is a family (P_theta) of observation laws on X, indexed by an unknown parameter theta in Theta. A comparison experiment F has laws (Q_theta) on Y over the **same** parameter class.

If the sciences initially use different parameters alpha and beta, declare an admissible relation R contained in Theta_E × Theta_F, then use Theta = R and P_(alpha,beta) = P_alpha, Q_(alpha,beta) = Q_beta. The theorem consequently quantifies over every admitted matched pair. Choosing one convenient correspondence after seeing outcomes changes the scientific claim. A transfer kernel cannot secretly receive theta, alpha or beta.

A Markov kernel K from X to Y is one randomized, observation-only procedure. Its pushforward is KP_theta. Define total variation by

```math
\operatorname{TV}(P,Q)=\sup_A|P(A)-Q(A)|.
```

For finite alphabets this equals one half of the sum of absolute probability differences. Define directional deficiency and symmetric distance by

```math
\delta(E,F)=\inf_K\sup_{\theta\in\Theta}\operatorname{TV}(KP_\theta,Q_\theta),
\qquad
\Delta(E,F)=\max\{\delta(E,F),\delta(F,E)\}.
```

Direction matters: small delta(E,F) means E can imitate F. Small Delta means decision procedures can transfer in both directions. Neither quantity is a measure of whether two theories have similar wording or pictures.

## 2. Universal bounded-risk transfer: arbitrary measurable observations

Assume K satisfies sup_theta TV(KP_theta,Q_theta) <= epsilon. Let D be any randomized decision rule from Y to an action space A. Let L(theta,a) have range in [0,M] and be measurable where needed. Compose D with K. For **every** theta,

```math
|R_E(\theta,DK)-R_F(\theta,D)|\le M\epsilon.
```

Proof: f_theta(y) = integral L(theta,a) D(da|y) lies in [0,M]. The expectation difference of a bounded function with this range is at most M times TV. This applies to every D and L using the **same K**. Taking infima over K gives an arbitrarily small additional slack when the deficiency infimum is not attained. Unbounded losses need integrability/tail conditions and do not inherit this bound automatically.

This is a true cross-domain theorem whenever the two scientific experiments and their common relation have been justified. It does not supply that justification.

## 3. Exact maximal finite-alphabet characterization, arbitrary Theta

Assume X and Y are finite, nonempty sets; Theta is any nonempty set. No finiteness or cardinality limit is imposed on Theta. Write K(y|x) for a row-stochastic matrix. For a finitely supported prior pi on Theta, a finite action set A and loss L:Theta×A->[0,1], define Bayes risk

```math
B_E(\pi,L)=\min_D\sum_\theta\pi_\theta R_E(\theta,D).
```

Then

```math
\boxed{
\delta(E,F)
=\min_K\sup_\theta\operatorname{TV}(KP_\theta,Q_\theta)
=\sup_{\substack{\pi\text{ finitely supported}\cr A\text{ finite},\ 0\le L\le1}}
\big[B_E(\pi,L)-B_F(\pi,L)\big].
}
```

Consequently the following are equivalent:

1. There is one K with KP_theta = Q_theta for every theta.
2. E has no greater optimal Bayes risk than F for every finitely supported prior, every finite action set and every bounded loss.
3. For every finite-action rule D on F and every such loss there is a rule on E whose risk is no greater at every theta.

More generally, delta(E,F) <= epsilon iff the universal Bayes-risk difference is <= epsilon. A minimizing simulator earns the pointwise risk-transfer guarantee in Section 2. The reverse pointwise decision-dominance condition implies the Bayes condition, completing the equivalence. Scaling [0,1] losses to [0,M] scales the tolerance by M.

### Proof A: finite restrictions determine the entire arbitrary class

The simplex of stochastic matrices is compact. For each theta, f_theta(K) = TV(KP_theta,Q_theta) is continuous. Its supremum is lower semicontinuous, so the minimum is attained.

Let d = sup_{S finite subset Theta} delta(E|S,F|S). Clearly d <= delta(E,F). Each closed constraint set C_theta = {K:f_theta(K)<=d} lies in the compact kernel simplex. Every finite collection has a common member: the finite restricted optimization attains a value <=d. The finite intersection property gives one K in the intersection over **all** theta. Thus delta(E,F)<=d and

```math
\delta(E,F)=\sup_{S\subseteq\Theta,\ S\text{ finite}}\delta(E|S,F|S).
```

This is the missing compatibility step: solving every finite parameter restriction yields one simulator valid over the whole class because the admissible finite-alphabet kernel space is compact. Pairwise comparisons alone do not necessarily suffice.

### Proof B: finite restriction duality and decision interpretation

For finite S, TV is the maximum over test functions in [0,1]. Combining that fact with the maximum over theta, then applying finite-dimensional compact convex minimax, yields

```math
\delta(E|S,F|S)
=\max_{\lambda,v}
\left[
\sum_{\theta,y}v_{\theta y}Q_\theta(y)
-\sum_x\max_y\sum_\theta v_{\theta y}P_\theta(x)
\right],
```

where lambda_theta>=0, sum_theta lambda_theta=1, and 0<=v_theta y<=lambda_theta. To see the minimax form, start from sum_theta y v_theta y [Q_theta(y)-sum_x P_theta(x)K(y|x)]. Maximizing over lambda,v represents max_theta TV. Minimizing over K subtracts the maximum linear utility in each row, giving the displayed expression.

Set prior pi=lambda and utility u(theta,y)=v_theta y/lambda_theta when lambda_theta>0; arbitrary values in [0,1] suffice for zero-weight theta. Under F the identity action y gives the first term, while the optimal utility under E is the second term. F's optimal utility is at least its identity-rule utility. Hence some decision problem has Bayes-risk difference at least the dual value. Section 2 proves that no decision problem has difference greater than deficiency. Equality follows on finite S; Proof A and finite-support priors complete the arbitrary-Theta theorem. Actions Y already suffice for the separating witness.

This is a classical comparison-of-experiments result with an explicit compactness extension, not a new general transfer theorem claimed by this project.

## 4. Target preservation is weaker than preserving every task

Let g:Theta->Z be the desired scientific answer. **Law-level identifiability** means

```math
P_\theta=P_{\theta'}\ \Longrightarrow\ g(\theta)=g(\theta').
```

This condition is necessary for learning g even with indefinitely many IID repetitions. It is not itself a finite-sample recovery theorem, a quantitative separation bound or a guarantee of uniform consistency over an infinite model class.

Define the exact target experiment G by G_theta=Dirac(g(theta)). With a finite target alphabet,

```math
\delta(E,G)=\inf_D\sup_\theta\Pr_\theta\{D(X)\ne g(\theta)\}.
```

Thus deficiency to G is the infimum worst-case error of answering this particular target; it need not preserve other decisions about theta. For finite X and finite target alphabet the infimum is attained by compactness; attainment is not assumed for general measurable X. Identifiability alone does not imply delta(E,G)=0 for a single noisy observation. Distinct overlapping laws are identifiable at the population-law level while exact single-sample decoding remains impossible.

Example: theta=(a,b), E observes both bits exactly, and T(E) retains only a. This representation preserves g(theta)=a perfectly, but loses all information needed for the task b. A claim covering **all future targets** cannot infer sufficiency from success on one present target.

For a fixed model, preserving every decision task still need not retain every raw bit. If X=(theta,U) and U is independent noise of known law, retaining theta and regenerating U simulates X exactly. More generally, a statistic is universally decision-sufficient when a theta-independent reconstruction kernel recovers the original observation law. In the finite model, the classical minimal sufficient deterministic partition groups outcomes with proportional likelihood vectors (P_theta(x))_theta, ignoring impossible outcomes. That is model-relative compression, not an assumption-free compression of every possible science.

## 5. Tight obstruction and data-processing certificates

For two parameters with different binary targets, let v=TV(P_0,P_1). For any randomized test with errors e0,e1,

```math
e_0+e_1\ge1-v,
\qquad
\max(e_0,e_1)\ge(1-v)/2.
```

The equal-prior **average** error optimum is exactly (1-v)/2; the worst-case lower bound need not be attained for every asymmetric pair. Proof: for rejection probability f in [0,1], e0+e1=1-(E_1 f-E_0 f), whose optimum is 1-TV.

If P_0=P_1 and the targets differ, the worst-case binary error is at least 1/2 at every IID sample size. Relabeling, embedding, reasoning, linking notes or deterministic data processing cannot remove this obstruction because KP_0=KP_1 for every K.

More generally, for any comparison target laws Q_0,Q_1,

```math
\delta(E,F)\ge\tfrac12
\left[\operatorname{TV}(Q_0,Q_1)-\operatorname{TV}(P_0,P_1)\right]_+.
```

Proof: triangle inequality between Q0,KP0,KP1,Q1 plus TV contraction under K. In particular, if the declared cross-science relation matches the same source parameter to two distinct target laws, deficiency is at least half their distance. This exposes ambiguity in the bridge rather than pretending a chosen correspondence is uniquely supported.

For m IID repetitions,

```math
\operatorname{TV}(P_0^{\otimes m},P_1^{\otimes m})
\le1-(1-v)^m\le\min\{1,mv\}.
```

The first bound needs no coupling existence assumption: relative to the dominating measure mu=P0+P1, let H have density min(dP0/dmu,dP1/dmu). Then H is a common submeasure of mass 1-v, and its product H^m is a common submeasure of the two product laws with mass (1-v)^m. Their TV is therefore at most 1-(1-v)^m. Bernoulli's inequality gives the second bound. Hence average binary error is at least (1-v)^m/2. This bound is tight: P0=Dirac(0), P1=(1-v)Dirac(0)+v Dirac(1). Identical laws have v=0, so repetition gives no improvement. IID assumptions are essential; a dependence structure may change the full observation experiment.

Equal component marginals do not mean equal joint laws. Uniform distributions on {00,11} and {01,10} have identical one-coordinate marginals but disjoint joint supports, with parity perfectly revealing the parameter. Any all-level observation audit must preserve this distinction.

## 6. Approximation across many levels and repeated samples

For experiments over the same Theta,

```math
\delta(E,G)\le\min\{1,\delta(E,F)+\delta(F,G)\}.
```

Compose near-optimal kernels and use TV contraction and triangle inequality. Along any finite chain of scientific levels, the certified risk distortion is bounded by the sum of declared directional deficiencies times the loss range. A claim about an infinite chain needs a convergent error budget and an independently justified limiting experiment/kernel; arbitrary finite-chain validity does not construct a limit.

For IID products, applying the same kernel independently yields

```math
\delta(E^{\otimes m},F^{\otimes m})
\le1-(1-\delta(E,F))^m
\le\min\{1,m\delta(E,F)\}.
```

Use a near-optimal single-observation K, then take its slack to zero. This is an **upper bound for a particular simulation construction**, not a statement that error necessarily accumulates at that rate or that an optimal joint simulator cannot do better. Correlated observations need a joint-law simulation certificate. Arbitrary adaptive measurement sequences similarly need conditional/history-uniform kernels; marginal one-step bounds alone do not certify a sequential law.

## 7. Why universal compression can fail

If a deterministic representation T merges x0 and x1, and the claimed model class includes Dirac(x0) and Dirac(x1), their compressed laws coincide. The original experiment separates the two states perfectly; the compressed representation has worst-case binary error at least 1/2 and reverse deficiency at least 1/2. Thus no many-to-one representation is universally lossless over an unconstrained class containing all point-mass states and all target decisions.

The useful strongest aim is therefore a **model-declared, target-declared or resource-declared** preservation theorem with exact error accounting. A universal theorem may characterize when transfer is possible and certify when it is impossible. It need not promise compression for every model.

## 8. Infinite observation spaces: do not hide the quantifier change

Sections 1–2 and 5–7 hold for measurable experiments with valid Markov kernels and the necessary loss measurability. Section 3's necessity/attainment argument uses compactness of the finite-alphabet kernel simplex. It cannot be imported unchanged to arbitrary infinite observation spaces.

Fritz–Gonda–Perrone–Rischel (2023), Theorem 5.13, establishes a standard-Borel comparison for a fixed prior with almost-sure equality. Corollary 5.15 removes the almost-sure qualification for discrete parameter spaces with a full-support prior. Their Proposition 5.19 gives a counterexample to upgrading prior-dependent simulability over arbitrary standard-Borel hypotheses into one prior-independent garbling. This is a genuine quantifier/regularity boundary, not merely missing compute.

Accordingly GENERAL-TRANSFER-01 should register separately: (i) the arbitrary-Theta finite-alphabet necessary-and-sufficient theorem above; (ii) kernel-certified universal forward transfer on general measurable observations; (iii) necessity under explicitly stated domination/regularity, or a prior-relative variant; and (iv) concrete empirical bridge construction and validation. None substitutes for the others. Quantizing infinite data first introduces another experiment and must receive its own preservation bound.

## 9. Primary-source and prior-work audit

- Blackwell (1953), *Equivalent Comparisons of Experiments*, Annals of Mathematical Statistics 24:265–272, DOI 10.1214/aoms/1177729032. Original publisher full-text/PDF endpoints were attempted but blocked by a security wall. Do not claim full-text inspection of this original.
- Le Cam (1964), *Sufficiency and Approximate Sufficiency*, Annals of Mathematical Statistics 35:1419–1455, DOI 10.1214/aoms/1177700372. Metadata verified; original full proof not recovered. Do not attribute this note's detailed normalization/proof to a source passage not inspected.
- Raginsky (2011), *Shannon Meets Blackwell and Le Cam: Channels, Codes, and Statistical Experiments*. Author-hosted primary research manuscript: https://maxim.ece.illinois.edu/pubs/raginsky_ISIT11.pdf . Read definitions in Sections II–III and data-processing Theorem 2. This supplies inspected source support for kernel orientation, TV convention, deficiencies and contraction. This note's finite-alphabet minimax/compactness proofs stand explicitly above.
- Fritz, Gonda, Perrone and Rischel (2023), *Representable Markov Categories and Comparison of Statistical Experiments in Categorical Probability*, Theoretical Computer Science 961:113896, DOI 10.1016/j.tcs.2023.113896. Inspected accepted author manuscript: https://pure.strath.ac.uk/ws/portalfiles/portal/163006824/Fritz_etal_TCS_2023_Representable_Markov_categories_and_comparison_of_statistical_experiments.pdf . Read Theorem 5.13, Corollary 5.15, Proposition 5.19 and the prior-dependence discussion. Broad categorical comparison is established prior work; it cannot be relabeled as this project's new discovery.

## 11. Process integrity

Targeted theorem audit, not a systematic review. Search covered original Blackwell/Le Cam metadata, an author-hosted primary comparison paper, and a peer-reviewed primary categorical extension. Original full-text access was incomplete and is disclosed. Mathematical claims are hand-derived with explicit assumptions; no proof-assistant receipt is asserted. The greatest remaining verification obligation is independent checking of the finite minimax/compactness proof and any proposed infinite-space necessity extension.

## 12. Robustness and what would change the conclusion

The finite-alphabet equivalence is an exact mathematical statement, not a pooled empirical effect; GRADE, heterogeneity estimates and meta-analysis are inapplicable to its proof. Its scientific usefulness is conditional on observation laws, parameter correspondence, losses and resource budget. It changes if any of those change. Unknown bridge error, same-data model selection, unbounded loss, joint dependence, unmeasurable decision rules or exchanging all-priors/prior-independent quantifiers can invalidate a promised guarantee. Empirical support for a cross-science bridge requires separate data and falsifiable checks; theorem generality alone supplies no empirical confidence.
