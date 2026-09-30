# Dominated experiments: arbitrary parameters and standard-Borel observations

Contributor: /root/current_stat_scope_audit, 2026-09-30 UTC. Written theorem/proof extension for GENERAL-TRANSFER-01. No GitHub mutation, Lean execution, empirical model validation or historical novelty claim.

## 0. Decision brief

The earlier finite-observation comparison theorem extends to **any measurable source observation space dominated by one probability measure, an arbitrary parameter set, and any nonempty standard-Borel target observation space**. One parameter-independent kernel minimizes directional total-variation deficiency. Its value equals the largest optimal Bayes-risk disadvantage across all finitely supported priors and all bounded finite-action tasks.

This closes the finite-alphabet restriction within a substantial explicit class. It does not close comparison for every nondominated experiment, arbitrary pathological measurable targets, computable/cost-constrained simulation, or empirically justified correspondence between scientific domains. The result belongs to classical Blackwell–Le Cam comparison theory; the contribution here is a fully stated proof and dependency audit for the project.

## 1. Exact theorem and assumptions

Let Theta be any nonempty set, without a cardinality restriction. Let (X,Sigma) be a measurable space. Suppose one probability measure mu satisfies P_theta << mu for **every** theta. Let Y be a nonempty standard-Borel space and Q_theta probability laws on Y. Define

```math
\delta(E,F)=\inf_{K:X\leadsto Y}\sup_{\theta\in\Theta}
\operatorname{TV}(KP_\theta,Q_\theta),
\qquad \operatorname{TV}(P,Q)=\sup_A|P(A)-Q(A)|.
```

K is one measurable Markov kernel, independent of the unknown parameter. For a finitely supported prior pi, finite nonempty action set A, and loss L:Theta×A->[0,1], let B_E(pi,L) be the optimal Bayes risk over measurable randomized rules. Then

```math
\boxed{
\delta(E,F)
=\min_{K:X\leadsto Y}\sup_\theta\operatorname{TV}(KP_\theta,Q_\theta)
=\sup_{\substack{\pi\text{ finitely supported}\cr A\text{ finite},\ 0\le L\le1}}
\bigl[B_E(\pi,L)-B_F(\pi,L)\bigr].
}
```

Consequently delta(E,F)=0 iff one K reproduces every Q_theta exactly, iff E is no worse in every finite-action bounded-loss decision problem for every finitely supported prior. For delta<=epsilon, that same minimizing K transfers **any** measurable decision rule on F with pointwise [0,M]-loss risk discrepancy at most M epsilon. The latter forward statement permits general action spaces whenever its rule/loss is measurable.

No theta-measurability is needed for the displayed finitely supported priors. An extension to arbitrary priors requires a measurable parameter model and measurable losses. A common sigma-finite dominating measure can be converted to an equivalent probability measure, so the probability domination convention does not exclude sigma-finitely dominated families.

## 2. Finite-target lemma: the requested first closure

First take Y finite. Write p_theta=dP_theta/dmu in L1(mu). A kernel is represented by finitely many classes k_y in L-infinity(mu), with k_y>=0 and sum_y k_y=1 almost everywhere. The resulting set C is weak-star compact: each coordinate lies in the weak-star compact unit ball, positivity and normalization are weak-star closed, and a finite product is compact.

For each theta,

```math
(KP_\theta)(y)=\int_X p_\theta(x)k_y(x)\,d\mu(x)
```

is weak-star continuous because p_theta belongs to L1. Hence TV(KP_theta,Q_theta) is continuous and its supremum over arbitrary Theta is lower semicontinuous. A minimizer exists on C.

These equivalence classes represent genuine measurable kernels: choose measurable versions of the finitely many k_y and remove their common measurable mu-null defect set; on that set use a fixed point mass. Domination makes this correction null for **all** P_theta, including uncountably many parameters. It does not choose a different exceptional repair separately for each theta.

For finite S subset Theta, apply convex minimax to

```math
\sum_{\theta\in S,y}v_{\theta y}Q_\theta(y)
-\sum_{\theta\in S,y}\int_Xp_\theta(x)v_{\theta y}k_y(x)d\mu(x),
```

where lambda is a prior on S and 0<=v_theta y<=lambda_theta. The kernel set is compact convex; the dual set is finite-dimensional compact convex; the payoff is continuous affine in each argument. The resulting dual is

```math
\delta(E|S,F|S)=\max_{\lambda,v}
\left[
\sum_{\theta,y}v_{\theta y}Q_\theta(y)
-\int_X\max_{y\in Y}\sum_\theta p_\theta(x)v_{\theta y}\,d\mu(x)
\right].
```

A measurable source maximizing action is obtained by choosing the first maximizing y in a fixed finite order. Interpret v_theta y=lambda_theta u(theta,y); F's identity rule supplies the first utility term and E's optimal rule supplies the second. The universal risk bound supplies the converse inequality. Thus finite-prior Bayes-risk duality holds even though X is infinite.

Finally let d=sup_{S finite} delta(E|S,F|S). Each constraint TV(KP_theta,Q_theta)<=d is closed in compact C, and every finite collection has a common member by the restricted minimum. The finite intersection property produces a single K satisfying every parameter constraint. Therefore delta(E,F)=d, establishing the theorem for finite Y and arbitrary Theta.

## 3. Compact-metric target: kernel compactness without disintegration

Let C be a nonempty compact metric target. Represent a kernel by its positive unital operator

```math
T:\mathcal C(C)\longrightarrow L^\infty(\mu),
\qquad (Tf)(x)=\int_C f(y)K(dy|x).
```

Here the continuous functions are real-valued. Positivity and T1=1 imply ||Tf||_infinity<=||f||_infinity. Put all such T in the product of weak-star compact L-infinity balls indexed by f in C(C), using pointwise weak-star convergence. Linearity, positivity and normalization are closed conditions: test their L-infinity equalities/inequalities against L1 functions. The operator set is compact convex by Banach–Alaoglu and product compactness.

### Why every limit operator is still a genuine kernel

Choose a countable dense rational vector subspace D of C(C) containing 1. Choose measurable versions of Tf for f in D. Outside one measurable mu-null set, all countably many rational linearity relations, positivity relations for nonnegative members of D, norm bounds and T1=1 hold simultaneously.

At such an x the map f->Tf(x) is a bounded rational-linear functional on D. It extends uniquely by continuity to a real-linear functional on C(C). Positivity extends as well: approximate any nonnegative continuous function by D and add a positive rational constant tending to zero to keep the approximants nonnegative. The extension is positive and takes 1 to 1. The Riesz representation theorem supplies a unique Borel probability K_x on C.

All continuous test integrals are measurable in x, by uniform approximation from D. For an open U subset C, continuous nonnegative functions increasing to its indicator show x->K_x(U) is measurable. A monotone-class argument then gives measurability of x->K_x(B) for every Borel B. On the exceptional set choose a fixed point mass. This is a Markov kernel on the original arbitrary measurable X; no conditional-distribution/disintegration theorem for X was assumed. The recovered operator equals T in L-infinity, so all dominated P_theta give the intended pushforward laws.

### Lower semicontinuity in the required TV topology

On compact metric C every Borel probability is Radon, and

```math
\operatorname{TV}(R,Q)
=\sup_{\substack{f\in\mathcal C(C)\cr0\le f\le1}}
\left[\int_C f\,dR-\int_C f\,dQ\right].
```

For a fixed theta and continuous f, the first integral is integral p_theta Tf dmu, a continuous functional in the pointwise weak-star operator topology. TV is therefore a supremum of continuous affine functions and is lower semicontinuous. Its uniform supremum is also lower semicontinuous. A minimizing genuine kernel exists; the finite-intersection argument again gives

```math
\delta(E,F)=\sup_{S\subseteq\Theta,\ S\text{ finite}}\delta(E|S,F|S).
```

TV itself is generally not continuous here. Lower semicontinuity suffices for closed sublevel constraints and existence of a minimum.

## 4. Continuous-test duality still has finite-action witnesses

Fix finite S. For a prior lambda on S and continuous functions v_theta on C satisfying 0<=v_theta<=lambda_theta, define

```math
\Phi(T,\lambda,v)=
\sum_{\theta\in S}\int_Cv_\theta\,dQ_\theta
-\sum_{\theta\in S}\int_Xp_\theta T v_\theta\,d\mu.
```

Maximizing over these tests represents max_theta TV exactly. The operator set is compact convex. The dual set is convex in the finite product of C(C) spaces and a prior simplex, with norm topology; Phi is separately continuous affine. Sion's one-compact-side minimax theorem permits interchanging min and sup, even though the continuous-test set need not be compact.

For a fixed dual tuple put h(x,y)=sum_theta p_theta(x)v_theta(y). The maximal source utility is

```math
\sup_T\sum_\theta\int_Xp_\theta T v_\theta\,d\mu
=\int_X\sup_{y\in C}h(x,y)\,d\mu(x).
```

The <= direction is pointwise. For >=, a countable dense set in C has the same supremum for each x outside the finitely many density defect sets. Choosing its first point within eta of that measurable supremum gives a measurable deterministic rule with utility within eta. This avoids imposing an extra measurable exact-argmax selection hypothesis on X.

Let u_theta=v_theta/lambda_theta for positive-weight states, and set u_theta=0 for zero weights. These are continuous [0,1] utilities. For any eta>0, compactness and uniform continuity yield finitely many actions a_1,...,a_N in C such that every y has an a_j with |u_theta(a_j)-u_theta(y)|<=eta for every theta in S. Pick the first such j measurably from the observed y.

Under F this finite-action rule attains the identity-rule utility within eta. E's optimal utility restricted to these finitely many actions cannot exceed its unrestricted utility. Thus a finite-action loss problem has Bayes-risk difference at least Phi's minimized dual value minus eta. Choose a dual tuple arbitrarily near its supremum, then take eta to zero. This proves

```math
\delta(E|S,F|S)
=\sup_{\substack{\pi\text{ supported on }S\cr A\text{ finite},\ 0\le L\le1}}
\big[B_E(\pi,L)-B_F(\pi,L)\big].
```

The general simulator risk bound proves the opposite inequality. Finite-action separating problems may approach the supremum without attaining it; no exact finite separating witness at the supremal value is asserted. Combining with the finite-intersection step proves the arbitrary-Theta compact-target theorem.

## 5. Any standard-Borel target: repair escaped mass

Choose a measurable isomorphism i:Y->B onto a Borel subset B of a compact metric C, and fix y0 in Y. Such an embedding exists for every nonempty standard-Borel space. Define a Borel map J:C->Y by J(i(y))=y on B and J(c)=y0 outside B. Embed each target law as Qbar_theta=i_*Q_theta.

Every Y-kernel gives a C-kernel by composition with i, so delta(E,Fbar)<=delta(E,F). Conversely every C-kernel K gives a Y-kernel JK and

```math
\operatorname{TV}(JKP_\theta,Q_\theta)
=\operatorname{TV}(J_*KP_\theta,J_*\bar Q_\theta)
\le\operatorname{TV}(KP_\theta,\bar Q_\theta).
```

Thus the two deficiencies are equal. The compact-target minimum is attained, and repairing that minimizer gives a genuine Y-kernel attaining the original optimum. This works even when delta>0 and the compact optimum assigns mass outside B; no unsupported closed-image or zero-escaped-mass premise is needed.

Embedding changes neither optimal finite-action risks nor their loss/prior specification: rules on Y extend to C using an arbitrary default on its complement, and C-rules restrict to B. The compact-target decision characterization consequently proves the full standard-Borel theorem stated in Section 1.

## 6. Dependencies and what this actually closes

The chain of premises is now explicit:

1. Common domination of the **entire** source family gives L1 densities and one shared null-set convention.
2. Compact weak-star operators give a simultaneous simulator rather than unrelated finite-subproblem simulators.
3. Compact-metric Radon laws let continuous tests express TV and provide finite-action approximate witnesses.
4. A Borel embedding and parameter-independent repair extend the result to all standard-Borel targets.
5. The bounded-risk simulator theorem supplies universal decision transfer and its error constant.

No finite parameter restriction remains: Theta may include every allowed network size, every finite level, every declared biological/psychological mechanism or any other chosen scientific grammar, provided its observation family meets the premises. Common domination is a substantive scope condition, not a statement that all conceivable scientific models have it. For example, an uncountable family of point masses on an uncountable standard-Borel space has no common dominating probability measure.

The theorem supplies an existence/decision characterization, not an algorithm for evaluating deficiency from an arbitrary model description or learning an unknown scientific bridge. A universally computable checker for unrestricted computable encoders is blocked by the separate halting reduction. Statistical model identification, experiment costs, adaptive acquisition, physical semantics, robust parameter correspondence and historical novelty remain separate obligations.

For ALLLEVEL-STAT-01, full gene-topology experiments at fixed finite taxon sets already lie in the finite/discrete dominated setting. This comparison theorem does not derive their observation-to-displayed-support relation, identify cyclic order, supply a computable classifier or remove their demonstrated indistinguishable pair. It clarifies exactly what a successful simulator/target certificate would have to establish.

## 7. Primary/prior-work checks

- Le Cam (1964), *Sufficiency and Approximate Sufficiency*, Annals of Mathematical Statistics 35(4):1419–1455, DOI 10.1214/aoms/1177700372. Original scanned paper https://scispace.com/pdf/sufficiency-and-approximate-sufficiency-nrxr6jc56j.pdf directly inspected on printed pp.1421–26, 1429–30 and 1449. Theorem 3 gives simultaneous approximate abstract transitions from finite-subset decision comparisons for arbitrary parameter sets; Remark 1 permits finite decision spaces. Proposition 19 realizes a transition as an ordinary Markov kernel for a dominated source and locally compact sigma-compact Radon target. A standard-Borel target has such a Borel-isomorphic model (uncountable: [0,1]; countable: discrete). Therefore this note's dominated standard-Borel closure is already classical, including its approximate scope. The source uses the full variation/L-space norm; its epsilon is not silently identified with the half-L1 TV convention in Section 1. See abstract-bridge.md for the normalization and the abstract/ordinary boundary.
- Sion (1958), *On General Minimax Theorems*, Pacific Journal of Mathematics 8:171–176, DOI 10.2140/pjm.1958.8.171. Primary publisher PDF https://msp.org/pjm/1958/8-1/pjm-v8-n1-p14-p.pdf inspected: Theorem 3.4 and its one-compact-side corollary on printed p.174 justify the minimax interchange used here. Banach–Alaoglu, Radon–Nikodym, Riesz representation and standard-Borel embedding are explicitly invoked classical prerequisites; they are not new project results.
- Raginsky (2011), *Shannon Meets Blackwell and Le Cam: Channels, Codes, and Statistical Experiments*, author manuscript https://maxim.ece.illinois.edu/pubs/raginsky_ISIT11.pdf, previously inspected Sections II–III and Theorem 2. Supplies inspected kernel/TV/deficiency orientation and data-processing background. This note proves its specific dominated compactness/duality claim explicitly rather than borrowing an unrestricted attainment assertion.
- Fritz, Gonda, Perrone and Rischel (2023), *Representable Markov Categories and Comparison of Statistical Experiments in Categorical Probability*, DOI 10.1016/j.tcs.2023.113896. Accepted manuscript https://pure.strath.ac.uk/ws/portalfiles/portal/163006824/Fritz_etal_TCS_2023_Representable_Markov_categories_and_comparison_of_statistical_experiments.pdf previously inspected, especially Theorem 5.13 and Proposition 5.19. Its prior-dependent/prior-independent distinction remains relevant outside this theorem's common-domination conditions; no contradiction is claimed.
- Khan, Yu and Zhang (2025), *A Simple Proof of Blackwell's Theorem on the Comparison of Experiments for a General State Space*, Economics Letters 247:112146, DOI 10.1016/j.econlet.2024.112146. Primary publisher abstract/indexed introduction retrieved, including its domination and finite-intersection scope; direct full-text opening failed. Its existence is a strong prior-work warning against treating the present extension as a discovery. Exact detailed theorem matching was not completed from full text.

This is established statistical comparison territory. There is no exhaustive priority search and no claim that the compactification repair or the proof packaging is historically new.

## 11. Process-integrity assessment

Proof dependencies, domination, null-set repair, operator-to-kernel representation, TV lower semicontinuity, finite-intersection compatibility, minimax hypotheses and finite-action approximation are written explicitly. The initial finite-target component was extended rather than substituted for the requested stronger scope. Primary minimax and relevant original Le Cam pages were directly inspected; the 2025 matching prior's full text was not opened. No proof assistant or automated infinite-dimensional test was run. Independent hand-review of Sections 1–6 is recorded in REVIEW-dominated.md; this subsequent prior-work update changes no proof claim or hypothesis.

## 12. Inference robustness

The result is exact conditional mathematics, not a pooled effect size or evidence that a scientific correspondence holds. Removing source domination, allowing a pathological target sigma-algebra, requiring computable or inexpensive kernels, changing the observable joint law, or restricting the action/loss menu can change necessity, attainability or practical usefulness. The completed dominated theorem therefore does not license an unrestricted all-sciences positive-transfer claim. A stronger claim must earn its own assumptions or impossibility certificate.
