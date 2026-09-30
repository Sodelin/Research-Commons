# All states and entire histories: two transfer upgrades

Author: /root. Date: 2026-09-30 UTC. Supplement to GENERAL-TRANSFER-01; established mathematical mechanisms proved here for the declared project scope. No novelty, empirical correspondence or proof-assistant execution claim.

## 0. What is being closed

An almost-everywhere simulator is not automatically an all-state simulator. Similarly, agreement on a fixed finite history is not automatically agreement on an infinite history. This note supplies sufficient hypotheses and complete arguments for both upgrades, with counterexamples to the assumptions being omitted. It does not infer a simulator from one successful prior test, or infer scientific mechanisms from a representation alone.

## 1. From a full-support prior to every parameter

Let Theta be a nonempty topological space, with its Borel sigma-algebra, and let m be a Borel probability with full support: every nonempty open subset has positive m-mass. Let (X,Sigma) be any measurable source space and let Y be a Polish space with its Borel sigma-algebra. For every theta let P_theta and Q_theta be probability measures on X and Y. Assume:

1. The source family is **setwise continuous**: theta -> integral g dP_theta is continuous for every bounded Sigma-measurable real g.
2. The target family is **weakly continuous**: theta -> integral f dQ_theta is continuous for every bounded continuous real f on Y.
3. One fixed measurable Markov kernel K:X -> Y satisfies TV(KP_theta,Q_theta) <= epsilon outside one m-null Borel set, for epsilon >= 0.

Then that **same K** satisfies the bound for every theta.

### Proof

For each bounded continuous f:Y -> [0,1], Kf is bounded Sigma-measurable. The function

```math
d_f(\theta)=\int_X Kf\,dP_\theta-\int_Y f\,dQ_\theta
```

is continuous by assumptions 1 and 2. If |d_f(theta_0)| > epsilon, its strict-violation set is a nonempty open set. It has positive m-mass, so it contains a parameter outside the exceptional null set. At that parameter the integral discrepancy is greater than epsilon, contradicting assumption 3 and the bounded-test characterization of TV.

Thus |d_f(theta)| <= epsilon for every theta and every such f. Borel probabilities on a Polish space are Radon, and continuous [0,1]-valued tests recover their TV distance. Taking the supremum over these tests proves the claim.

No countable union over all tests or all parameters is used. The argument rules out each putative violating open set separately. Common source domination is not required for this particular **fixed-kernel upgrade**; it can be required by the separate theorem used to obtain a kernel in the first place. An almost-everywhere risk comparison alone is not assumption 3.

### Full support alone is insufficient

Take Theta=[0,1] with its usual topology and Lebesgue prior, X a singleton, P_theta the same point mass for every theta, and Y={0,1}. Set Q_0=delta_1 and Q_theta=delta_0 for theta>0. The constant-zero kernel is exact almost everywhere under a full-support prior, but fails at theta=0. No all-state exact kernel exists because identical source laws would have to produce different target laws. Target weak continuity fails precisely at that exceptional state.

Source continuity is substantive as well. On X={0,1}, take P_0=delta_0 and P_theta=delta_1 for theta>0; set Q_theta=delta_0 for all theta and use deterministic K(1)=0, K(0)=1. Target continuity holds and this K is exact almost everywhere, but not at zero; source continuity fails. Another K may work here: this example refutes the automatic upgrade for the chosen K, not existence of every possible simulator.

## 2. From conditional step guarantees to a whole path

Let S_0,S_1,... be nonempty standard-Borel observation spaces. For each theta in an arbitrary parameter set, suppose P_theta and Q_theta are path laws built from initial distributions on S_0 and specified measurable conditional kernels

```math
p_{\theta,n}(\cdot\mid h),\quad q_{\theta,n}(\cdot\mid h),
\qquad h\in H_{n-1}=\prod_{j=0}^{n-1}S_j,\quad n\ge1.
```

The initial distributions and these kernels determine probability laws on the countable product sigma-algebra by the usual sequential extension theorem. Histories here are in a common output space; these are already the simulator-output and target conditionals, if a simulator is involved. The construction of that simulator and its causal admissibility remain separate premises.

### Complete exact criterion

For each theta, the entire path laws are equal **if and only if** their initial distributions are equal and, for every n>=1, p_{theta,n}(.|h)=q_{theta,n}(.|h) for P_theta^{0:n-1}-almost every history h. This permits a different history-null set for each parameter and time; it does not require the kernels to agree on unreachable histories.

Necessity: equality of path laws gives equality of every consecutive-prefix joint law. For each event in a countable generating pi-system of the standard-Borel next-observation space, equality of its integrals over every measurable history event implies equality of the two conditional probabilities almost everywhere. Taking the union of countably many exceptional sets and applying uniqueness of measures on the generating pi-system yields equality of the entire conditional measures outside one history-null set. Sufficiency: equality of initial laws and those conditional laws gives equality of the next prefix by induction; equality on the finite-prefix cylinder algebra then gives equality of the product laws. Thus the exact criterion covers every specified pair of path laws, including undominated parameter families. It does not produce the requisite conditional laws from unknown empirical data.

### Uniform approximate bound

Assume nonnegative numbers epsilon_n, independent of theta, such that

```math
\operatorname{TV}(P_\theta^0,Q_\theta^0)\le\epsilon_0,
\qquad
\sup_{h\in H_{n-1}}
\operatorname{TV}\bigl(p_{\theta,n}(\cdot\mid h),q_{\theta,n}(\cdot\mid h)\bigr)
\le\epsilon_n\quad(n\ge1)
```

for every theta. Set e_n=min{1,epsilon_n}. Then, writing P_theta^{0:n} and Q_theta^{0:n} for prefix laws,

```math
\operatorname{TV}(P_\theta^{0:n},Q_\theta^{0:n})
\le1-\prod_{j=0}^n(1-e_j)
\le\min\left\{1,\sum_{j=0}^n\epsilon_j\right\},
\qquad
\operatorname{TV}(P_\theta,Q_\theta)
\le1-\prod_{j=0}^{\infty}(1-e_j)
\le\min\left\{1,\sum_{j=0}^{\infty}\epsilon_j\right\}.
```

The product is the limit of the decreasing finite products. The multiplicative bound is **sharp for every declared sequence of error budgets**; an attaining example is given below. The infinite sum can diverge, in which case its additive upper bound is simply 1. In particular, exact step agreement at every history and every time gives equality of the entire infinite path laws. Any measurable decision on the full path with loss in [0,M] has risk discrepancy at most M times the displayed whole-path bound.

### One-step proof, retaining history

For prefix laws R and U on H and kernels p,q from H to the next observation space S, write R tensor p for the law on H x S that retains its history. For any Borel event A in H x S,

```math
\left|(R\otimes p)(A)-(R\otimes q)(A)\right|
\le\int_H\left|p(A_h\mid h)-q(A_h\mid h)\right|\,dR(h)
\le\sup_h\operatorname{TV}(p_h,q_h).
```

Kernel contraction also gives TV(R tensor q,U tensor q) <= TV(R,U). The triangle inequality therefore yields

```math
\operatorname{TV}(R\otimes p,U\otimes q)
\le\operatorname{TV}(R,U)+\sup_h\operatorname{TV}(p_h,q_h).
```

This gives the additive corollary. For the stronger bound, let d=TV(R,U) and let H=R meet U be their common submeasure, defined by taking the minimum of their Radon–Nikodym densities relative to R+U. It has mass 1-d. The decomposition

```math
R\otimes p-U\otimes q
=H\otimes p-H\otimes q
+(R-H)\otimes p-(U-H)\otimes q
```

gives an event discrepancy at most (1-d)e+d when sup_h TV(p_h,q_h)<=e. The first difference is bounded by (1-d)e by integrating the conditional event discrepancies; each remaining positive measure has mass d, so their difference on an event has magnitude at most d. The case d=1 is immediate. Consequently

```math
\operatorname{TV}(R\otimes p,U\otimes q)\le d+(1-d)e.
```

This expression is nondecreasing in d for 0<=e<=1. Iteration from d_0<=e_0 proves the multiplicative prefix bound; 1-product_j(1-e_j)<=sum_j e_j gives the additive bound. No measurable selection of maximal couplings is assumed. The uniform-history premise avoids comparing conditional versions only on disjoint almost-sure history sets.

### Passing from prefixes to the infinite path

The finite-prefix events form an increasing union of sigma-algebras, which is an algebra generating the countable product sigma-algebra. For two fixed path laws P,Q, put nu=(P+Q)/2. Every measurable event A can be approximated in nu-symmetric-difference measure by an event B in that generating algebra. For completeness, the class of events with this approximation property contains the algebra, is closed under complements, and is closed under countable unions: for A=union_k A_k first choose a finite union A_1 union ... union A_N with nu(A minus that finite union) small by continuity from below, then approximate its finitely many members. It is consequently the whole generated sigma-algebra.

For such an approximation,

```math
|P(A)-Q(A)|\le |P(B)-Q(B)|+P(A\triangle B)+Q(A\triangle B)
=|P(B)-Q(B)|+2\nu(A\triangle B).
```

Taking arbitrarily good approximations and then the supremum over A proves

```math
\operatorname{TV}(P,Q)=\sup_n\operatorname{TV}(P^{0:n},Q^{0:n}).
```

The reverse inequality follows directly by lifting prefix events to cylinders. Combining this equality with the prefix bounds and the decreasing-product limit gives the whole-path bound. This passage does not require domination of the entire family indexed by theta: nu is used for just one pair at a time, and the conditional bounds already hold for every theta.

### Sharpness and why a small fixed one-step error is inadequate

For any sequence e_n in [0,1], let every S_n={0,1}, let P be the deterministic all-zero path and let Q have independent Bernoulli(e_n) coordinates. Conditional discrepancies are exactly e_n; versions on every history are defined by the same deterministic/independent rules. Q assigns mass product_{j=0}^n(1-e_j) to the all-zero prefix and mass product_{j=0}^infinity(1-e_j) to the all-zero path. Thus both multiplicative bounds are attained. No smaller uniform bound can be deduced from those error budgets alone.

Let every S_n={0,1}, let P be the deterministic all-zero path, and let Q be independent Bernoulli(epsilon) at every time, for 0<epsilon<1. Every conditional one-step TV discrepancy, including the initial step, equals epsilon. Yet Q assigns probability one to observing at least one 1, whereas P assigns probability zero. Whole-path TV is 1. For a prefix of n+1 observations it is 1-(1-epsilon)^(n+1).

Thus per-step accuracy alone does not give a horizon-independent small bound. Summable errors are a sufficient remedy, not a necessary characterization of all pairs: identical laws also satisfy loose, nonsummable declared error budgets. Merely having some exact simulator for each prefix is different again from having a **consistent** sequence of specified kernels constructing one path law.

## 3. Relation to the master target

These results close two concrete extensions omitted by a finite-alphabet, finite-horizon or prior-relative check. They provide all-state and whole-history conclusions once their premises hold. They do not identify the observation laws from biological data, determine interventions from passive correlations, solve arbitrary computational model checking, or show that any two scientific fields share a sufficient observation map.

Le Cam's all-parameter theorem supplies a different route to a simultaneous simulator under its own abstract or dominated-kernel assumptions. It should not be confused with upgrading one prior's chosen simulator by continuity. Likewise, exact deterministic dynamical lumpability supplies an all-integer-time quotient when its transition compatibility is proved; this stochastic path lemma concerns laws, not that deterministic quotient.

## 4. Sources and verification boundary

- Khan, Yu and Zhang (2024), *On comparisons of information structures with infinite states*, Journal of Economic Theory 218:105841, DOI https://doi.org/10.1016/j.jet.2024.105841. Publisher-indexed Corollary 2 motivated checking the full-support/continuity issue. Complete publisher text was not opened. Section 1 is an independently written fixed-kernel proof and does not import unverified assumptions from that article.
- The Radon characterization of TV, kernel contraction and the sequential extension theorem are classical prerequisites explicitly used above. No historical novelty is asserted. Neither a finite simulation nor a proof assistant substitutes for their hypotheses.

## 11. Process-integrity assessment

All quantifiers, continuity requirements, null-set conventions, product sigma-algebra, conditional-version premises and the cylinder-to-path passage are stated. The two omission counterexamples are exact constructions. Independent hand-review is to be recorded in REVIEW-continuity-and-paths.md; no Lean run or empirical test is claimed.

## 12. Inference robustness

The positive results are conditional and uniform in the declared parameters. Full-support priors without the indicated continuity can hide exceptional states. Small nonsummable conditional errors can accumulate to singular infinite path laws. These failures prevent the respective unconditional upgrade; they do not invalidate every application outside the sufficient hypotheses. The actual scientific bridge and computational resource restrictions remain application obligations.
