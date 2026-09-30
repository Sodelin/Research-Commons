# Ordinary transfer on arbitrary measurable spaces

Author: /root. Date: 2026-09-30 UTC. A general representation criterion, not a historical novelty or a terminating feasibility algorithm.

## 0. What remains valid without domination or standard-Borel targets

The finite-prior decision-gap theorem does not universally characterize ordinary kernels outside its realization assumptions. There is nevertheless an exact representation criterion for **every** pair of ordinary measurable observation spaces. Its additional requirements are actual measurable outputs and pointwise countable additivity. It is useful for exposing the obstruction, but it is not a shortcut for checking arbitrary scientific models.

## 1. Complete ordinary representation criterion

Let X,Y be any nonempty measurable spaces, Theta any nonempty index set, and P_theta,Q_theta probability laws on X,Y. Write B_b(X) and B_b(Y) for real bounded measurable functions. For prescribed errors epsilon_theta>=0, the following are equivalent:

1. There is one measurable Markov kernel K:X -> Y with TV(KP_theta,Q_theta)<=epsilon_theta for every theta.
2. There is one linear map T:B_b(Y) -> B_b(X) satisfying these requirements:
   - T is positive and T1=1, as **pointwise** functions on X.
   - For every sequence of measurable sets A_n decreasing to the empty set, T1_{A_n}(x) decreases to zero for **every x**.
   - For every theta and every bounded measurable f:Y -> [0,1],

```math
\left|\int_X Tf\,dP_\theta-\int_Y f\,dQ_\theta\right|
\le\epsilon_\theta.
```

The first bullet together with the codomain B_b(X) encodes positivity, normalization and ordinary measurability. The second is continuity from above for indicators; it is equivalent here to pointwise order continuity for bounded nonnegative sequences decreasing to zero. These are actual function representatives, not arbitrary equivalence classes modulo a parameter-dependent null set.

### Proof: kernel to operator

Set Tf(x)=integral f(y) K(dy|x). Kernel measurability and bounded measurable approximation give Tf in B_b(X); positivity, linearity and normalization are immediate. Continuity from above holds for each probability K_x. The last inequality is the bounded-test characterization of TV. This construction is independent of theta.

### Proof: operator to kernel

For each x define K_x(A)=T1_A(x) for all measurable A in Y. Positivity and normalization make K_x nonnegative with mass one, and linearity gives finite additivity. The prescribed continuity from above makes each finitely additive K_x countably additive: for disjoint A_j, the union of the terms after the first n decreases to the empty set, and finite additivity followed by the indicated limit gives K_x(union_j A_j)=sum_j K_x(A_j). Thus each K_x is a probability measure.

For each measurable A, x -> K_x(A)=T1_A(x) is measurable by the actual codomain condition. Hence K is a Markov kernel on the original spaces; no disintegration, source domination, target separability or measurable-parameter assumption is needed.

Positivity and T1=1 give the contraction ||Tf||_infinity<=||f||_infinity. T agrees with kernel integration on simple functions by linearity. Every bounded measurable real function is uniformly approximable by simple functions, so contraction proves agreement for every f in B_b(Y). The final operator inequality consequently is exactly the claimed TV bound. This proves equivalence at each prescribed error tolerance, including zero.

## 2. Deficiency and its limitation

For the full class C of operators satisfying the measurable, positive, unital and continuity requirements above,

```math
\inf_{K:X\leadsto Y}\sup_\theta\operatorname{TV}(KP_\theta,Q_\theta)
=\inf_{T\in C}\sup_{\theta,\ 0\le f\le1}
\left|\int Tf\,dP_\theta-\int f\,dQ_\theta\right|.
```

This follows from the proved kernel/operator correspondence and holds for every such measurable-space instance. No attainment is asserted in this unrestricted category. The statement that the infimum is zero does not replace existence of a T satisfying the exact constraints. The dominated standard-Borel compactness theorem separately supplies attainment and a decision-gap formula in its valid class.

One admissible T transfers every measurable bounded decision by composition, with the corresponding TV risk bound. A finite-prior risk comparison alone need not produce a T with these pointwise consistency requirements: abstract-bridge.md's non-Borel labeling example makes its supremal ordinary finite-prior gap zero while its ordinary kernel deficiency is 1/2.

## 3. Positivity alone permits the wrong object

To see the countable-additivity requirement, let X be a singleton and Y the natural numbers with all subsets measurable. A free ultrafilter U on Y gives a positive unital linear functional T(f)=lim_U f on bounded sequences. For each cofinite tail A_n={n,n+1,...}, T1_{A_n}=1 although A_n decreases to the empty set. There is no probability measure whose integral functional equals this T. It describes a finitely additive object, not an ordinary kernel. This illustrative example uses the usual axiom-of-choice set-theoretic setting.

Likewise, an abstract experiment's dual M(E) can contain functions that are not measurable on its original sample-space representation. The non-Borel example fails this measurability requirement instead. Either omission invalidates ordinary realization.

## 4. Honest meaning of full generality

This proves a necessary-and-sufficient **representation criterion** for all ordinary measurable-space instances, while the abstract Le Cam theorem supplies an all-abstract-experiment decision criterion. The ordinary criterion still quantifies over an infinite functional object and its countable-additivity constraints. It is not a classification obtained from finite data, a decision-duality theorem without assumptions, a cheap construction or a solution of biological observation fibers. The separate computability reduction forbids a universally terminating feasibility checker for unrestricted program-defined models.

Established representation principles supply the baseline formal generality. Scientific and resource generality requires verified source laws, target meanings, available observations and effective premises; none follows from representing every instance in one notation.

## 11. Process integrity

The criterion is hand-proved from elementary kernel integration and the continuity-from-above characterization of countable additivity. All quantifiers and actual-function measurability are explicit. No historical novelty, empirical validation, formal-assistant run or universal algorithm is asserted. Independent review is to be recorded separately.

## 12. Inference robustness

The equivalence covers arbitrary observation sigma-algebras and parameter sets, including nondominated families. That scope is bought by explicit pointwise measurable/order-continuous operator requirements, not by dropping ordinary realization requirements. It cannot be used to turn a mere finite-prior decision comparison or a finitely additive transition into a measurable sampling procedure.
