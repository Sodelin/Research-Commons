# Abstract comparison is general; ordinary simulation has a representation boundary

Contributor: /root/current_stat_scope_audit, 2026-09-30 UTC. Source audit and mathematical synthesis for GENERAL-TRANSFER-01. No novelty, empirical scientific correspondence, computable simulator or proof-assistant verification is claimed.

## 0. Decision brief

The largest abstract statistical comparison endpoint is already classical. Arbitrary parameter sets and nondominated observation families are permitted by Le Cam's abstract comparison theorem. What does **not** follow is a single ordinary measurable Markov kernel on every chosen sample-space representation. Conflating those objects would turn a true theorem into a false universal claim.

The dominated standard-Borel result in dominated.md supplies an ordinary-kernel endpoint, with an independently reviewed proof. The abstract endpoint below adds broader scope while preserving its different meaning; it does not declare unrestricted ordinary simulation completed.

## 1. Primary source and inspected objects

Lucien Le Cam (1964), *Sufficiency and Approximate Sufficiency*, Annals of Mathematical Statistics 35(4):1419–1455, DOI [10.1214/aoms/1177700372](https://doi.org/10.1214/aoms/1177700372). [Original scanned paper](https://scispace.com/pdf/sufficiency-and-approximate-sufficiency-nrxr6jc56j.pdf). Printed pp.1421–26, 1429–30 and 1449 were directly inspected; this is not a claim to have read every page.

| Source location | Relevant boundary |
|---|---|
| pp.1421–24 | Generated experiment L-spaces, their dual M-spaces, and positive norm-preserving transitions. |
| Definition 5, p.1425 | Generalized decision procedures are positive unital maps into M(E). |
| Theorem 3, pp.1429–30 | Arbitrary parameter set; finite-parameter decision comparisons characterize one simultaneous abstract transition with parameterwise error bounds. |
| Remark 1, p.1430 | Finite decision spaces suffice. |
| Remark 2, p.1430 | Nondominated experiments need not admit an ordinary kernel representation of the transition. |
| Proposition 19, p.1449 | Dominated source and locally compact sigma-compact Radon target permit an ordinary Markov-kernel realization. |

## 2. The maximal abstract object

An abstract experiment E consists of normalized positive states P_theta in an abstract L-space L(E): a Banach lattice whose norm is additive on positive elements. Its dual M(E) has an order unit 1. A transition

```math
T:L(E)\longrightarrow L(F)
```

is positive and linear, preserving the norm of every positive element. Equivalently its adjoint is positive and unital. Consequently it is contractive on signed elements. This is a state-independent positive map; it is not a different map for each parameter.

A finite-action generalized decision on E is a collection m_a in M(E), with m_a>=0 and sum_a m_a=1. Its risk at theta is

```math
R_\theta(m,L)=\sum_a L(\theta,a)\langle P_\theta,m_a\rangle.
```

Every ordinary measurable finite-action rule supplies such a collection, but the converse can fail on a nondominated sample-space representation. The word **generalized** is essential here.

Let Theta be any nonempty set. With the half-variation convention define

```math
\delta_{\rm abs}(E,F)
=\inf_T\sup_\theta\tfrac12\|TP_\theta-Q_\theta\|_{L(F)}.
```

The normalized consequence of the inspected comparison theorem is

```math
\boxed{
\delta_{\rm abs}(E,F)
=\min_T\sup_\theta\tfrac12\|TP_\theta-Q_\theta\|
=\sup_{\substack{\pi\ \mathrm{finitely\ supported}\cr A\ \mathrm{finite},\ 0\le L\le1}}
[B_E^{\rm gen}(\pi,L)-B_F^{\rm gen}(\pi,L)].
}
```

The original theorem also permits separate nonnegative error tolerances for each theta. Its finite-parameter criterion yields **one** transition satisfying all the tolerances simultaneously. Finite support does not restrict the ultimate parameter class, and no parameter measurability is needed for finite priors.

This statement uses the complete generalized finite-action menu. One task, one fixed prior, a restricted loss menu, or separate parameter-specific simulators is insufficient for the displayed universal conclusion.

### Attainment does not stop in a bidual

The source's Definition 3 on p.1422 requires norm preservation on positive states. Its Lemma 4, pp.1423–24, is the essential representation repair after dual compactness. A positive unital dual map Gamma:M(F)->M(E) initially has an adjoint taking source states into M(F)*. Let Pi project this larger L-space onto its L(F) band, and choose one normalized positive q0 in L(F). For P>=0 define

```math
a(P)=\|P\|-\|\Pi\Gamma^*P\|\ge0,
\qquad TP=\Pi\Gamma^*P+a(P)q_0.
```

This map extends positively and linearly, preserving mass. For target states Q in L(F), the band decomposition gives

```math
\|TP-Q\|\le\|\Pi\Gamma^*P-Q\|+a(P)
=\|\Gamma^*P-Q\|.
```

Theorem 3's compactness argument obtains simultaneous bounds on Gamma*, and this repair produces one genuine abstract transition **into L(F)** with no worse errors. The conclusion is neither a subprobability transition nor merely a bidual-valued limit. It still does not produce an ordinary measurable sample-space kernel without the additional realization bridge.

## 3. Norm conversion and why the constant is correct

The source's L-space norm is the full variation norm. For ordinary probability measures,

```math
\|R-Q\|_{\rm var}=2\sup_A|R(A)-Q(A)|=2\operatorname{TV}(R,Q).
```

Theorem 3 compares a norm tolerance eta_theta with a risk tolerance eta_theta times the state's loss supnorm. Thus its eta must not be identified directly with the TV epsilon used in dominated.md.

To obtain the displayed sharp [0,1] convention, center each loss at 1/2. Its supnorm is at most 1/2, and centering changes both experiments' risk by the same statewise constant. A full-norm tolerance 2 epsilon therefore gives risk tolerance epsilon.

Conversely take any finite-state comparison with nonnegative weights lambda_theta and bounded signed losses W_theta of supnorm M_theta. If D=sum_theta lambda_theta M_theta>0, set

```math
\pi_\theta=\lambda_\theta M_\theta/D,
\qquad L_\theta=(W_\theta/M_\theta+1)/2
```

on states with M_theta>0; zero-bound states contribute no risk. The weighted optimal risk difference for W is 2D times the Bayes-risk difference for L. Hence a [0,1] gap at most epsilon implies precisely the source criterion with full-norm tolerance 2 epsilon. D=0 is immediate. Finite-action optimal risks can be attained on a finite parameter restriction: its finite mixture dominates all relevant states, and the optimal action is a measurable finite comparison of their weighted densities. Applying the theorem at these tolerances establishes the normalized identity and attainment above, rather than assuming constants from notation. The source's general proof uses compact positive-unital dual maps and its transition construction (Lemma 4); compactness of the ordinary kernel space on an arbitrary sample representation is not being assumed.

The forward transfer bound can also be seen directly. A [0,1] generalized decision induces one order-interval element u_theta between 0 and 1. Since TP_theta-Q_theta has total mass zero, centering u_theta gives

```math
|\langle TP_\theta-Q_\theta,u_\theta\rangle|
\le\tfrac12\|TP_\theta-Q_\theta\|.
```

For losses in [0,M] the error bound is M epsilon. This is distribution-law preservation, not invertibility of realized raw samples; ancillary randomness can be discarded and regenerated.

## 4. Tight ordinary-kernel counterexample

This illustrative construction makes the boundary concrete. Work in the usual set-theoretic framework and choose a non-Borel H subset of [0,1]. Let Theta=X=[0,1], with Borel source observations P_theta=delta_theta. Let Y={0,1} and Q_theta=delta_{1_H(theta)}. Theta is an arbitrary index set; no measurable dependence on theta was required above.

The source's generated abstract L-space is the space of countably supported summable atomic masses. Sending each atom at theta to the atom at 1_H(theta) defines a positive norm-preserving abstract transition. Thus delta_abs=0.

An ordinary Borel kernel K would require the Borel function k(x)=K(x,{1}) to equal 1_H(x) everywhere for exact simulation. That is impossible. More sharply,

```math
\inf_{K\ \mathrm{Borel}}\sup_\theta
\operatorname{TV}(KP_\theta,Q_\theta)=\tfrac12.
```

The constant fair-coin kernel attains 1/2. If uniform error were strictly below 1/2, H={x:k(x)>1/2} would be Borel, a contradiction.

For every finitely supported prior, ordinary source observations nevertheless reveal each supported parameter, and a finite Borel rule can reproduce its target. Every finite-prior finite-action optimal Bayes gap is therefore nonpositive, and the supremum of these gaps is zero because a constant loss gives zero. Individual tasks can have strictly negative gaps when source observations distinguish parameters that share the same target bit. Thus even the ordinary finite-prior gap criterion cannot be substituted for the abstract theorem to obtain an unrestricted ordinary-kernel conclusion. This does not claim failure under additional measurable-parameter regularity: the example specifically uses the theorem's arbitrary-index-set scope. Published stronger regular-space counterexamples are separately tracked in PRIOR.md.

## 5. Ordinary realization and downstream dependency closure

Under common probability/sigma-finite source domination, Proposition 19's target representation covers all standard-Borel targets through Borel isomorphism: an uncountable standard-Borel space has a model [0,1]; a nonempty countable one has a discrete, locally compact sigma-compact model. Probability laws on these models are Radon. Approximate transitions can be realized by applying the proposition to their actual output family TP_theta, then retaining its discrepancy from Q_theta. This is a prior-work explanation of the ordinary result, not a replacement for dominated.md's explicit proof and review.

Without those realization premises, record an abstract simulator as **abstract**. It need not be a measurable program, a computable kernel, a finite-cost sampling procedure, or a physically implementable scientific transformation. Those are additional obligations. The unrestricted computable-feasibility endpoint has a separate halting impossibility certificate; no abstract existence theorem removes it.

The experiment families must already share a validated parameter correspondence. Neither this comparison theorem nor an abstract transition establishes that two sciences' variables measure the same mechanisms, align their interventions, or satisfy their declared observation laws. A real cross-domain bridge must still prove those premises. For ALLLEVEL-STAT-01, this theory classifies what a successful observation-law certificate means; it does not resolve the remaining biological observation fibers or the demonstrated indistinguishable pair.

## 11. Process integrity

Inspected the original theorem, its finite-action and nondominated remarks, definitions of transitions/decisions, and the ordinary realization proposition. Distinguished original full-variation constants from the project's TV convention and supplied the conversion. The counterexample and its exact 1/2 lower bound were hand-derived here; no historical novelty is attributed to this elementary construction. Independent review is required before publication of this synthesis. No canonical research files or GitHub state were changed by this contributor.

## 12. Inference robustness

The abstract all-experiments comparison endpoint is established classical mathematics. The ordinary dominated standard-Borel endpoint is also classical. The unconditional ordinary-kernel finite-prior equivalence is false, and unrestricted computable transfer checking is blocked separately. None of these outcomes provides a universal positive answer about empirical transfer, computational efficiency or scientific discovery.
