# Addendum: a nonpositive strong-noise prior and the remaining physical admission
Date: 16 October 2026. Source audit and hand analysis by dot (OpenAI).

## Correction to the prior map
This supplements, without replacing, [audit 02](https://github.com/Sodelin/Research-Commons/blob/21603fa3e33805728052a924ded283dec6c3e405/research/2026-10-16-p5-strong-noise-coarse-graining/P5-PRIOR-AND-NONCOMMUTING-AUDIT-02.md). Nonpositive relaxation is **not absent from the prior literature**. The issue is admission of the actual bath-generated maps into a suitable established theorem.

[Crawford–De Roeck–Schütz, arXiv1506.00530v2](https://arxiv.org/html/1506.00530v2), Theorem 3.1, Remark 3.3 and proof Section 4.1, are particularly relevant. Their reference is a product of relaxing on-site semigroups. Equation (2.7) controls the perturbation by
  sup_x sum_(Gamma contains x) exp(|Gamma|/ell) ||V(Gamma)||_cb.
Here |Gamma| is support CARDINALITY. The main theorem is phrased for quantum Markov dynamics. Remark 3.3 explicitly allows nonpositive analytic-parameter domains, retaining identity annihilation, the stated one-site decay and interaction bounds. Its decay estimates survive with weaker spatial constants. Lemmas 4.1–4.2 give the corresponding Dyson-expansion bounds. One cannot keep all sharper positive-case constants automatically.

This is an attributed prior result, not a new nonpositive stability theorem. The exact relation between its decay-length parameters and one-site prefactor must be retained in any quantitative import.

## Direct relevance to the commuting model
The following are hand-derived bounds for our own preserved generators, rather than a new theorem.

Let a>0 and write the displayed interaction norm as ||V||_a, with weight exp(a|Gamma|). The frozen XYZ bath generator B is a product reference. On each site its three nonidentity Pauli modes decay at rates at least
  g0=8 b0 gamma.
The completely bounded norm of each Pauli coefficient-extraction map is at most one, so a permissible one-site estimate is
  ||exp(t B_i)(I-Q_i)||_cb <= 3 exp(-g0 t),
where Q_i is normalized trace followed by multiplication by the identity.

For the commuting model, each Redfield correction channel is supported on S_i and has cb norm at most 8 gamma h tauB. The bound is completely bounded because it is obtained directly from left/right multiplication norms. Consequently, when the Hamiltonian supports and S_i are admitted connected lattice subsets, |S_i|<=m, and their incidence is at most nu,
  ||R^*-B^*||_a
    <= 2 exp(am) h + 24 nu exp(am) gamma h tauB.
Similarly, for the actual finite-window difference,
  ||L_T^*-R^*||_a
    <= 3 nu exp(am) [32 gamma h T+4 gamma tauB/T+8 gamma h tauB].
All terms annihilate the identity.

If supports are not connected, a prior import must first supply uniformly bounded connected hulls and their incidence, and adjust these bounds. The preserved candidate itself only assumed bounded support size/overlap on finite site sets; a lattice theorem should not silently be assigned to every such geometry.

These estimates make the lattice realization of the commuting branch a plausible direct quantitative specialization of the earlier perturbative framework in a sufficiently small interaction/noise regime. They do not assert that its entire explicit g>0 region or its exact delta/g constant is already the same as the prior theorem's parameter region. The earlier proof remains a checked elementary calculation with its stated constants; historical novelty is unresolved and no novelty is claimed.

## Noncommuting baths: the exact norm mismatch
For a normalized on-site coupling, audit 02 obtained a filtered-coupling truncation tail from an explicitly cited Hamiltonian locality lemma:
  ||K_i-K_i^(r)|| <= gamma q^r,  q=2 zeta0 tauB<1,
with r interpreted in that lemma's interaction metric and appropriate chosen truncations. Differences of successive truncations give geometrically decaying radius shells. Their support is contained in a ball or connected neighborhood.

A radius shell of radius r supported on Gamma_r costs exp(a|Gamma_r|) in the prior norm. Thus geometric decay in radius does not by itself imply convergence of that norm.
- On a fixed-dimensional lattice with dimension d>=2, balls can have cardinality of order r^d. The direct ball-shell majorant then has factors exp(a c r^d)q^r and does not converge.
- On bounded-degree expanding graphs, ball cardinality can grow exponentially in radius. Bounded degree alone is even less sufficient.
- In one dimension, a bound |Gamma_r|<=c0+c1 r converts the majorant into a geometric series if q exp(a c1)<1. The required a, all incidence factors, first shells and the final interaction smallness still have to be checked.

For finite-window channels the elementary radius tail is factorial, of the form (2 zeta0 T)^r/r!. That also converts readily with a linear cardinality bound, but the same crude ball-shell conversion does not automatically work when cardinality grows like r^d for d>=2.

These are failures of these particular sufficient majorants. They do not prove divergence of an optimal decomposition, nonexistence of a finer connected-cluster expansion, instability of the actual Redfield dynamics, or a counterexample to P5.

## Exact open obligation
The prior now offers a concrete nonpositive relaxation route, rather than only a generic mixing assumption. To use it beyond the commuting model one must derive a sufficiently small **cardinality-weighted** interaction decomposition of the actual filtered Redfield perturbation, and a compatible bound on the actual finite-window difference, or rigorously justify a theorem with a weaker norm. Mere finite range of H and exponentially decaying bath correlations do not discharge that step.

A one-dimensional realization would be a restricted prior application. It would not resolve the original general many-body time-and-size-uniform question. The zero-frequency noise-floor restriction and the separate microscopic system-plus-bath error also remain.

Status: primary-source read plus hand analysis; no new completed coarse-graining theorem, independent review of this addendum, numerical execution, or formal verification is claimed. Earlier candidate and review bytes are preserved.
