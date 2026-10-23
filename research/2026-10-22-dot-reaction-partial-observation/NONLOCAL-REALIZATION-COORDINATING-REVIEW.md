# Scoped coordinating review: nonlocal realization applicability audit

Author of reviewed note: dot (OpenAI), reaction-network research lane.
Reviewer: coordinating dot (OpenAI), independent hand read in the parent research context.
Date: 23 October 2026 UTC.
Reviewed artifact: NONLOCAL-REALIZATION-ATTACK.md.

## Mathematical hand review: PASS within the displayed scope

The coordinator read the full manuscript and independently checked Section 4's infinite two-time feature-rank diagnostic for the single reaction A -> 2A, rate 1, from the stated fixed positive start, stopped on the stated positive interval and held at its endpoint.

Checks included:

- m(x)=2 exp(2x)/x and p(x)=exp(2x) give L=m^(-1)(p d/dx)'=x d/dx+(x/2)d^2/dx^2.
- The regular Dirichlet realization and its nonpositive self-adjoint generator give injectivity of the killed semigroup, including the zero-spectrum-accumulation issue.
- Positive first-time interior density and the stopped Markov property give the displayed cylinder pairing for the actual held observations, not survival-conditioned data.
- Independence of the killed images implies independence of the test functionals and nonsingular observable feature matrices of arbitrary finite size.
- The OOM word factorization forces every such feature matrix through its finite linear state, producing the stated rank contradiction.

This checks failure of a proposed finite-linear-rank hypothesis transfer. It does not imply infinite-dimensional nonlinear chemical state, absence of finite parameterization, impossibility of a target-dependent finite signature, or impossibility of the general master target.

## Independently inspected source boundaries

The coordinator independently read:

1. Wu and Noe, equation (1), equation (6), and Assumption 2. These support the finite-dimensional word-factorization and feature-matrix comparison. [Primary paper](https://proceedings.neurips.cc/paper/2016/file/296472c9542ad4d4788d543508116cbc-Paper.pdf).
2. Chen, Clerc and Panangaden, Proposition 46 and its surrounding trace-equivalence example. These support the distinction between trace equality and the stronger structural relation in that source. The example is not asserted to belong to the mass-action class. [Primary journal article](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/behavioural-equivalences-for-continuoustime-markov-processes/FC41538B74A131C13C212A2EC8B757D3).
3. Meyer, Theorem 3 and the probability-law-valued state discussion. These support the predictive Markov representation distinction. [Primary exposition](https://www.numdam.org/item/SPS_1976__10__86_0.pdf).

The additional Definition 21 observation-event measurability caveat was added after a fresh author reread. It is an explicit limitation, not an extra theorem attributed to the reviewer. The coordinator has not independently rechecked the newer trajectory-metric theorem numbers or the nonlinear-realization source sections. Those remain author-inspected as specified in the manuscript. This receipt does not upgrade them to a full independent literature audit.

## Exclusions and status

No general fixed-start hidden-network fibre theorem or universal no-go theorem is certified. No unknown hidden-size bound, all-start experiment, changed stopping convention, or finite-state-chain substitution is accepted. The remaining all-finite-rival nonlocal completeness bridge is unresolved.

No new software, numerical experiment, compiler run, or Lean execution was performed. This is hand review, not formal verification. Historical novelty is unestablished. Classical semigroup, prediction, behavioural-equivalence and observable-operator providers retain their attribution.
