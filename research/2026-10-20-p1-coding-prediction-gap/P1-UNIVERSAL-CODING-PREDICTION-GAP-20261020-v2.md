# P1: the measurement gap between quantum block redundancy and prediction risk

Date: 20 October 2026 (UTC).

Attribution and status: prepared by dot for Nolan's P1 research project. This is an authored hand derivation and a bounded primary-source applicability assessment. The accompanying REVIEW.md records scoped hand/source PASS. This is a separate assistant-context review, not external peer review. No numerical execution, improved P1 rate, historical novelty, or formal verification is claimed.

## 1. Question and outcome

The original model consists of two unknown N-qubit Gibbs states at common known fixed inverse temperature beta, with all Pauli coefficients of weight at most k individually bounded by one. Interaction incidence and total strength per site are unrestricted. The decision is equality versus full trace-norm separation at least epsilon, with all copies charged and arbitrary collective measurements allowed. Write M = sum_{l=1}^k 3^l binom(N,l).

The accepted square-root/PGM comparison would make a uniform Bayes squared-Bures risk bound O_{beta,k}(M/n), over every finite prior on this class, useful for a two-source test using 2n copies. The current full-class upper bound remains O(M log M) at fixed accuracy and confidence.

This pass checked whether quantum universal coding or sequential prediction supplies that risk bound. It does not obtain one. The new applicability distinction is exact: a Bayesian block-redundancy increment equals the Umegaki prediction risk after measurement **minus** a nonnegative measurement-information loss. A small increment therefore is not, by itself, a risk upper bound. This is an application of standard entropy identities and data processing, not a new information-theory principle.

The prior local audit already rejected fixed-dimensional LAN and special qubit redundancy asymptotics as uniform growing-N suppliers. The present calculation addresses the additional operational conversion from an unmeasured block to a classical density-matrix estimate; it does not repeat those asymptotic objections.

## 2. Exact finite-prior identity

Let (p_theta, rho_theta) be any finite ensemble of density matrices on a finite-dimensional Hilbert space. No commutativity is assumed. Natural logarithms are used. Zero-prior terms are omitted. Define

    omega_n = sum_theta p_theta rho_theta^{tensor n},
    s = sum_theta p_theta S(rho_theta),
    chi_n = S(omega_n) - n s,
    delta_n = chi_{n+1} - chi_n.

Let C contain n training copies and B denote one formal future system, so

    omega_CB = sum_theta p_theta rho_theta^{tensor n} tensor rho_theta.

The future system is used to express the loss and joint state; no additional experimental copy is queried in the estimator. Let a POVM on C have classical outcome Y. Its posterior mean is

    mu_y = sum_theta p(theta | y) rho_theta.

For this fixed measurement, mu_y minimizes posterior Umegaki relative-entropy loss. Indeed, for any reported state sigma_y, the posterior average decomposes exactly as

    sum_theta p(theta | y) D(rho_theta || sigma_y)
      = sum_theta p(theta | y) D(rho_theta || mu_y)
        + D(mu_y || sigma_y).

The support convention is the usual one: a term is infinite when the reported state does not contain the source support. The posterior mean contains the supports of all positive-posterior states, so the displayed minimum is finite.

Consequently the optimized risk for this POVM is

    R_D(Y) = sum_y p_y S(mu_y) - s
           = S(B | Y) - s
           = chi_1 - I(B:Y).

On the other hand,

    delta_n = S(B | C) - s
            = chi_1 - I(B:C).

Subtracting gives, for each POVM,

    R_D(Y) = delta_n + I(B:C) - I(B:Y).                 (1)

Optimization over all collective POVMs on the n original copies gives

    R_D^*(p,n)
      = delta_n + Delta_meas(p,n),                    (2)

    Delta_meas(p,n)
      := I(B:C) - sup_{POVM C -> Y} I(B:Y) >= 0.       (3)

The final inequality is data processing. An infimum/supremum is sufficient; no assumption that a particular optimizer is attained is needed. The joint state also factors through the classical source label, so I(B:C) <= chi_1 and delta_n >= 0.

Equations (1)-(3) apply to every finite prior on the original Gibbs class, including faithful noncommuting states and arbitrary collective training measurements. They do not require a spectral lower bound. They establish a lower bound R_D^* >= delta_n, with the additional term specified exactly. They do not establish a lower bound for the P1 decision task.

For a known common eigenbasis, measuring C in that basis can preserve its correlations with B. The extra term then vanishes. This helps explain why a classical predictive-density argument cannot simply be copied into the noncommuting model.

## 3. The target is Bures risk, not relative entropy

Use root fidelity f(rho,sigma) = ||sqrt(rho)sqrt(sigma)||_1 and squared Bures distance b^2 = 2(1-f). The standard inequalities give

    b^2(rho,sigma) <= -2 log f(rho,sigma) <= D(rho||sigma).

Thus R_B^*(p,n) <= R_D^*(p,n). A bound on delta_n alone does not upper-bound the right-hand side of (2). The identity also does not disprove a direct Bures-risk theorem: relative entropy is a stronger loss and can carry a logarithmic penalty absent from Bures risk.

For this particular sufficient route, one would need an actual n-copy measurement satisfying, uniformly over every finite admitted prior,

    delta_n + Delta_meas(p,n) <= C_{beta,k} M/n.        (4)

Equation (4) is stronger than the unresolved Bures gate. A direct bound R_B^* <= C_{beta,k} M/n could succeed without (4). Neither bound is established here. An unmeasured quantum memory or a quantum recovery channel is not already a classical state-valued estimator; using such an output directly for P1 would require its own joint two-source decision analysis and copy accounting.

## 4. Primary coding and prediction suppliers

### Hayashi's universal block state

[Hayashi, arXiv:0806.1091v2, 18 July 2008](https://arxiv.org/html/0806.1091v2), Section II, equation (9) and the following relative-entropy inequality, gives a source-independent block state with

    D(rho^{tensor n} || sigma_U,n)
      <= ((d+2)(d-1)/2) log(n+1).

The displayed source convention uses base-two logarithms; the formula retains this form after converting both sides to nats. Its coefficient is ambient-dimensional: d=2^N in P1, not the number M of local Hamiltonian coefficients. Section III's sharper minimax statement, Theorem 1, is asymptotic at fixed d. These are useful coding results but do not supply a uniform M/n measured Bures-risk guarantee.

For completeness, averaging any block-code bound over the prior yields

    sum_theta p_theta D(rho_theta^{tensor n} || sigma_n)
      = chi_n + D(omega_n || sigma_n) >= chi_n.

An upper bound on this cumulative quantity does not by subtraction give a matching bound on its consecutive increments. In addition, a family of universal block states need not be a consistent Bayesian posterior sequence or specify a measurement-and-estimation procedure.

### Fixed-measurement Bayesian prediction

[Tanaka and Komaki, Physical Review A 71, 052323 (2005)](https://journals.aps.org/pra/abstract/10.1103/PhysRevA.71.052323) supplies the posterior-predictive principle under relative-entropy loss. The published abstract was inspected. [Tanaka, arXiv:quant-ph/0602072v1 (2006)](https://arxiv.org/html/quant-ph/0602072v1), Section II and the theorem in Section III, explicitly fixes an arbitrary measurement, allowing collective measurements, then optimizes the predictive state under an alpha-divergence. The alpha=0 estimator uses a normalized square of the posterior average of square roots. These statements do not optimize the measurement with a uniform growing-dimension risk rate. The alpha=0 affinity loss and root-fidelity Bures loss must retain their different conventions; no fidelity claim from the paper's final remark is used here.

## 5. Exact generic control: coding increments need not upper-bound Umegaki prediction risk after measurement

[Hayashi, Dasgupta and Warsi, arXiv:2609.10072v1, 9 September 2026](https://arxiv.org/html/2609.10072v1), Lemmas 10/13, Theorem 16 and equation (73), gives the optimum over all n-copy POVMs for the Haar pure-state prior. This is a preprint and is **not** an admitted finite-temperature Gibbs family.

Here omega_n is uniform on the symmetric subspace of dimension binom(n+d-1,d-1), so

    delta_n = log((n+d)/(n+1)).

The source's exact relative-entropy prediction risk is

    R_D^* = log(n+d) - ((n+1)/(n+d)) log(n+1).

Subtracting gives

    R_D^* - delta_n = ((d-1)/(n+d)) log(n+1).

At fixed d>1, the ratio R_D^*/delta_n therefore grows like log n. Yet the same measurement, reporting its ray, has average squared overlap (n+1)/(n+d). Since 2(1-sqrt(x)) <= 2(1-x), its Bures risk is at most 2(d-1)/(n+d). This checks the metric distinction; it is not a counterexample to the sought Bures rate.

## 6. P1 consequence and stopping point

The primary results checked here supply neither a uniform O_{beta,k}(M/n) classical-output Bures estimator nor a two-unknown-source decision procedure with a smaller fully paid budget. The existing square-root/PGM comparison remains available if the risk gate is eventually proved; using n copies of each input would cost 2n original copies.

The precise missing step is a measurement-level Bures-risk bound for every finite prior on the interacting coefficientwise-bounded Gibbs class. A cumulative coding redundancy bound alone, a fixed-measurement posterior formula, or a quantum-memory predictor does not establish it. The exact measurement loss in (2) explains one invalid conversion, while leaving a direct Bures or decision-specific route open.

This is a bounded applicability assessment, not an exhaustive literature search or a new obstruction to all coding-based methods. No P1 upper or lower bound changes. No experiment, symbolic checker, or numerical benchmark was run in this pass.

## 7. Project sources and prior coverage

- [Current scope, immutable 69b14f90](https://github.com/Sodelin/Research-Commons/blob/69b14f90b74847a691fdda39347a5ff5c90626cf/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md).
- [Current priority, immutable cac3fd17](https://github.com/Sodelin/Research-Commons/blob/cac3fd176a13f2d9e3ab83c4595e4cf3b9979604/research/2026-10-19-dot-priority-review-2012z/CHECKPOINT.md).
- [Accepted square-root/PGM comparison and its still-unproved M/n gate](https://github.com/Sodelin/Research-Commons/blob/2a2ee35f0660daaa6c41c78ad8c1f6e636ce935f/research/2026-10-19-p1-distance-weighted-pgm-route/actual-distortion/square-root-comparison/README.md).
- [Accepted full-class upper 13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md).

Saved prior audits were checked before this pass: the pointwise Kubo-Mori status record (including its fixed-dimension information-increment source audit), modular-work acquisition assessment, and square-root/PGM comparison. Directed public searches covered quantum universal coding, redundancy, predictive Bures risk and quantum exponential-family redundancy. Unrelated keyword matches were not treated as suppliers. Primary-source depth is specified above; no claim is made that every cited paper was fully independently audited.

Revision record: this successor preserves the mathematical content of the original authored note, SHA256 12cabad2d80c55369914431d93c7089d5b983ff732cc4ee5526bbc4f53ef7a94. The review terminology correction uses “Umegaki prediction risk after measurement”; it does not use “measured relative entropy,” which denotes a different divergence. The review-status sentence is updated accordingly.
