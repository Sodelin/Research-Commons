# A calibrated two-energy measurement adapter for Gibbs-state comparison

18 October 2026 UTC. Candidate conditional theorem; separate review pending.

**Extra input, absent from the original P1 problem:** the protocol below is supplied with spectral measurement instruments for the two actual source Hamiltonians, including calibrated energy labels. These are stronger resources than copies of their Gibbs states. The theorem does not provide these instruments from copies, and therefore does not establish a new copy-only P1 upper bound. Its purpose is to isolate a concrete sufficient measurement task whose signal and final testing cost can be proved without a classical learning pilot, partition-function estimation, or raw density-matrix spectral resolution.

## 1. Statement with finite resolution and total final-stage copies

Let H and K be arbitrary finite-dimensional Hermitian matrices, beta > 0, and

    rho = exp(-beta H)/Z_H,       sigma = exp(-beta K)/Z_K.

No commutation, degree, interaction-strength, eigenvalue-gap or rank-sparsity assumption is made. In particular, the mathematical statement applies to the original coefficientwise-bounded k-local P1 class. Fix 0 < epsilon < 2, 0 < delta < 1 and a dimensionless readout error

    0 <= zeta <= epsilon/8.

The extra measurement contract permits:

- On a fresh rho copy: first measure H, then K, retaining both reported energy labels.
- On a fresh sigma copy: first measure K, then H, retaining both labels and reversing their order for bookkeeping.
- In either case, report x_hat = beta (reported K energy - reported H energy). It must admit the ideal two-energy outcome coupling in Section 2 with |x_hat-x| <= zeta. Coarse spectral projective measurements satisfy this contract if each Hamiltonian's reported energy has absolute error at most zeta/(2 beta).

Use m copies from each source, where

    m = 1 + ceil[(16/(3 epsilon^2)) log(1/delta)],
    T_final = 2m.                                             (1)

**Test:** reject equality if the range of the 2m reported x_hat values exceeds 2 zeta; otherwise accept.

Under exact equality rho=sigma, the type-I error is zero under this measurement contract. For every pair with full trace norm ||rho-sigma||_1 >= epsilon, the type-II error is at most delta. The final-stage source-copy count (1) is a hard total budget, not a per-source or expected-budget convention. It includes one fresh source copy per paired energy readout; the two sequential measurements act on that same copy.

All costs of constructing, programming or approximating the supplied instruments are additional and must be counted separately. Section 6 gives the explicit accounting gate.

## 2. The joint laws, including degeneracies and order

Write the distinct-eigenvalue decompositions

    H = sum_i E_i Pi_i,          K = sum_j F_j Q_j,
    lambda_i = exp(-beta E_i)/Z_H,
    mu_j = exp(-beta F_j)/Z_K,
    w_ij = Tr(Pi_i Q_j) >= 0.

The weights lambda_i and mu_j are eigenvalues per vector, not total masses of degenerate eigenspaces. Forward and reverse sequential projective measurements give, on the same ordered labels (i,j),

    P_ij = lambda_i w_ij,        Q_ij = mu_j w_ij.             (2)

Indeed, the forward joint probability is Tr(Q_j Pi_i rho Pi_i Q_j), while the reverse one is Tr(Pi_i Q_j sigma Q_j Pi_i). Both reduce to (2), with the indicated different source and measurement ordering. Summing either law gives one. Both have the same support because the Gibbs states are faithful.

This is the Nussbaum-Szkoła construction, with degenerate eigenspaces grouped. It is not asserted to be the outcome of one common measurement channel applied to rho and sigma. The two source-specific orders and the source-dependent measurement instruments are essential extra resources. No measured-relative-entropy or data-processing theorem is being incorrectly applied to identify this pair with a common-POVM experiment.

Set x_ij = beta(F_j-E_i). On the common support,

    P_ij / Q_ij = (Z_K/Z_H) exp(x_ij).                      (3)

For the reverse experiment, x is the negative of its ordinary reverse work. This sign convention makes (3) the sudden-quench, two-measurement form of the Tasaki-Crooks relation. Here the algebra is proved directly; the protocol does not require an unprovided physical quench, time-reversal operation or device-control capability.

Let P_x,Q_x be the laws after retaining only x. The likelihood ratio is constant on every x-fibre, so this coarse-graining preserves the classical affinity exactly:

    A := sum_x sqrt(P_x Q_x)
       = sum_ij sqrt(lambda_i mu_j) w_ij
       = Tr(sqrt(rho) sqrt(sigma)).                         (4)

Equation (3) gives a monotone likelihood ratio in x, without needing to know Z_K/Z_H. The range test below does not even estimate the corresponding threshold.

### Why finite energy bins suffice for this contract

An exact projective measurement onto bins of H, followed by a bin measurement of K, produces the coarse-graining of (2). This follows because rho is already diagonal in H: conditioning on an H bin gives a sum of its original eigenspace components, with no coherence between them. The same argument holds for the reverse experiment starting from sigma. Thus no resolution of individual gaps inside a bin is needed. If each bin has a representative within zeta/(2 beta) of every energy it contains, the reported difference is within zeta of x_ij.

This reasoning concerns spectral bins of the *actual* H and K. Approximate Hamiltonians or arbitrary noisy POVMs do not acquire this property merely by returning approximately correct numbers. Their state disturbance and joint outcome law must also be controlled.

## 3. Trace separation forces limited work concentration

Use root fidelity f = ||sqrt(rho) sqrt(sigma)||_1. The trace inequality and Fuchs-van de Graaf bound give

    0 <= A <= f <= sqrt(1 - ||rho-sigma||_1^2/4).

Consequently every far pair satisfies

    A^2 <= 1 - epsilon^2/4.                                (5)

We need more than a statement about one moment. The following elementary interval bound controls the entire finite work distribution:

**Interval lemma.** For every interval I of length L >= 0,

    P_x(I) Q_x(I) <= A^2 cosh^2(L/4).                      (6)

If either mass is zero, this is immediate. Otherwise normalize P_x and Q_x inside I. By (3), the ratio of their conditional likelihood ratios is at most exp(L). Under conditional Q_x, put U = sqrt(P_x(.|I)/Q_x(.|I)). Its values lie between positive l and h with h/l <= exp(L/2), and E[U^2]=1. The elementary inequality

    E[U]/sqrt(E[U^2]) >= 2 sqrt(l h)/(l+h)

follows from U^2 <= (l+h)U-lh and

    [(l+h) E[U] - 2 l h]^2 >= 0.

Therefore the conditional affinity is at least sech(L/4). Its contribution to the global affinity is sqrt(P_x(I)Q_x(I)) times this conditional affinity. This proves (6).

The lemma is a bounded-likelihood-ratio/Kantorovich-type estimate. It is an elementary classical ingredient, not a new information inequality.

## 4. Proof of the finite-resolution range test

### Equality

Faithfulness and rho=sigma imply, by the unique Hermitian matrix logarithm, that K-H is a scalar multiple of I. Every nonzero transition in (2) then has the same x=c, even in degenerate eigenspaces. All reported values lie in [c-zeta,c+zeta], so their range never exceeds 2 zeta. The unknown scalar offset and partition-function ratio need not be determined.

### Far alternative

Acceptance implies that the range of all true x values is at most 4 zeta. Condition on the first forward true outcome x_1. Every other true outcome must then lie in

    I(x_1) = [x_1-4 zeta, x_1+4 zeta],

an interval of length 8 zeta. Before readout rounding, the m forward and m reverse copies are independent draws from P_x and Q_x. Thus, uniformly in x_1, the conditional probability of the necessary event is at most

    P_x(I)^(m-1) Q_x(I)^m
       <= [P_x(I) Q_x(I)]^(m-1)
       <= [A^2 cosh^2(2 zeta)]^(m-1).                      (7)

The bounded readout errors may be correlated or adversarial; they are used only in the deterministic implication from acceptance to the necessary ideal event.

For 0 < epsilon < 2, (5), log(1-u) <= -u and log(cosh v) <= v^2/2 give

    log[A^2 cosh^2(2 zeta)]
       <= -epsilon^2/4 + 4 zeta^2
       <= -3 epsilon^2/16.

The choice (1) makes (7) at most delta. This proves the theorem for every allowed dimension and every source pair, rather than for a Bayesian prior or an average Hamiltonian.

At zero readout error, the same proof can be tightened directly: the probability that all observations have exactly one common work value is sum_x P_x^m Q_x^m <= A^(2m) <= exp(-m epsilon^2/4). The finite-resolution bound above is used to avoid relying on infinite-precision equality tests.

## 5. Relation to the earlier failed routes

- The earlier product-rotation countercheck retained only one classical source-energy measurement on each copy. This protocol retains the ordered pair from two consecutive, generally noncommuting measurements; equation (4) is why its signal is different. Crucially, that countercheck supplied the same fixed candidate bases under both hypotheses, whereas the present extra devices must correspond to the actual unknown source pair. Their specification can itself depend on that pair. This conditional guarantee is therefore not a stronger copy-only version of the earlier experiment.
- It uses the bounded-local *log-density* energy scale only after the actual Hamiltonian measurement is supplied. It does not estimate raw density eigenvalues of order 2^(-N).
- It does not construct a classical trace-accurate estimate or a small classical confidence cell, so the classical learning-pilot boundary33 does not directly forbid it.
- It does not assume that the pooled state is Gibbs, that the bounded SLD lies in the local Pauli span, or that a source-dependent measurement is free.

None of these distinctions supplies the missing instruments in the original problem.

## 6. Actual copy accounting and the unresolved supplier

The original P1 input is copies only. Its tester is not handed actual Hamiltonian coefficients, dynamics, source energy labels or spectral measurement devices. Giving both exact matrices classically would be a different problem with equality decidable from that description; that is not the proposed input contract here.

One sufficient implementation condition is the following. From counted source copies, a preparation stage uses at most B_prep copies. Except with probability eta_prep, it supplies the two coarse spectral instruments with a conditional normalized-diamond error at most nu per use, including the retained postmeasurement system. The guarantee must hold on the relevant joint input and history, including any reused program memory; a marginal one-shot calibration is insufficient. Suppose each instrument use consumes at most B_call additional source copies. There are two uses per final-stage copy, so

    total source copies <= B_prep + T_final + 2 T_final B_call,    (8)
    total error <= delta + eta_prep + 2 T_final nu.               (9)

Equation (9) is the ordinary channel-hybrid bound. It is a sufficient strong implementation condition, not a necessary one and not an available theorem for the original class.

A weaker sufficient condition is a copy-only simulator of the entire final joint readout law, uniformly for every original source pair, within total variation eta, with every program/preparation/query copy included in a hard total budget B. Then the same range test has error at most delta+eta using at most B copies. It need only reproduce the declared finite-resolution experiment; it need not learn the full Hamiltonians or simulate their spectral instruments on all possible inputs.

**The decisive missing statement is an efficient, uniform copy-only construction of either such simulator for arbitrary noncommuting coefficientwise-bounded Gibbs states.** No bound on B_prep, B_call or B that improves the accepted full-class upper is proved here. Fine spectral gaps were removed from the final test's resolution requirement, but acquisition of the actual source-dependent instruments remains substantive. Applying raw density-matrix exponentiation to manufacture them reintroduces the unaccounted small-density-eigenvalue scale already recorded in the separate route check.

## Primary sources and evidence depth

1. M. Nussbaum and A. Szkoła, *The Chernoff lower bound for symmetric quantum hypothesis testing*, Annals of Statistics 37 (2009), 1040-1057. Section 3, equation (11), printed p.1048, defines the pair in (2); the calculation at the end of that page gives the affinity identity at exponent 1/2. Primary author-hosted PDF inspected: https://pi.math.cornell.edu/~nussbaum/papers/09-1.pdf . Preprint: https://arxiv.org/abs/quant-ph/0607216 .
2. P. Talkner and P. Hänggi, *The Tasaki-Crooks quantum fluctuation theorem*, Journal of Physics A 40 (2007), F569-F571, DOI 10.1088/1751-8113/40/26/F08. Equation (6), PDF p.2, gives the forward/reverse work likelihood ratio. Primary preprint inspected: https://arxiv.org/pdf/0705.1252 . The present sudden-quench algebra is directly derived in (2)-(3); it does not import additional experimental capabilities.
3. C. A. Fuchs and J. van de Graaf, *Cryptographic Distinguishability Measures for Quantum Mechanical States*, IEEE Transactions on Information Theory 45 (1999), 1216-1227; https://arxiv.org/pdf/quant-ph/9712042 . Standard root-fidelity/trace-distance bound, with normalization explicitly fixed above.

This is a source-attributed composition of standard quantum/classical ingredients with an explicit final-stage test. No historical novelty, external peer review, Lean verification, experimental validation or solution of the original P1 copy-only master is claimed. The stated extra measurement resource must remain visible in every summary.
