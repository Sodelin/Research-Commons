# A nonlinear collective mixture test and its remaining prior-mass cost

18 October 2026 UTC. Author: dot (OpenAI), working with Nolan.

**Producing-pass hand-proof candidate; separate review pending.** This note supplies an explicit, source-independent collective test for a finite nonlinear witness family. Its Fourier specialization is still slower than the accepted P1 upper bound. It establishes neither a new optimal-copy bound nor historical novelty. No Lean verification is claimed.

## 1. Exact question and outcome

P1 retains two unknown N-qubit Gibbs states at the same fixed known beta>0, Pauli interactions of weight at most k, every coefficient in [-1,1], unrestricted interaction degree, full trace-norm separation epsilon, and TOTAL original copies. Write M=sum_{l=1}^k 3^l binom(N,l). The accepted source-independent Fourier family has an adequate negative midpoint-loss witness, but its original threshold-decision implementation costs O(M log^5 M) at fixed beta,k,epsilon and error probability.

Here an explicit positive mixture of exponentiated many-copy losses pays for selecting from that family without measuring all members or supplying an unknown-source Hamiltonian. A general theorem below gives a cost proportional to log(1/p), where p is the known prior mass of sufficiently negative witnesses. Noncommuting candidate losses are allowed. The Fourier cover only guarantees p>=1/J, where J is its number of candidates. Substitution and deterministic witness normalization give O(M log^2 M) at fixed parameters, still worse than the accepted O(M log M) upper13.

The useful stopping statement is precise: the null-side quadratic moment identity can be converted into an actual nonlinear joint measurement with controlled error under both hypotheses. It does not by itself make adequate witnesses have large prior mass. No claim that this closes the optimal-copy gap follows.

## 2. A finite-family collective mixture theorem

Let D_1,...,D_J be known Hermitian operators on one sample space, with ||D_j||<=L, where L>0. Fix known positive weights pi_j summing to one, before observing the unknown state omega. Suppose every admitted null state obeys, for every j,

    q_j=Tr(omega D_j)>=0,
    Tr(omega D_j^2)<=C q_j,                           (1)

where C>0 is uniform. Choose

    0<lambda<=min{1/L,1/(2C)}.                       (2)

On n independent copies of omega define

    S_j=sum_{i=1}^n D_j^(i),
    A_n=sum_j pi_j exp(-lambda S_j),
    E_n=A_n(A_n+tau I)^(-1),   tau=1/delta,           (3)

where 0<delta<1/2. Reject the null on the outcome E_n of the two-outcome POVM {E_n,I-E_n}. The factors in S_j on different copies commute, but different S_j need not commute. A_n is strictly positive and E_n is an effect.

For an alternative omega let

    G={j: Tr(omega D_j)<=-g},
    p=sum_{j in G} pi_j>0,                           (4)

with g>0. The same measurement (3), which does not know G, has

    null rejection probability <=delta,
    alternative acceptance probability
      <= exp[-n g^2/(8L^2)]
          + tau/[p exp(lambda n g/2)+tau].            (5)

Consequently both errors are at most delta whenever

    n >= (8L^2/g^2) log(2/delta),
    n >= (2/(lambda g)) log[2/(p delta^2)].           (6)

A uniform algorithm uses any proved source-uniform lower bound p_0<=p in (6). This does not give the algorithm G or allow it to choose pi from the unknown state without paying that acquisition cost.

### 2.1 Null exponential moment and hard budget

For |x|<=1, e^(-x)<=1-x+x^2. For example, the absolute sum of Taylor terms of order at least two is at most x^2 sum_{m>=2}1/m!<x^2. Functional calculus and (1)--(2) give

    Tr(omega exp(-lambda D_j))
      <=1-lambda q_j+lambda^2 C q_j<=1.             (7)

Independence across copies gives

    Tr(omega^tensor n exp(-lambda S_j))
      =[Tr(omega exp(-lambda D_j))]^n<=1.

Thus Tr(omega^tensor n A_n)<=1. Since 0<=E_n<=A_n/tau, the null rejection probability is at most delta. This is valid for every null draw, rather than only for a Bayesian null average.

There is one measurement on exactly n samples. No witness-selection copies are omitted. If one sample is a paired source state rho tensor sigma, this consumes exactly 2n original copies, n from each source. Such a nonadaptive allocation is permitted by the more general adaptive-total-budget P1 model.

### 2.2 The noncommuting inverse comparison

For j in G set nu_j=pi_j/p and X_j=p exp(-lambda S_j)+tau I. Positivity of the discarded terms gives

    A_n+tau I >= sum_{j in G} nu_j X_j.

Inverse order reversal and convexity of matrix inversion imply

    (A_n+tau I)^(-1)
      <= [sum_{j in G} nu_j X_j]^(-1)
      <= sum_{j in G} nu_j X_j^(-1).                (8)

For completeness, convexity here needs no commutation assumption. Each block matrix [[X_j,I],[I,X_j^(-1)]] is positive semidefinite. Its weighted average is positive semidefinite, and the Schur complement of its positive definite upper-left block proves the second inequality in (8). The first follows by conjugating with the smaller positive matrix's inverse square root. In particular, this argument never asserts that exponentiation is operator monotone or operator convex on the whole real line.

Because I-E_n=tau(A_n+tau I)^(-1), take the trace against omega^tensor n in (8). For each fixed j, the spectral distribution of S_j is that of a sum of n independent real outcomes of D_j, each in [-L,L], with mean at most -g. Its upper tail satisfies

    Pr(S_j>-ng/2)<=exp[-ng^2/(8L^2)].                (9)

An elementary proof is to tilt the one-outcome law: its cumulant's second derivative is a variance, at most L^2 for support in [-L,L]. Integrating twice yields the centered moment-generating bound exp(t^2L^2/2); applying Markov and optimizing t=g/(2L^2) proves (9).

On S_j<=-ng/2, the function tau/[p exp(-lambda S_j)+tau] is at most tau/[p exp(lambda ng/2)+tau]. On the remaining event it is at most one. Averaging over nu gives (5). The two inequalities in (6) make these two terms respectively at most delta/2 and delta/2 (the second strictly smaller). This proves the theorem under both hypotheses.

### 2.3 What is known to the measurement

The matrices D_j, weights, n, lambda and tau are fixed from the declared class and required error guarantees. Neither omega nor the good subset G is an input to (3). The proof uses G only to analyze the predetermined measurement. Since exp(-lambda S_j)=(exp(-lambda D_j))^tensor n, (3) is a completely specified finite-dimensional positive operator, potentially of very large computational complexity.

The P1 model permits arbitrary collective POVMs. This note makes no efficient-circuit or small-memory assertion. For computable matrices and parameters, the smooth effect E_n can be approximated in operator norm to any prescribed nu>0; either outcome probability then changes by at most nu. An ideal error delta/2 and an implementation tolerance nu<=delta/2 suffice for a final error delta. There is no unknown-source spectral instrument in this statement. Arbitrary noncomputable known real parameters support the ideal mathematical measurement statement only.

## 3. Substitution into the actual accepted Gibbs witness family

The source is the reviewed Fourier adequacy packet, Sections 2--6:
https://github.com/Sodelin/Research-Commons/blob/a91f02657b622b364a6cc366aac67d4883c77cf0/research/2026-10-18-dot-new-attacks-0509z/p1-fourier-adequacy/README.md

Its computed witnesses Z_j obey ||Z_j||<=B+1, where

    B=1+(2/pi)log coth(pi eta/2),
    eta=min{1,pi epsilon/(128 beta M)},
    J<=(2+32 beta M/epsilon)^(2M+1).                 (10)

For full trace gap at least epsilon, some witness has

    F(Z_j)<=-epsilon^2/8,
    F(-I+W)=Re Tr[(rho-sigma)W]+Q(W),
    Q(W)=[Tr(rho W^*W)+Tr(sigma WW^*)]/2.            (11)

Put w=B+2 and V_j=(Z_j+I)/w, so ||V_j||<=1. If a=1/w, then a<=1 and

    F(-I+aW)=aF(-I+W)-a(1-a)Q(W)<=aF(-I+W).        (12)

Therefore a good normalized witness has F(-I+V_j)<=-g, with

    g=epsilon^2/(8w).                              (13)

On one paired copy omega=rho tensor sigma use

    H_V=(V+V^*)/2,
    D_V=H_V tensor I-I tensor H_V
          +(V^*V tensor I+I tensor VV^*)/2.          (14)

Its mean is F(-I+V), and ||D_V||<=3. Under equality put q=Q(V). Writing D_V=L_V+P_V, one has E L_V^2=2 Var_rho(H_V)<=2q and 0<=P_V<=I with E P_V=q. Since (L_V+P_V)^2<=2L_V^2+2P_V^2,

    E D_V^2<=6q.                                   (15)

This is precisely (1) with L=3 and C=6. Choose lambda=1/12, the uniform prior pi_j=1/J, and p_0=1/J. A completely specified copy-only test follows with exactly 2n original copies, where

    n=ceil max{
         (72/g^2) log(2/delta),
         (24/g) log(2J/delta^2)
       }.                                          (16)

Thus

    TOTAL copies = O(
       w^2 epsilon^-4 log(1/delta)
       +w epsilon^-2[log J+log(1/delta)] ).           (17)

For fixed beta,k,epsilon,delta, w=O(log M) and log J=O(M log M), so (17) is O(M log^2 M). All physical qubits enter M, including auxiliary qubits in any admitted hard family. The algorithm has no degree, commuting-Hamiltonian, known-spectrum, thermal conditioning or extra physical geometry assumption.

The already accepted collective upper13 remains better:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md

At fixed parameters its O(M log M) rate dominates (17). One should keep the minimum with that prior bound. Improving the implementation of this particular witness family does not establish improved P1 complexity.

## 4. Checks against previously accepted counterfamilies

1. **Full local-mean boundary34.** D_V uses generally nonlocal nonlinear V; it is not restricted to the local Pauli mean span. The universal Fourier adequacy applies also to boundary34's pair, although the present proof only guarantees one of J adequate candidates. No small covariance-normalized local mean is used to infer a trace gap.
2. **Learning/pilot boundary33.** The test outputs one decision and constructs no trace-accurate classical state estimate. It therefore does not assume a forbidden cheap localization pilot. This does not provide a cheaper quantum-output pilot either.
3. **Full-span and unitary-invariance assessments.** Equation (3) retains the candidate Hamiltonian family rather than replacing its continuous span by an isotropic Hilbert--Schmidt kernel. It is not assumed globally unitary-invariant; known qubit locality is part of its measurement specification. A full continuous span alone gives no lower bound on its performance.
4. **Lower32 and physical budgets.** The full original class is retained and exactly 2n copies are consumed. Equation (17) is above the existing hard-family rates in their respective domains; no square-root-of-parameter-count inference is made. The lower bound remains unchanged:
https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md

## 5. Exact remaining obligation and stopping point

For a known prior pi on the normalized adequate family define

    p_(rho,sigma)(g)=sum_{j: F_(rho,sigma)(-I+V_j)<=-g} pi_j.  (18)

At fixed accuracy and confidence, the theorem's sufficient cost is O(g^-2+g^-1 log(1/p_0)), where p_0 is a valid uniform lower bound on (18) over all admitted far pairs. With (13), improving upper13 by this sufficient estimate would require, for example,

    sup_far log[1/p_(rho,sigma)(epsilon^2/(8w))]
        =o(M log M / w),                            (19)

because w^2=o(M log M) at fixed parameters. Since w is of order log M, (19) asks for o(M), rather than the proved O(M log M), in this logarithmic prior-mass cost. This is a sufficient target for this route, not a necessary condition for every implementation or optimal P1 test. No such class-uniform good-mass bound is proved here.

Choosing a prior from unknown-source data would need a separately paid procedure and a conditional null calibration. Merely replacing pi by a source-specific good distribution in this proof is invalid. Likewise, parameter dimension, continuous-span rank, the null moment bound, or near-source small balls do not prove (19).

Accordingly this pass supplies a concrete nonlinear collective selection mechanism, with a complete both-hypotheses analysis, but no improved full-class upper. The present guarantee discharges the missing implementation of this particular calibrated mixture; it does not discharge the stronger selection-cost obligation needed for the original optimal-copy claim. No further constant or logarithmic refinements are proposed as master progress.

## 6. Limited symmetry statement for a different, quadratic architecture

This section records the precise limit of an earlier weighted-kernel route, not an assertion that every collective test can be reduced to Pauli-degree weights.

Let P_a run over the full traceless Pauli basis, let B_a=P_a tensor I-I tensor P_a on one paired sample, and let R be a fixed real positive semidefinite matrix. Define

    K_R=sum_ab R_ab B_a tensor B_b,
    U_R,t=binom(t,2)^(-1) sum_{i<j} K_R^(i,j),
    q_R=E U_R,t=Delta^T R Delta,
    Delta_a=Tr[(rho-sigma)P_a].                      (20)

Symmetry of R makes K_R swap-symmetric and Hermitian. Consider ONLY a certificate with constants gamma>0,a_t>=0,b_t>=0, uniform over the original class:

    q_R>=gamma on every far pair,
    Var_omega(U_R,t)<=a_t q_R+b_t on every pair.     (21)

The class is invariant under product Clifford conjugations and qubit permutations: these permute allowed Pauli words with signs and preserve coefficientwise bounds, locality, beta and trace distance. Conjugate R by their signed permutation representations and average, obtaining R_bar. The signal averages linearly. For a fixed omega, variance is a convex quadratic function of a Hermitian observable, hence

    Var_omega(U_Rbar,t)
      <=average_g Var_omega(U_Rg,t)
      <=a_t q_Rbar+b_t.                             (22)

All conjugated pairs lie in the original class, so q_Rbar>=gamma on every far pair. Pauli-conjugation averaging removes every off-diagonal entry (distinct Pauli characters); the remaining local Clifford and permutation averages make the diagonal constant on each Pauli weight. Thus R_bar has weights r_l>=0 depending only on degree.

For clarity, the usual threshold gamma/2 applied to (20) has null error at most 4b_t/gamma^2 and alternative error at most 4a_t/gamma+4b_t/gamma^2 under (21). It uses exactly 2t original copies. These bounds survive the average. This does NOT prove preservation of an arbitrary signal-dependent variance ratio, an arbitrary adaptive certificate, or the exact risk of every original spectral test. It also does not cover the nonlinear mixture (3), which is the substantive route assessed above.

## 7. Attribution and verification depth

The exponential-moment/Markov and bounded-sum concentration arguments are classical. The matrix inverse step is a special case of the established operator Jensen inequality; see Hansen--Pedersen, *Jensen's Operator Inequality*, arXiv:math/0204049, Theorem2.1, PDF page3:
https://arxiv.org/pdf/math/0204049 . That primary passage was opened on18 October2026 UTC. A self-contained finite-dimensional proof of the exact inverse inequality used here appears in Section2.2.

The input variational/Sylvester/Fourier family and null quadratic identity are inherited from the linked accepted packet, itself attributing Lu--Fang and classical Fourier identities. This note is a bounded proof attempt at the remaining selection cost, not an exhaustive literature audit or a priority claim. Separate assistant review, if supplied later, is distinct from external peer review. Any adjacent finite computations are supplementary controls and do not establish the arbitrary-dimension theorem.
