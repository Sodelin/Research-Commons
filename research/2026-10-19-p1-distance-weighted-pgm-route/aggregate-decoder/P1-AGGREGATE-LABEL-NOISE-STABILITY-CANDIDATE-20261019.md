# P1: a logarithmic cost in the aggregate-label sufficient functional

19 October 2026. Author: dot (OpenAI), working with Nolan.

Status: new hand-proof candidate, awaiting separate review. This tests the specific sufficient functional in the overlapping-loss aggregate decoder. It is not a lower bound for P1 testing, and it is not a lower bound for arbitrary trace learning. The example is an exactly admitted, known-basis one-body Gibbs family that can itself be trace-learned using O(N) copies at fixed accuracy. Classical noise stability is the mechanism; historical novelty is not claimed. No code execution or Lean verification is claimed.

## 1. Question and precise answer

The aggregate decoder assigns a latent acceptable output to the fixed source before seeing its samples, and then upper-bounds the original loss by the probability of failing to identify that assigned output exactly. These tasks can differ. A measurement may return a different acceptable output without identifying the independent latent assignment.

Let C={tau_i} be any finite eta-net of the original N-qubit Gibbs class, and let L be any zero-one loss with at least one acceptable output per input. Suppose every acceptable pair obeys

    L_ij=0 implies ||tau_i-tau_j||_1<=R.

Let B_n^*(C,L) be the exact aggregate-fidelity functional in the companion decoder note, using root fidelity, n fixed-source copies, a supremum over priors, and an infimum over all stochastic assignments supported on acceptable outputs. Put

    c_0=log 2-h(1/8)>0,
    h(x)=-x log x-(1-x) log(1-x).

For fixed beta>0, every sufficiently large N admits the one-body family below. If

    eta+R<=1/128,

then the following candidate bound holds for every integer n>=1:

    B_n^*(C,L) >= max{0, 1-n eta/2
                  -exp[-(c_0 N/4)(1-1/(4N))^n]}.       (1)

In particular, with n eta/2<=1/24, the desired certificate B_n^*<=1/12 requires, whenever the numerator is positive,

    n >= log[c_0 N/(4 log(8/7))]
             /[-log(1-1/(4N))]
       = 4N log N+O(N).                               (2)

Thus this sufficient functional cannot give an O(N) bound on the full one-body class, whose coefficient count is M=3N. The family remains a legal subset for higher k, but (2) is only Omega(N log N), not Omega(M log M) when k>=2. It does not obstruct an O(M) aggregate bound in those higher-locality regimes. It does not establish any P1 minimax rate.

For the corrected decoder note, take 0<epsilon<=1/32,

    a=epsilon/16, eta<=min{epsilon/16,1/(12n)},
    nu=epsilon/64.

The exact loss has R=a; the rational robust loss has R=a+3nu. Both satisfy eta+R<=11epsilon/64<=11/2048<1/128. Therefore (1)-(2) apply to either relation, including an arbitrary fine net that does not contain the test family's states exactly.

## 2. Exact normalized physical family

Take a uniform sign vector S=(S_1,...,S_N) in {-1,+1}^N once, before all copies. Set

    r_N=1/(2 sqrt(N)),
    h_N=atanh(r_N)/beta,
    H_S=-h_N sum_(b=1)^N S_b Z_b,
    rho_S=exp(-beta H_S)/Tr exp(-beta H_S)
         =tensor_(b=1)^N (I+r_N S_b Z_b)/2.             (3)

For N large enough that r_N<=tanh(beta), every coefficient has magnitude at most one. There are exactly N physical spins and no auxiliaries. All states have full rank. The locality is one, hence is allowed in every at-most-k class with k>=1. The normalization in (3) is exact, and beta is common and fixed.

One computational-basis observation from rho_S returns N independent signs X_b with mean r_N S_b. Conditional on S, n original copies give n independent such rows. Since all rho_S commute in this same known basis, any collective n-copy POVM, including an adaptive procedure using at most n copies, is a stochastic postprocessing of the complete basis data Y. Padding unused copies proves the hard-budget statement. There is no independent redraw of S between copies.

## 3. Any small-radius assigned output has exponentially small prior mass

For two source signs s,t with Hamming distance d, their root fidelity is exactly

    f(rho_s,rho_t)=(1-r_N^2)^(d/2).                    (4)

For classical probabilities, full L1 distance is at least 2(1-root fidelity), by summing |p-q|>=(sqrt(p)-sqrt(q))^2. Thus if ||rho_s-rho_t||_1<=2b with b<=1/2, then

    d <= 2[-log(1-b)]/[-log(1-r_N^2)]
      <= 4b/r_N^2.                                   (5)

Choose for every s a net representative i(s) with ||rho_s-tau_i(s)||_1<=eta. No injectivity is assumed. This induces the legitimate prior

    p_i=2^(-N) |{s:i(s)=i}|                           (6)

on fixed candidate indices. For an arbitrary allowed assignment q(j|i), write q_j(s)=q(j|i(s)). If q_j(s)>0, then ||rho_s-tau_j||_1<=eta+R. Any two signs in the support of q_j therefore have source distance at most 2(eta+R). Fix one such sign if the support is nonempty. Equations (5) and r_N^2=1/(4N) put the whole support inside its Hamming ball of radius at most N/8 when eta+R<=1/128.

The usual binomial entropy bound gives

    Pr(q_j(S)>0) <= 2^(-N) sum_(d=0)^floor(N/8) binom(N,d)
                 <= exp[-c_0 N].                     (7)

In particular, w_j=E q_j(S)<=exp[-c_0 N]. This holds for fractional/randomized assignments as well as deterministic partitions, and for arbitrary output density matrices tau_j. Overlapping acceptable sets have not been replaced by an equivalence relation.

## 4. Exact posterior channel and its remaining noise

For one coordinate, let P_+ and P_- be the laws of its n observations conditional on S_b=+1 and -1. Under the uniform prior define

    m(Y_b)=E(S_b|Y_b)=(P_+(Y_b)-P_-(Y_b))
                         /(P_+(Y_b)+P_-(Y_b)),
    gamma=E[m(Y_b)^2] in [0,1).                       (8)

Let T map a function of S_b to its conditional expectation given Y_b. Its adjoint maps back by conditional expectation given S_b. Sign symmetry implies T* T fixes constants and maps the sign function to gamma times itself. Thus it is precisely the binary noise operator of correlation gamma. Independence across coordinates makes the full T* T the N-coordinate Boolean noise operator T_gamma. This is an exact identity for the observation experiment, not an approximation by independent source parameters after conditioning.

The remaining noise has an explicit lower bound:

    1-gamma=2 sum_y P_+(y)P_-(y)/(P_+(y)+P_-(y))
           >= [sum_y sqrt(P_+(y)P_-(y))]^2
           =(1-r_N^2)^n.                             (9)

For the inequality, apply Cauchy-Schwarz to the factors sqrt(2P_+P_-/(P_++P_-)) and sqrt((P_++P_-)/2). The second squared norm is one. The last equality uses the exact product law for n weak Bernoulli observations.

## 5. Bound every assigned-label decoder, uniformly over q

Draw J conditionally on S according to q_j(S), independently of measurement randomness and observations given S. Its posterior probabilities given the full basis data are v_j(Y)=E[q_j(S)|Y]. Even the optimal decoder of J has success at most

    E max_j v_j(Y)
       <= sqrt(sum_j E v_j(Y)^2).                     (10)

The posterior-channel identity and the Boolean hypercontractive inequality yield

    E v_j(Y)^2
       =<q_j,T_gamma q_j>
       =||T_sqrt(gamma) q_j||_2^2
       <=||q_j||_(1+gamma)^2
       <=w_j^(2/(1+gamma)).                           (11)

Here all norms and inner products use the uniform sign prior. The last step uses 0<=q_j<=1. Since sum_j w_j=1 and (7) bounds every w_j,

    sum_j E v_j^2
       <= [exp(-c_0 N)]^((1-gamma)/(1+gamma)).

Combining (9)-(11), and using 2(1+gamma)<=4, proves the uniform bound

    Pr(correct assigned output)
       <=exp[-c_0 N(1-gamma)/(2(1+gamma))]
       <=exp[-(c_0 N/4)(1-r_N^2)^n] =: U_n.           (12)

The assignment may depend on n, the full net and its induced prior. Equation (12) covers all such assignments at once. The conclusion is about identifying the preassigned J exactly; it does not say every acceptable-output decoder has this small success probability.

The only non-elementary supplier in (11) is classical Boolean hypercontractivity. A directly inspected primary research source is Montanaro and Osborne, *Quantum boolean functions*, author PDF dated 12 April 2010, Section 8, Theorem 46, equations (90)-(91), PDF page 25:
https://people.maths.bris.ac.uk/~csxam/papers/qboolean_toc.pdf
Its p-to-q statement, restricted to diagonal matrices with p=1+gamma and q=2, gives exactly ||T_sqrt(gamma) f||_2<=||f||_(1+gamma). The noise convention is in Definition 43 and equations (85)-(86). This uses a classical special case of their theorem; it makes no new quantum-hypercontractivity claim. Only these statements and the relevant conventions were checked, not the entire paper.

## 6. Transfer back to any fine net and the functional

For fixed s, replace rho_s^tensor n by tau_i(s)^tensor n. The full trace difference is at most n eta; any measurement event changes by at most n eta/2. This remains true after averaging over s and the conditional assigned label J. The state need not commute after the replacement.

Consequently, for the prior (6) and every allowed q, the best possible success in the exact aggregate-label task on the net experiment is at most U_n+n eta/2. In particular its PGM error is at least 1-U_n-n eta/2.

For A_j=sum_i p_i q(j|i) tau_i^tensor n, the companion note's verified subnormalized PGM inequality says that this same PGM error is at most sum_(j!=l) f(A_j,A_l). Therefore

    min{1,sum_(j!=l) f(A_j,A_l)}
       >= max{0,1-U_n-n eta/2}.

Taking the infimum over q and then the supremum over priors proves (1). This order is essential: a lower bound on one arbitrarily chosen q would not suffice. The construction handles every q, including random assignments and arbitrarily many outputs.

If n eta/2<=1/24 and B_n^*<=1/12, (1) forces U_n>=7/8. Taking logarithms gives (2). For n=C N with any fixed C, U_n tends to zero exponentially in N; the sufficient functional stays at least 23/24-o(1). For n=o(N log N) the same conclusion holds. This is not obtained by bounding a few copy moments.

## 7. The actual family is learnable with O(N) copies

For clarity, there is no corresponding N log N learning lower bound here. Measure every copy in the known Z basis, and estimate each S_b by its sample-majority sign. Hoeffding's inequality gives the uniform per-coordinate error bound

    Pr(hat S_b!=S_b)<=exp(-n r_N^2/2)=exp[-n/(8N)].

Let H be the total number of incorrect estimated signs. For fixed desired full trace accuracy d_0>0, the elementary upper fidelity bound gives

    ||rho_S-rho_hatS||_1
       <=2 sqrt(1-(1-r_N^2)^H)
       <=2 r_N sqrt(H)=sqrt(H/N).                     (13)

The first inequality follows by Cauchy-Schwarz applied to (sqrt(p)-sqrt(q))(sqrt(p)+sqrt(q)). Markov's inequality therefore yields

    Pr(||rho_S-rho_hatS||_1>d_0)
       <=exp[-n/(8N)]/d_0^2.

Taking n>=8N log(12/d_0^2) makes this at most 1/12, for every fixed source S. The output rho_hatS is an admitted state of the same family. Every physical sample is counted, no side information about S is supplied, and no arbitrary quantum-state estimation oracle is assumed. This is only a learner for the displayed known-basis sign family, not a full Gibbs-class upper bound.

Thus the latent exact-label reduction can lose a logarithm even on this simple experiment. The correct decoder may output any one of many nearby candidates depending on its data, whereas the sufficient functional asks it to reproduce an independently assigned output.

## 8. Consequence for the current research direction

The overlapping-loss aggregate theorem remains mathematically valid. This calculation tests whether its sufficient condition is sharp enough, and identifies a concrete geometric/statistical obstruction for the one-body regime. It does not refute a useful O(M) aggregate bound for fixed k>=2, where M grows faster than N, nor does it imply optimality of upper 13. A proof of such a bound for the full higher-locality class is still absent.

The parameterized argument uses the original fixed-beta coefficientwise class and exact normalization. It changes neither the P1 decision promise nor its permitted measurements. It supplies no new full-class testing upper or lower bound. Any broader loss-aware theorem should control the actual acceptable-output error without charging exact agreement with a latent independently assigned label. A further minimax identity by itself would not establish that missing quantitative theorem.
