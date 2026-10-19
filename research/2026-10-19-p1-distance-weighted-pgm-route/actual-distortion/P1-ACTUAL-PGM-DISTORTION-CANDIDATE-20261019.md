# P1: actual PGM distortion, exact Gibbs identities, and two positive restricted-class tests

19 October 2026. Author: dot (OpenAI), working with Nolan.

Status: hand-proof candidate awaiting separate review. This note tests actual decoding distance, rather than recovery of an independently assigned acceptable label. Its positive bounds are applications of established Bayesian quantum-estimation and classical minimum-distance methods. No historical novelty, full interacting P1 rate improvement, efficient implementation, or Lean verification is claimed. A separate diagnostic script, if executed, will be reported separately.

## 1. Question and quantitative outcome

The original master concerns two unknown N-qubit Gibbs states at common known beta>0, arbitrary Pauli terms of weight at most k, every individual coefficient in [-1,1], no degree or incident-strength bound, equality versus full trace distance at least epsilon, and worst-case total original copies with arbitrary collective/adaptive measurements. That scope is unchanged.

For a finite known candidate family rho_i and arbitrary prior p, take n copies from one fixed unknown candidate. Write

    R_i=rho_i^(tensor n), S=sum_i p_i R_i,
    Lambda_j=p_j S^(-1/2) R_j S^(-1/2),
    w_ij=p_i Tr(R_i Lambda_j).

All Gibbs states are faithful, so S is invertible; zero prior weights can be dropped. The actual squared trace-distance risk is

    R_n(p)=sum_ij w_ij ||rho_i-rho_j||_1^2.             (1)

This is the ordinary PGM followed by output of its candidate state. We prove:

* Exact reversible Dirichlet/Bregman formulas for arbitrary noncommuting Gibbs candidates, with beta factors shown below.
* For the FULL one-body class, including unknown, noncommuting local orientations and arbitrary correlations in the prior,

    R_n(p) <= min{4, 6 cosh^2(sqrt(3) beta) N/n}.        (2)

* For any declared known common-basis commuting exponential family with m sufficient statistics, classical Yatracos theory gives

    R_n(p) <= min{4, C (m+2)/n}                        (3)

  with a universal C. The bound is uniform over priors and does not assume a Fisher eigenvalue lower bound, a high-temperature regime, or bounded interaction degree.

These are genuine quantitative positive tests of actual distortion. They do not prove the desired O(M/n) risk for the original interacting noncommuting family, where M=sum_(l=1)^k 3^l binom(N,l). Section 7 states the exact unsuccessful extension.

## 2. Reversible PGM and the Gibbs coefficient-mean identity

Let H_theta=sum_(a=1)^M theta_a P_a, psi(theta)=log Tr exp(-beta H_theta), and mu_a(theta)=Tr(rho_theta P_a). All coefficient vectors lie in the original cube. Put theta_i for candidate i and mu_i for its mean vector. Natural logarithms are used throughout.

The weight can be written

    w_ij=p_i p_j Tr(R_i S^(-1/2) R_j S^(-1/2)).         (4)

It is nonnegative, real, symmetric in i,j by cyclicity, and has both marginals p. Thus K_ij=w_ij/p_i is a reversible Markov kernel. Its positivity is stronger than mere reversibility: for real f_i, set B_f=sum_i p_i f_i R_i. Then

    sum_ij w_ij f_i f_j
      =Tr[(S^(-1/4) B_f S^(-1/4))^2]>=0.

Consequently K is a positive semidefinite self-adjoint contraction in L2(p). Define

    E_n(f,g)=1/2 sum_ij w_ij (f_i-f_j)(g_i-g_j)
            =<f,(I-K)g>_p.                            (5)

For quantum relative entropy D(rho||sigma)=Tr rho(log rho-log sigma), exact cancellation of partition functions gives

    D(rho_i||rho_j)
      =psi(theta_j)-psi(theta_i)
         +beta (theta_j-theta_i) dot mu_i,
    J_ij:=D(rho_i||rho_j)+D(rho_j||rho_i)
      =beta (theta_i-theta_j) dot (mu_j-mu_i).          (6)

No commutation assumption enters this identity: log rho_theta=-beta H_theta-psi(theta) I exactly. Since grad psi=-beta mu,

    sum_ij w_ij J_ij
      =-2 beta sum_a E_n(theta_a,mu_a)
      =2 sum_a E_n(theta_a,partial_a psi).              (7)

The average one-way relative entropy is half of (7). Individual cross terms E_n(theta_a,mu_a) need not have a specified sign, although their negative sum is nonnegative.

For completeness the noncommuting Hessian is

    partial_ab psi(theta)
      =beta^2 int_0^1 Re Tr[
          rho_theta^s (P_a-mu_a I)
          rho_theta^(1-s) (P_b-mu_b I)] ds.             (8)

It follows from differentiating the matrix exponential under the trace. The centered integral is the Kubo-Mori covariance. For delta=theta_i-theta_j,

    J_ij=int_0^1 delta^T Hess psi(theta_j+t delta)
                         delta dt.                    (9)

The coefficient cube is convex, so this path stays admitted. Equations (6)-(9) are exact Bregman identities, not a uniform curvature estimate.

Quantum Pinsker with full trace norm reads D(rho||sigma)>=||rho-sigma||_1^2/2. Applying it in both directions gives

    R_n(p)<=sum_ij w_ij J_ij.                          (10)

This provides a sufficient route but may overpay relative to actual trace distortion.

## 3. The known quadratic-label comparison, with a finite-dimensional proof

A useful supplier is Albarelli, Branford and Rubio, *Measurement incompatibility in Bayesian multiparameter quantum estimation*, arXiv:2511.16645v4 (3 August 2026), published in Quantum 10, 2192 (13 August 2026). Sections 3.2.1-3.2.2 derive the PGM quadratic-loss formula and its factor-two comparison with individually optimal scalar estimation. The versions and applicable passages were directly checked:

https://arxiv.org/html/2511.16645v4
https://doi.org/10.22331/q-2026-08-13-2192

Here is an explicit proof for arbitrary finite priors, sufficient for this note. For any real scalar label x_i, let

    b=sum_i p_i x_i^2, B=sum_i p_i x_i R_i.

The PGM's quadratic risk is exactly

    Q_PGM(x)=sum_ij w_ij(x_i-x_j)^2
            =2[b-Tr(B S^(-1/2) B S^(-1/2))].           (11)

The optimal scalar Bayes quadratic risk over all POVMs and real output estimators is

    Q_opt(x)=b-Tr(B L),  (SL+LS)/2=B.                 (12)

To see this directly, the first and second operator moments T,U of an arbitrary POVM and estimator obey U>=T^2. Its risk is at least b-2Tr(BT)+Tr(ST^2). Completing the square with the Hermitian solution L shows the minimum is (12); the spectral measurement of L attains it.

In a basis diagonalizing S, with eigenvalues s_u>0,

    Tr(BL)=sum_uv 2|B_uv|^2/(s_u+s_v),
    Tr(B S^(-1/2) B S^(-1/2))
          =sum_uv |B_uv|^2/sqrt(s_u s_v).

Since 2/(s_u+s_v)<=1/sqrt(s_u s_v),

    Q_PGM(x)<=2 Q_opt(x).                             (13)

The same ONE PGM is used for every scalar label. Consequently, summing (13) does not multiply the physical copy count by the number of labels. The different scalar measurements used to upper-bound Q_opt are comparison strategies, not a claimed jointly performed measurement.

For a candidate state's expectation x_i=Tr(rho_i O), with Hermitian ||O||<=1, measuring O separately on all n original copies and averaging is unbiased with mean-square error at most 1/n. Therefore

    sum_ij w_ij [Tr((rho_i-rho_j)O)]^2 <=2/n.          (14)

More precisely the right side can be 2 E_p Var_(rho_i)(O)/n. This applies even when different O's do not commute, because (13) is a separate comparison for each coordinate and the actual PGM is common.

## 4. Full one-body Gibbs test: proof of (2)

Take the entire one-body class

    H_h=sum_(b=1)^N h_b dot (X_b,Y_b,Z_b),
    h_b in [-1,1]^3.

Its state is a tensor product rho_h=tensor_b rho_(r_b), with

    rho_r=(I+r dot sigma)/2,
    r_b=-tanh(beta |h_b|) h_b/|h_b|,
    |r_b|<=R_beta:=tanh(sqrt(3) beta)<1.               (15)

Use the continuous value r_b=0 at h_b=0. Candidates need not share local eigenbases. Their prior may correlate all h_b arbitrarily. The physical state factorization follows from the one-body Hamiltonian, not from the prior.

Apply (14) to each of the 3N local Pauli observables. For the actual n-copy PGM of the whole candidate ensemble,

    sum_ij w_ij sum_b |r_(i,b)-r_(j,b)|^2<=6N/n.       (16)

There is no allocation of n copies to each of 3N observables. The physical instrument is one PGM on n copies; the scalar comparisons establish (16).

It remains to convert the complete Bloch-vector error into full-system trace error. For a single qubit define

    v(r)=atanh(|r|) r/|r|, v(0)=0.

The non-scalar part of log rho_r is v(r) dot sigma. Hence

    D(rho_r||rho_s)+D(rho_s||rho_r)
       =(r-s) dot (v(r)-v(s)).                        (17)

The Jacobian of v has radial eigenvalue 1/(1-|r|^2) and tangential eigenvalue atanh(|r|)/|r|. The latter is at most the former, by integrating 1/(1-t^2) over [0,|r|]. On the convex ball |r|<=R_beta, v is Lipschitz with

    L_beta=1/(1-R_beta^2)=cosh^2(sqrt(3) beta).

Thus (17)<=L_beta |r-s|^2. Quantum relative entropy is additive on tensor products. Combining this fact with Pinsker in both directions gives the pointwise bound

    ||tensor_b rho_(r_b)-tensor_b rho_(s_b)||_1^2
       <=L_beta sum_b |r_b-s_b|^2.                    (18)

Equations (16)-(18) prove (2) for every n>=1 and every finite prior. The trivial trace-distance bound supplies the cap 4. All quantities are normalized states, and the bound is for full trace norm, not half trace distance. Beta is fixed; this constant is not claimed beta-uniform.

An explicit comparison to the preceding sign-family diagnostic is useful. That family's local Bloch radii tend to zero and it lies in (15). Actual squared-distortion risk is O(N/n), uniformly over all priors on it, while the previous aggregate assigned-label certificate required N log N. The positive statement concerns actual output distance; it does not repair the previous assigned-label bound.

## 5. Finite minimax and two unknown sources: copy accounting

The prior-dependent PGM itself is not supplied an unknown input prior. For a finite candidate set, (2) holds for every prior. Standard finite minimax over the compact convex set of POVMs therefore supplies a single measurement with worst-case squared risk at most 6 L_beta N/n. It need not equal any single chosen-prior PGM.

For an ideal-known-matrix one-body equality test, fix 0<epsilon<=1 and take

    n>=ceil(4608 L_beta N/epsilon^2),
    a=epsilon/8,
    eta<=min{epsilon/16,1/(12n)}.

Build a known eta-net of this one-body family. Markov's inequality and (2), followed by finite minimax for the zero-one loss of exceeding radius a, give failure at most 1/12 for every net state. Replacing a true source by its net representative changes any n-copy event by at most n eta/2<=1/24. Thus each source is decoded within a+eta<=3epsilon/16 with failure at most 1/8.

Apply that decoder separately to the two unknown sources, using exactly n copies from each, total 2n. With probability at least 3/4 both estimates are good. Under equality their output distance is at most 3epsilon/8; under original full-trace separation at least epsilon it is at least 5epsilon/8. Threshold epsilon/2 separates them. This is a valid restricted one-body decision guarantee with every original copy paid and no actual-Hamiltonian oracle.

This ideal finite-matrix statement does not assert efficient construction or finite-precision performance without accounting for approximation. The rational robust-distance repair in the reviewed aggregate-decoder packet can be used if an effective implementation is desired. No new ideal-to-effective claim is needed for (1)-(2). In particular, no uncounted learning step is hidden in the minimax existence proof.

## 6. Classical known-basis comparison for arbitrary commuting interactions

Suppose a declared known common basis simultaneously diagonalizes a fixed list of m commuting Hamiltonian statistics. A basis observation has the classical exponential-family law

    p_theta(x)=exp[-beta theta dot T(x)-psi(theta)].

It is one complete classical draw per physical copy. For any two parameters, the region where p_theta(x)>=p_phi(x) is a halfspace in the m sufficient statistics, with intercept psi(phi)-psi(theta). Its Yatracos set class therefore has VC dimension at most m+1, independent of incident strength and of the smallest probability.

A directly checked primary statement is Ashtiani, Ben-David and Mehrabian, *Sample-Efficient Learning of Mixtures*, arXiv:1706.01596v3 (3 June 2018), Appendix A: Lemma 19 (PDF page 14), Theorem 22 and proof (PDF page 15), and Theorem 24 (PDF page 16). The exponential-family application is explicitly stated on PDF page 13. The v3 record reports a correction to an earlier version; the present argument uses v3:

https://arxiv.org/pdf/1706.01596v3

In the realizable case, their minimum-distance estimate has

    Pr[TV(p_hat,p)>alpha sqrt((v+log(1/delta))/n)]<=delta

for universal alpha, with v the Yatracos VC dimension. Integrating this tail (set delta=exp(-t)) gives

    E TV(p_hat,p)^2<=alpha^2(v+1)/n.                  (19)

One may cap it by one. Full L1 risk is four times (19). This is the classical Yatracos/minimum-distance method, not a new learning theorem here. The finite discrete class needed below poses no measurability or existence issue.

For a finite prior on commuting states the PGM is exactly posterior resampling: measure the common-basis n-copy data Y and independently draw J from the posterior distribution of I given Y. Conditional on Y, I and J are iid from that posterior. For any estimator p_hat(Y),

    E[||p_I-p_J||_1^2 | Y]
       <=2E[||p_I-p_hat||_1^2+||p_J-p_hat||_1^2 |Y]
       =4E[||p_I-p_hat||_1^2 |Y].                    (20)

The source-uniform bound (19) remains valid under every prior, including highly correlated or atomic priors. Applying it to (20) proves

    R_n(p)<=16 alpha^2(m+2)/n,                        (21)

as well as the trivial cap 4. This covers known-basis interacting classical Gibbs distributions. It does not supply a common-basis observation for arbitrary noncommuting Gibbs sources. Nor does it assert that pairwise commuting unknown candidates come with their basis for free in a different physical problem: the known candidate/basis restriction is explicit.

## 7. The exact full-class failure of the current extension

The quadratic-label comparison (14) is valid for ALL original Gibbs candidates, not only one-body states. Summing it for all M permitted Pauli means gives

    E_w ||mu_i-mu_j||_2^2<=2M/n.                      (22)

However, no N-independent full-trace-to-local-mean conversion has been established. The one-body proof uses two specific properties: tensor-product additivity of the physical state's relative entropy, and a fixed one-qubit Bloch-radius bound. Both are lost for general interacting states. Replacing them with a lower bound on the entire Gibbs spectrum can cost exp(O(beta M)); coefficientwise bounds do not prevent growing incident strength. A uniform inverse Fisher/Kubo-Mori estimate cannot be inserted without proof.

Even the direct Bregman calculation currently gives only a dominated bound. Positivity of K implies

    E_w (theta_(i,a)-theta_(j,a))^2
       =2 E_n(theta_a,theta_a)
       <=2 Var_p(theta_a)<=2.

Use Cauchy-Schwarz in the nonnegative pair law, then (22), in (6):

    E_w J_ij
      <=beta sqrt[E_w||theta_i-theta_j||_2^2
                    E_w||mu_i-mu_j||_2^2]
      <=2 beta M/sqrt(n).                             (23)

Together with (10) this is valid, but an O(M^2) fixed-accuracy sufficient budget is worse than accepted upper 13. There is no legitimate cancellation of the square root of n using only coefficient boundedness and (22).

The precise unsupplied estimate is a uniform bound, for every finite prior over the ORIGINAL full interacting class,

    E_w ||rho_i-rho_j||_1^2 <= C_(beta,k) M/n,          (24)

or a weaker error-probability estimate adequate for the binary decision task. The stronger sufficient Bregman statement E_w J_ij<=C_(beta,k) M/n is also unproved. The classical argument does not establish it: quantum candidates have no shared sample value on which all likelihood halfspaces can be evaluated, and sign(log rho-log sigma) is not generally the Helstrom sign(rho-sigma).

This is a precise failed extension, not an impossibility theorem. The reviewed counterexample 34 already warns against a uniform conversion based only on local linear-mean covariance; it does not refute (24), which concerns the full n-copy PGM law. The present derivation has not repeated that counterexample as a new result.

## 8. Attribution, scope, and evidence depth

The PGM quadratic-loss comparison is existing quantum-estimation theory; its exact finite form was rederived here and the latest available v4 source was checked. The commuting O(m/n) bound is the existing classical VC/Yatracos method, with an elementary posterior-resampling comparison. The application to the full one-body coefficientwise Gibbs family and the displayed constants are derived in this note. Historical novelty of that application has not been established and is not asserted.

The canonical full scope remains:
https://github.com/Sodelin/Research-Commons/blob/d15ec7f5d9a741ecbaa21d8f5f0cca49da4d0b81/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md

The preceding reviewed aggregate positive lemma and negative exact-label test are:
https://github.com/Sodelin/Research-Commons/blob/51d7b671acf36da945ae3435ba6065baaa305d0c/research/2026-10-19-p1-distance-weighted-pgm-route/aggregate-decoder/README.md

The accepted full-class upper is:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md

This note preserves the two-unknown-source master and its open exponent gap. The one-body and known-basis conclusions are explicit restricted comparisons, not a silent change of the original problem. The bounded source inspection is not an exhaustive prior-work audit. Any separate review and bounded numerical controls should be attached with their exact scope rather than described as external peer review or a formal proof.
