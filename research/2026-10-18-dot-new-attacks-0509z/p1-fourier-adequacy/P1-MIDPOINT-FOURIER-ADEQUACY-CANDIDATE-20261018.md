# A source-parameterized adequate variational family without inverse-state conditioning

18 October 2026 UTC. Author: dot (OpenAI), working with Nolan.

**Producing-pass hand-proof candidate, awaiting separate review.** This is an adequacy and acquisition-cost assessment for the original P1 class. Its elementary cover-based testing bound is worse than the accepted upper; it is not an improvement of P1, a novelty claim, or a formal Lean proof.

## 1. Precise outcome

Let beta>0, 1<=k<=N, and let P_1,...,P_M be all nonidentity N-qubit Paulis of weight at most k, where M=sum_{j=1}^k 3^j binom(N,j). The two unknown Hamiltonians H=sum h_a P_a and K=sum k_a P_a have all coefficients in [-1,1]. Their Gibbs states are rho and sigma at the same beta. There is no degree or per-site interaction bound.

For each 0<epsilon<=1, this note constructs an explicitly source-independent finite family of known operators Z, specified by two candidate coefficient vectors and one scalar. It has size at most

    L <= (2+32 beta M/epsilon)^(2M+1).                  (1)

Define the midpoint variational loss

    F_(rho,sigma)(Z) = 1+2 Re Tr(rho Z)
        +(1/2)Tr(rho Z^* Z)+(1/2)Tr(sigma Z Z^*).      (2)

Every operator in the family has norm at most

    B = 1+(2/pi) log coth(pi eta/2),
    eta = min{1, pi epsilon/(128 beta M)}.             (3)

For rho=sigma, F(Z)>=0 for EVERY operator Z. For full trace norm ||rho-sigma||_1>=epsilon, at least one member of the finite family obeys

    F(Z) <= -3 epsilon^2/16.                          (4)

Thus a uniformly adequate, generally nonlocal nonlinear witness family exists with logarithmic operator norm and a description using 2M+1 real parameters. No inverse minimum eigenvalue enters (1)--(4). The construction does not assert that the optimizer is a k-local operator, that its coefficients can be learned cheaply, or that a variational optimizer can find it with few copies.

## 2. Midpoint loss and weighted approximation

The objective is the t=1/2 numerator in Lu--Fang, *Estimating quantum relative entropies on quantum computers*, arXiv:2501.07292v2, Lemma2/Eq.(3) and Lemma4/Eq.(37):
https://arxiv.org/html/2501.07292v2 . Its standard f_t-divergence equals 2 times the infimum of (2). Only this midpoint node is needed for the present decision assessment; no claim about completing all Petz quadrature nodes is made.

For faithful rho,sigma the unique minimizer satisfies

    (1/2) Z_* rho+(1/2) sigma Z_* = -rho.              (5)

In a left sigma eigenbasis v_j and right rho eigenbasis u_i, with eigenvalues mu_j and lambda_i,

    <v_j|Z_*|u_i>
       = -2 lambda_i/(lambda_i+mu_j) <v_j|u_i>.        (6)

This ordering is important for noncommuting states. Define the squared weighted norm

    Q(E) = (1/2)Tr(rho E^*E)+(1/2)Tr(sigma EE^*).

Expansion and (5) give the exact completion of the square

    F(Z_*+E) = F(Z_*)+Q(E).                           (7)

In the mixed eigenbasis, Q(E)=sum_ij (lambda_i+mu_j)|E_ji|^2/2.

Writing Z=-I+W gives

    F(-I+W)=Re Tr[(rho-sigma)W]+Q(W).                 (8)

When rho=sigma the right side is Q(W)>=0. More generally let Delta=rho-sigma and take W=-(||Delta||_1/2) sign(Delta). Since sign(Delta) is Hermitian with norm at most one, Q(W)<=||Delta||_1^2/4 and its linear term is -||Delta||_1^2/2. Hence

    F(Z_*) <= -||rho-sigma||_1^2/4.                  (9)

This proves the decision gap directly. It does not use a spectral lower bound for either source.

## 3. Fourier representation and its finite cutoff

For real x the classical identity

    tanh(x/2) = 2 integral_0^infinity sin(sx)/sinh(pi s) ds    (10)

follows by expanding 1/sinh(pi s)=2 sum_{n>=0} exp(-(2n+1)pi s) and integrating. The resulting sum is 4x sum_{n>=0}[(2n+1)^2 pi^2+x^2]^-1. This is the logarithmic derivative of the cosh product, NIST DLMF Eq.4.36.2, evaluated at x/2:
https://dlmf.nist.gov/4.36.E2 . The series differentiation and integration are locally uniformly convergent for real x; near zero the sine cancels the 1/s singularity.

Set b=log Z_H-log Z_K, where Z_H=Tr exp(-beta H). Since ||H||,||K||<=M, |b|<=2 beta M. Define

    U_s(H,K,b)=exp(is b) exp(-is beta K) exp(is beta H).

The relative log superoperator A(X)=(log sigma)X-X(log rho) is self-adjoint on Hilbert--Schmidt space and has eigenvalues x_ji=log mu_j-log lambda_i. They satisfy |x_ji|<=4 beta M. Applying (10) to A and then to I gives

    Z_* = -I + integral_0^infinity
             [U_s-U_(-s)]/[i sinh(pi s)] ds.          (11)

Indeed -1+tanh(x/2)=-2/(1+exp(x)), giving exactly (6). Notice that U_(-s) need not equal U_s^*: the order of the two Hamiltonian evolutions is retained. The integral converges in operator norm in this finite-dimensional setting because ||U_s-U_(-s)||<=2s(|b|+beta||H||+beta||K||) at the origin and the scalar kernel decays exponentially at infinity.

Let eta be (3), S=(1/pi)log(128/epsilon), and truncate the integral in (11) to [eta,S], defining Z_c(H,K,b). The discarded scalar multiplier has uniform absolute error at most epsilon/8 on |x|<=4 beta M:

    low-frequency error <= 2|x|eta/pi <= epsilon/16,
    high-frequency error <= 2 integral_S^infinity 1/sinh(pi s) ds
                         <= (16/(3pi)) exp(-pi S)
                         < epsilon/16.               (12)

For the first inequality use |sin(sx)|<=s|x|. For the second use exp(-pi S)=epsilon/128<=1/128, so 1/sinh(pi s)<= (8/3)exp(-pi s) for s>=S. Also eta<=1<S, so the truncated interval is nonempty.

The mixed-basis entries of Z_c-Z_* equal this scalar error times <v_j|u_i>. Since sum_ij (lambda_i+mu_j)|<v_j|u_i>|^2/2=1, (12) implies

    sqrt(Q(Z_c-Z_*)) <= epsilon/8.                    (13)

It would be incorrect to infer a dimension-free operator-norm error merely from the scalar multiplier error. The weighted norm (13), which is exactly the objective norm, is what is needed.

On the other hand, the truncated integral itself has the uniform operator-norm bound

    ||Z_c|| <= 1+2 integral_eta^S 1/sinh(pi s) ds <= B. (14)

Here integral_eta^infinity 1/sinh(pi s) ds=(1/pi)log coth(pi eta/2). Thus B=O(1+log(1+beta M/epsilon)). The normalizations and the partition shift have not been assumed known to the algorithm; Section4 includes b in the candidate family.

## 4. Source-independent cover of the adequate class

For two parameter triples, let

    D=|b-b'|+beta||H-H'||+beta||K-K'||.

The unitary Duhamel inequality gives ||U_s-U'_s||<=|s|D. Therefore

    ||Z_c(H,K,b)-Z_c(H',K',b')||
        <=2D integral_eta^S s/sinh(pi s) ds <=D/2.    (15)

The last integral over [0,infinity) is 1/4, from the same exponential series and sum_{n>=0}(2n+1)^-2=pi^2/8.

Cover each coefficient interval [-1,1] by a grid with mesh at most epsilon/(16 beta M), and cover [-2 beta M,2 beta M] for b by mesh at most epsilon/8, including endpoints. Every point is within the respective mesh of a grid point. Each coordinate needs at most 2+32 beta M/epsilon grid points. There are 2M coefficient coordinates and one b coordinate, which proves (1).

For a nearest triple,

    D <= epsilon/8+epsilon/16+epsilon/16=epsilon/4,
    ||Z_c-Z_grid|| <= epsilon/8.

Since Q(E)<=||E||^2, combine this with (13) and the triangle inequality for sqrt(Q) to get sqrt(Q(Z_grid-Z_*))<=epsilon/4. Equations(7) and (9) prove (4).

This family is defined before seeing either unknown source. It includes every original source pair's suitable approximate optimizer. The candidate shift is enumerated rather than supplied by a partition-function oracle. Known candidate Hamiltonians may be used to specify measurements in the unrestricted collective P1 model; this does not furnish the actual unknown Hamiltonians or claim efficient gate synthesis.

## 5. A valid acquisition bound, and why it is not an improvement

Finite quadrature on [eta,S] can approximate each known Z_grid in operator norm within epsilon/16. For completeness the integrand has a finite uniform derivative bound

    L_int = 8 beta M/sinh(pi eta)
          +2pi cosh(pi S)/sinh(pi eta)^2.

The Riemann error on a mesh h is at most (S-eta)L_int h; choosing h<=epsilon/[16(S-eta)L_int] suffices. Further deterministic implementation errors can be absorbed by choosing a finer mesh. No source copies are used to specify known candidate matrices. This is a finite computability statement, not an efficient-circuit theorem.

Denote such a computed operator by Z_tilde. Its norm is at most B+1. The total weighted error from Z_* is at most 5epsilon/16, so

    F(Z_tilde) <= -epsilon^2/4+25epsilon^2/256
                =-39epsilon^2/256 <=-epsilon^2/8.      (16)

Every computed candidate still has nonnegative F under exact equality, since that fact holds for all operators independently of approximation.

On one paired sample omega=rho tensor sigma define

    C_Z=(Z+Z^*+(1/2)Z^*Z) tensor I
             +I tensor ((1/2)ZZ^*),
    R=(B+2)^2,
    E_Z=[R I-(I+C_Z)]/(2R).

The norm bound ||I+C_Z||<=1+2||Z||+||Z||^2<=R makes E_Z an effect. Its expectation is 1/2-F(Z)/(2R). Under equality every effect mean is at most 1/2; under the alternative some mean is at least 1/2+epsilon^2/(16R).

Badescu--O'Donnell's quantum Threshold Decision theorem, CorollaryA.4 on PDF page33, applies to this finite list of known effects:
https://www.cs.cmu.edu/~odonnell/papers/quantum-data-analysis.pdf . Set threshold 1/2+epsilon^2/(32R) and tolerance epsilon^2/(64R), so the null and alternative lie in disjoint required regimes. Its copy bound gives

    TOTAL original copies
      = O( R^2 epsilon^-4 [log L+log(1/delta)] ).      (17)

Each paired sample consumes two original copies. The factor of two is included in the O notation. This is an actual copy-only collective test with a uniform hard budget, albeit with unrestricted computation and measurement complexity. It does not assume a free measurement-selection oracle or unconstrained variational training.

At fixed beta,k,epsilon this gives O(M log^5 M), whereas the already accepted Helstrom-net upper gives O(M log M). Its epsilon dependence is also worse. Consequently (17) is recorded only to expose the full acquisition accounting; it is NOT advertised as an improved bound. The useful conclusion of this pass is the adequacy statement (1)--(4), which removes inverse-state conditioning as a necessary premise for this particular variational family.

## 6. Does the quadratic objective itself remove the cover cost?

There is a genuine null-side quadratic structure, but it is insufficient by itself. Let W=Z+I, H_W=(W+W^*)/2 and define a paired observable

    D_W=H_W tensor I-I tensor H_W
          +(1/2)W^*W tensor I+(1/2)I tensor WW^*.

Its mean is F(-I+W). Under rho=sigma, put q=Tr[rho(W^*W+WW^*)]/2. Then E D_W=q and

    E D_W^2 <= (4+2||W||^2) q.                       (18)

To prove this, write D_W=L+P with L=H_W tensor I-I tensor H_W and P the positive quadratic part. Then E L^2=2 Var_rho(H_W)<=2q, since H_W^2<=(W^*W+WW^*)/2. Also 0<=P<=||W||^2 I and E P=q. Finally (L+P)^2<=2L^2+2P^2. This is a per-operator null moment bound, not a uniform empirical-process or adaptive-selection theorem. Under unequal sources the same matching of quadratic forms does not automatically control both orientations of W in H_W^2.

No justified argument here reduces the search cost below log L or proves a uniform fast decision rate for the whole nonlinear family. In particular a blanket O(sqrt(M) polylog N) fixed-accuracy tester from parameter dimension alone would contradict the accepted P1 lower bound32 in its stated k>=5, fixed-beta, epsilon<=1/4096 domain. Its exponent min{(2k+2)/3,(4k-1)/5} exceeds k/2; its logarithmic overhead does not remove that contradiction. This is an inherited consistency constraint, not a new lower bound.

## 7. Prior comparison, limitations and exact remaining step

The Sylvester variational formulation is established prior work (Lu--Fang, cited above). The Fourier identity is classical. Real-time filtering of thermal functions is also an established technique; Hastings, *Quantum Belief Propagation*, arXiv:0706.4094v3, Eqs.(6)--(10), provides a related thermal-filter construction:
https://arxiv.org/pdf/0706.4094 . Its geometric locality conclusions use stronger locality assumptions and are not imported for this coefficientwise-only class. The present calculation does not establish historical novelty.

The adequate operators are products and integrals of candidate Hamiltonian evolutions, not members of the local Pauli linear span. Therefore earlier local-mean failure34 does not invalidate the adequacy argument. Conversely, parameterizing an adequate family is not a training, learning or measurement-selection guarantee; earlier learning and scalar-score failures remain intact.

The accepted lower-bound reference is:
https://github.com/Sodelin/Research-Commons/blob/9b7bb4034a136542a4d2c06afce84c64d1a50ce3/research/2026-10-16-g6-gibbs-certification/latent-light-fraction-32/README.md

The accepted full-class upper reference is:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md

The decisive missing step is a decision-specific collective procedure that exploits this source-controlled nonlinear family with a proven total-copy rate improving the existing upper while remaining consistent with the lower bounds. A source-uniform localized complexity or variance theorem would have to be proved for this actual family and both hypotheses; (18) and parameter count alone do not supply it. The full optimal-copy P1 target remains open.

Primary passages were checked on18 October2026 UTC. No exhaustive prior search or external peer review is claimed. An adjacent finite checker, if present, is diagnostic verification of displayed identities and constants only; it cannot replace the all-N argument.
