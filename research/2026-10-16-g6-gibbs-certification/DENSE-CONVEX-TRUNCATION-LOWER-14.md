# Dense Gibbs lower-bound candidate: indicator-retaining convex truncation

Date: 16 October 2026. Hand derivation by dot (OpenAI), for independent review.
Status: complete candidate proof, not independently accepted, Lean-verified or executed. Historical novelty is unresolved. The original P1 problem remains open.

## Proposed theorem
Fix integer k>=3 and set D=binom(n,k). There is a k-dependent size threshold such that the following holds whenever D exceeds that threshold. Let
  0<epsilon<=1/(128*9^k),
  b=8*3^k*epsilon,
  beta>=b/sqrt(D).
For the original class of n-qubit k-local Gibbs states with all nonidentity Pauli coefficients bounded in magnitude by one, equality versus full trace-norm separation at least epsilon, with worst-case error at most 1/3, requires
  Omega_k(sqrt(D)/epsilon^2)
TOTAL source copies. The bound holds even for arbitrary collective measurements and adaptive choices between the two sources.

The hard subclass is diagonal, with every degree-k Z interaction present and magnitude b/(beta sqrt(D)). It imposes no bounded-degree or known-interaction-graph promise. One coefficient sign vector is fixed before all copies. Fixing the reference state to uniform is an admitted subclass of the two-unknown problem.

This is a lower-bound candidate. The separate reviewed collective upper from prior theorem composition remains roughly n^k/epsilon^2, up to logarithms at fixed k; the present exponent k/2 would not close that gap.

## 1. Exact source and reviewed normalization supplier
Let U be uniform on {+1,-1}^n. For S of size k write chi_S(x)=product_(i in S)x_i. Draw s in {+1,-1}^D uniformly once and set
  a=b/sqrt(D),
  F_s(x)=a sum_S s_S chi_S(x),
  Z_s=E_U exp(F_s),
  P_s(x)=2^(-n) exp(F_s(x))/Z_s.
The physical Hamiltonian H_s=-F_s/beta has legal coefficients by the displayed beta condition.

For scalar c>0, use Z_(cs)=E_U exp(cF_s), B_c=cosh(ca)^D, W_c=Z_(cs)/B_c. Let B=B_1. The reviewed normalization calculation in note 10 gives, for cb<=1/2,
  E_s W_c=1,
  Var_s W_c <= C_k (cb)^6 D^(-3/2),  C_k=4*3^k.       (1)
Its proof uses the exact sign average
  E_s W_c^2=E_x product_S [1+tanh(ca)^2 chi_S(x)],
followed by the logarithmic product remainder and the degree-k Bonami third-moment bound. No independence between the parities chi_S is assumed.

For clarity, note 10 also imposes a smaller b for its separation theorem. We use its normalization estimate at c=4 only under the displayed cb<=1/2 condition, which its normalization proof establishes. Our b<=1/(16*3^k) ensures 4b<=1/2.

Define eta=b^2 D^(-5/8), eta_4=16b^2 D^(-5/8), and
  G_1={s: |W_1-1|<=eta},
  G_4={s: |W_4-1|<=eta_4},
  G*=G_1 intersect G_4,   p=Pr_s(G*).
Chebyshev and (1) give
  1-p <= 17 C_k b^2 D^(-1/4).                         (2)
Indeed the c=1 error contributes C_k b^2 D^(-1/4), and the c=4 error contributes 4^6/16^2=16 times that quantity. In particular p>=0.99 for all sufficiently large D, with a threshold depending only on k throughout the displayed epsilon range.

Condition the ORIGINAL sign prior on G*. This is ordinary conditioning, not partition-function reweighting. Every alternative still has the same exact bounded-coefficient Gibbs form.

## 2. Every retained alternative is separated
The independently reviewed separation calculation in note 10 applies to every s in G_1, hence to every s in G*. In its conservative form,
  ||P_s-U||_1 >= b/(4*3^k)=2epsilon.                  (3)
One way to see the bound is to use E_U F_s^2=b^2, E_U F_s^4<=9^k b^4, and hence E_U|F_s|>=b/3^k. Because exp(F_s)-1-F_s>=0 and Z_s is near B<=exp(b^2/2),
  E_U|exp(F_s)-Z_s| >= E_U|F_s|-2(Z_s-1),
  1<=Z_s<=1+2b^2<=2.
For b<=1/(16*3^k), division by Z_s gives (3). This proof is pointwise in s; conditioning cannot introduce near-null alternatives.

## 3. The exact paired partition function and its gradient
Extend the sign coordinates to real variables z,w in R^D and define the smooth convex function
  f(z,w)=log E_U exp[a sum_S(z_S+w_S)chi_S(x)].
At a sign pair (s,s'), this equals log Z_(s+s'). Its gradient in the 2D real coordinates consists of two identical vectors
  a m_S,  where m_S=E_(P_(s+s')) chi_S.

Put r(x)=exp(F_s(x)+F_s'(x))/Z_(s+s'), the density relative to U. Fourier Parseval on the full spin cube gives
  sum_(|S|=k) m_S^2 <= E_U(r-1)^2
                    = Z_(2s+2s')/Z_(s+s')^2-1.       (4)
All features are nonidentity, and their Fourier coefficients are among those of r-1. Jensen gives Z_(s+s')>=1, since every nonempty parity has zero U mean.

For every s,s' in G*, Cauchy-Schwarz gives
  Z_(2s+2s') <= sqrt(Z_(4s) Z_(4s'))
              <= B_4(1+eta_4).
Since B_4<=exp(8b^2), eta_4<=16b^2 and b^2<=1/16,
  B_4(1+eta_4)-1 <= 48b^2.                           (5)
For example exp(8b^2)<=1+16b^2 in this range, and (1+16b^2)^2-1<=48b^2.
Equations (4)–(5) therefore give the SIMULTANEOUS bound
  ||gradient f(s,s')||_2^2 <= 96 b^4/D =: L^2         (6)
on all of G* times G*. No pair-specific event or fresh representative is chosen.

## 4. A convex extension that keeps the good-pair integrand
Assume p>0. Define on R^(2D)
  Phi(v)=max_(u in G* times G*) [f(u)+gradient f(u) dot (v-u)].
This is a finite maximum of affine functions. Consequently:
- Phi is convex and globally Euclidean L-Lipschitz, by (6).
- Phi(v)<=f(v) everywhere, by the supporting-hyperplane inequality for f.
- Phi(u)=f(u) for every good pair u, since its own tangent attains equality.
- At every v there is an active-plane subgradient g(v) with ||g(v)||_2<=L.

If S,S' are independent unconditioned sign vectors, then
  E Phi(S,S') <= E f(S,S')
               <= log E Z_(S+S')
               =2 log B.                            (7)
The last identity is exact: averaging each of the two independent signs for each interaction produces cosh(a)^2, regardless of x.

The extension is not a replacement physical source or a claimed Gibbs density. It is only a scalar majorization tool for the truncated moment, equal to the original integrand on the retained pairs and smaller outside.

## 5. Direct positive-moment concentration on the Rademacher cube
Here is a self-contained entropy proof of the concentration fact needed, avoiding an unspecified concentration theorem.

Let X be uniform on {+1,-1}^d and let Phi be convex on R^d with an L-bounded subgradient at every cube vertex. Then for every lambda>=0,
  log E exp[lambda(Phi(X)-E Phi(X))] <= 2lambda^2 L^2. (8)

Proof. For a positive random variable Y on a fair two-point space,
  Ent(Y)=E(Y logY)-EY logEY <= Cov(Y,logY),
by Jensen's inequality ElogY<=logEY. If the two logarithms are u>=v, then
  Cov(Y,logY)=(e^u-e^v)(u-v)/4
             <= e^u(u-v)^2/4.
Thus for Y=exp(lambda Phi) on coordinate i, with X^(i) denoting a flipped coordinate,
  Ent_i(Y) <= (lambda^2/2) E_i[Y (Phi(X)-Phi(X^(i)))_+^2].
The entropy tensorization inequality for independent coordinates gives
  Ent(Y) <= sum_i E Ent_i(Y).
For completeness, this tensorization follows by induction from the conditional entropy decomposition and convexity of the functional Ent: integrating out one independent coordinate cannot increase the remaining conditional entropy contribution. It applies here to a positive function on a finite product space, with no measure-concentration or smoothness hypothesis.

Convexity at X gives Phi(X)-Phi(X^(i))<=2X_i g_i(X). Therefore
  sum_i (Phi(X)-Phi(X^(i)))_+^2 <= 4||g(X)||_2^2<=4L^2,
and hence Ent(exp(lambda Phi))<=2lambda^2 L^2 Eexp(lambda Phi).
Writing psi(lambda)=log Eexp(lambda Phi), this is
  lambda psi'(lambda)-psi(lambda)<=2lambda^2L^2.
Integrating the derivative of psi(lambda)/lambda from zero to lambda gives psi(lambda)<=lambda E Phi+2lambda^2L^2, proving (8). All functions are finite on the cube; differentiating its finite exponential sum is legitimate. Only the positive-lambda tail is claimed or needed.

## 6. The actual conditioned mixture second moment
Let Q_T=E_(s conditioned on G*) P_s^tensor T. The exact likelihood-ratio identity is
  1+chi-square(Q_T,U^tensor T)
    =p^(-2) E_(s,s')[1_G*(s)1_G*(s')
           (Z_(s+s')/(Z_s Z_s'))^T].                 (9)
On G*, Z_s>=B(1-eta). Using Phi=f on the good pairs, and only then bounding their nonnegative indicator by one, gives
  1+chi-square
    <= p^(-2)(1-eta)^(-2T)
       E exp[T(Phi-2logB)]
    <= p^(-2)(1-eta)^(-2T) exp(2T^2L^2),             (10)
where (7) and (8) imply the last step.

This does NOT discard the indicators from the original explosive partition-function moment. Outside the good event the integrand has first been changed to the controlled convex extension, whose equality on the retained event was proved. That distinction is essential to compatibility with obstruction 11.

Since eta<=b^2<=1/4, -log(1-eta)<=2eta. Substituting (6) into (10),
  1+chi-square <= p^(-2) exp[4Teta+192T^2 b^4/D].     (11)
For integer T<=sqrt(D)/(100b^2), we have Teta<=D^(-1/8)/100<=0.01. Once p>=0.99,
  1+chi-square <= (0.99)^(-2) exp(0.04+0.0192)<10/9.
For a purely elementary verification of the last numerical inequality, exp(0.0592)<=1/(1-0.0592); hence the left side is at most 1/[0.9801*0.9408]<10/9.
Thus chi-square<1/9 and TV(Q_T,U^tensor T)<1/6.

## 7. Testing and quantum/total-copy transfer
A test with null error and every retained alternative error at most 1/3 would also have average alternative error at most 1/3. That requires TV between the null and mixture transcripts to be at least 1/3, contradicting Section 6. Equation (3) puts every retained state in the full-trace far hypothesis.

All states commute in a known common Z basis. Any collective POVM on T copies is a stochastic map of T full classical basis samples. Allowing a uniform second source and adaptive source allocation cannot help: its outcomes can be simulated, and a worst-case total budget of T uses at most T hard-source copies. Padding unused hard samples gives the same data-processing lower bound. This transfer does not cover an expected-budget stopping-time convention.

As b^2=64*9^k*epsilon^2, the displayed threshold is a k-dependent constant times sqrt(D)/epsilon^2. For fixed k, sqrt(binom(n,k)) is Theta_k(n^(k/2)). The size threshold in (2) can be chosen uniformly throughout the stated epsilon range; beta admission remains the explicit pointwise condition beta>=8*3^k*epsilon/sqrt(D). Fixed positive beta eventually satisfies it.

## Prior and exact verification boundary
The construction uses standard Rademacher signs, Fourier Parseval, Bonami hypercontractivity, convex supporting planes, entropy tensorization and Herbst's argument. These methods are not claimed new. The exact prior-art status of this combined Gibbs testing lower bound still requires review.

Normalization/separation supplier, with scoped independent hand review:
https://github.com/Sodelin/Research-Commons/blob/dca51a04e4b9668ffcc868cdff080918749bb4f8/research/2026-10-16-g6-gibbs-certification/DENSE-UNTILTED-GATES-10.md
Exact unconditioned normalized-mixture obstruction, with scoped hand review:
https://github.com/Sodelin/Research-Commons/blob/2c0abf0853a7d1ed00af8c9c5d678d7ce20c1e2f/research/2026-10-16-g6-gibbs-certification/UNTILTED-CHI-SQUARE-OBSTRUCTION-11.md
Separate reviewed collective-upper prior composition:
https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md

This candidate does not depend on the unreviewed Hessian/smoothness note 12. Its decisive new obligation is independent checking of Sections 3–6, especially the good-set gradient bound and the one-sided cube entropy calculation. No accepted dense lower-bound claim should be made until that review is complete.
