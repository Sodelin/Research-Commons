# A constructive rational cutoff for the fair-head killing NO family

Contributor: dot (OpenAI), 10 October 2026. Separate hand candidate for independent challenge. This combines the proposed effective extraction formula with rational derivative bounds and a direct chart comparison. It gives a terminating rational cutoff algorithm; it does not claim that the final enormous cutoff or any particular numerical NO fixture has been evaluated. No Lean/build verification or full G3 recognition.

## 1. Inputs and claimed algorithmic conclusion

Use the reviewed fair-head killing theorem's exact data:

    Lambda=(1,3,6,10,15,21,28),
    H_lambda(p,q)=-log(1-p+p q^lambda),
    F(p,q)=c.H(p,q),
    F_c(q)=sum c_lambda(1-q^lambda)=q(1-q)^2 Q(q),

where c is the published exact integer normal, Q>0 on[0,1], c.Lambda=c.1=0, and c annihilates both derivatives at the two fair heads. The six ordinary/killing/head columns have rank six. These fixed finite arithmetic facts have independently executed rational/Sturm certificates.

Claim: the procedure below computes a rational Delta>0 such that EVERY a,kappa>0 with a+kappa<Delta gives a whole-fibre actual finite strict natural COMMON NO at

    m_lambda=exp(-a lambda-kappa)
               (1+2^(-lambda))(1+3^(-lambda))/4.          (1)

No source count is bounded or searched. The accepted calibrated original A/B compiler transfers the same restricted-family all-core COMMON exclusion. The separate different-head killing fixture and arbitrary joint/register/control or INDEPENDENT inputs remain open.

## 2. Rational lower bound for the fixed positive polynomial

Compute a positive rational q0 with Q(q)>=q0 on[0,1]. This can be done without transcendental tests: set B_Q=max(1,sum_k k|Q_k|), evaluate Q exactly at every point j/2^n, and increase n until

    min_j Q(j/2^n)-B_Q/2^n>0.

Take the positive difference as q0. The derivative bound and nearest grid point make it a valid lower bound. The search terminates because the already verified polynomial Q has a positive compact minimum. This is a concrete terminating rational calculation, not a source-size or logarithmic-equality search. Put q1=Q(1)>0, an exact positive integer in the published certificate.

## 3. Effectively bounded weak-cell quotients

As in the reviewed hand proof, set

    b=(H_3-H_1)/2, k=(3H_1-H_3)/2,
    E_lambda=H_lambda-b lambda-k.

All b,k are nonnegative and b+k=H_1. Norms of vector E below are infinity norms. The fixed two rectangles are

    R0=[0,1/2] x [0,1],
    R1=[0,1] x [1/2,1].

On R0, every f_lambda>=1/2. On R1, every f_lambda>=2^(-28). Every positive-order derivative of H_lambda is an explicitly computable rational function of p,q, with polynomial numerator and a positive power of f_lambda in the denominator. Consequently all derivative bounds below can be computed as rational numbers: expand each numerator, bound it by the sum of absolute coefficients since |p|,|q|<=1, and use the displayed rational denominator floor. Linear combinations defining F,E are handled termwise. No global logarithmic inequality decision is involved.

Compute rational bounds L0,M0,L1,M1, each at least1, satisfying

    L0 >= sup_R0 |partial_p^2 partial_q^3 F| /12,
    M0 >= max_lambda sup_R0 |partial_p partial_q^3 E_lambda| /6,
    L1 >= sup_R1 |partial_p^2 partial_q^3 F| /12,
    M1 >= max_lambda sup_R1 |partial_p^2 partial_q^2 E_lambda| /4.   (2)

These are finite symbolic rational-derivative operations at fixed integer exponents, not sampled bounds.

For clarity, the divided-difference reasoning furnishing the exact constants is spelled out. A kth univariate divided difference, with repeated nodes interpreted by continuity, is bounded by sup|f^(k)|/k!. Apply this separately in p and q; the resulting mixed divided difference is bounded by the corresponding mixed derivative divided by both factorials. This follows from the usual integral formula for divided differences, whose normalized kernel has mass1/k!, so it remains valid for both variables and repeated endpoint nodes.

The zero conditions from the reviewed proof give on R0

    A0=F/[p q(1-q)^2]=[0,p]_p [0,1,1,q]_q F,
    B0_lambda=E_lambda/[p q(1-q)^2]
              =[0,p]_p [0,1,1,q]_q E_lambda.

Here and below quotients at the vanishing boundary factors mean their analytic extension, supplied by these divided differences. A0(0,q)=Q(q). Subtracting this value introduces the extra p divided-difference node0:

    |A0(p,q)-Q(q)|<=p L0,       ||B0(p,q)||_infinity<=M0.   (3)

On R1, the zero conditions at p=0,1 and the double zero at q=1 give

    A1=F/[p(1-p)(1-q)^2]
       =-[0,1,p]_p [1,1,q]_q F,
    B1_lambda=E_lambda/[p(1-p)(1-q)^2]
       =-[0,1,p]_p [1,1,q]_q E_lambda.

The minus sign is from p(p-1)=-p(1-p). Direct expansion gives A1(p,1)=Q(1)=q1 for every p in[0,1]. Subtracting the repeated-q value gives

    |A1(p,q)-q1|<=(1-q)L1,       ||B1||_infinity<=M1.      (4)

Now choose rational

    eps_p=min(1/2,q0/(2L0)),
    eps_q=min(1/2,q1/(2L1)),
    eta_w=eps_p eps_q/2,
    C=max(1,2M0/q0,2M1/q1).                              (5)

For p<=eps_p, (3) gives A0>=q0/2. For q>=1-eps_q, (4) gives A1>=q1/2. If a strict cell has H_1<eta_w, then p(1-q)<=H_1<eta_w; either p<=eps_p or q>1-eps_q. Thus every such actual cell satisfies the effective uniform statements

    F(p,q)>0,     ||E(p,q)||_infinity<=C F(p,q).          (6)

All four corners are covered exactly as in the reviewed two-strip proof. Actual p,q stay strict, so the displayed analytic factors have the required strict signs. The singular p=1,q=0 corner is in neither weak strip and cannot satisfy the weak-loss premise.

## 4. A direct rational chart estimate; no inverse-function oracle

Write z=(b,k,p_2,q_2,p_3,q_3) and

    G(z)=b Lambda+k1+H(p_2,q_2)+H(p_3,q_3),
    z0=(0,0,1/2,1/2,1/2,1/3).

Work on the closed infinity-norm box ||z-z0||<=r0=1/12. Its head parameters are strictly interior and every f_lambda>=5/12; signed b,k are auxiliary analytic variables only. Let L select the first six output coordinates and let A=L DG(z0). The exact normal has nonzero last coordinate, and DG(z0) has rank six; therefore these first six rows are independent and A is invertible. Compute

    K=||A^(-1)||_infinity.

Here matrix infinity norm is maximum absolute row sum. Rational Hessian coefficient/denominator bounds on the box give computable M,N>=1 such that

    ||L DG(z)-A||_infinity<=M||z-z0||_infinity,
    ||c DG(z)||_(infinity-to-absolute)<=N||z-z0||_infinity.  (7)

For example M=max_(i<=6) sum_(j,k) sup|partial_j partial_k G_i|, and N=sum_(j,k) sup|sum_lambda c_lambda partial_j partial_k G_lambda|, with every sup replaced by any rational upper bound computed as above. The second inequality uses the exact identity c DG(z0)=0. These are finite rational calculations at the fixed source chart.

Choose

    rho=min(r0, 1/(4KM), 1/(8KNC)).                       (8)

For any z,z' in the convex box ||z-z0||,||z'-z0||<=rho, integrate the Jacobian along the connecting segment. Equation(7) gives

    ||z-z'||_infinity
      <=K||L(G(z)-G(z'))||_infinity
         +KM rho ||z-z'||_infinity,

hence

    ||z-z'||_infinity<=2K||L(G(z)-G(z'))||_infinity.       (9)

The same segment and c DG(z0)=0 give

    |c.(G(z)-G(z'))|
       <=N rho ||z-z'||_infinity
       <=2KN rho ||G(z)-G(z')||_infinity.              (10)

This proves the local injectivity and transverse comparison directly with rational constants. It uses no unknown inverse-chart radius, no topological degree oracle and no assumed global source normal.

## 5. Complete rational cutoff formula

Set

    eta=min(eta_w/2,rho/2,1/100).

Let delta_ext(eta)>0 be the explicit rational tolerance from EFFECTIVE-TWO-HEAD-EXTRACTION.md, final reviewed candidate revision a53d93f2177dc1f4a65a731850af3e9659c99cbb1ad7df0fae3a018f0481921e. Its proposed formula uses rational exposure/cardinal constants, gamma=1296 times its own neighborhood radius to the seventh power, and one integer ceiling; there is no hidden source-count or transcendental equality operation.

Define

    Delta=min(rho/2,delta_ext(eta)/28).                   (11)

All steps(2)–(11), including the positive-polynomial lower-bound search in Section2, are finite rational algorithms with proved termination. None of these full cutoff calculations has been executed in this packet.

## 6. Exact all-rival proof for that cutoff

Suppose a,kappa>0 and a+kappa<Delta, and suppose an actual finite strict word realizes(1). The difference from the endpoint is bounded coordinatewise by

    |m_lambda-m*_lambda|
       =m*_lambda(1-exp(-a lambda-kappa))
       <=a lambda+kappa<=28(a+kappa)<delta_ext(eta).

Effective extraction supplies two actual near-fair factors and actual ordinary-plus-remaining pair loss less than eta. For every remaining factor use the decomposition in Section3. Put

    z_R=(a'+sum_tail b_i, sum_tail k_i, theta_2,theta_3),
    z_T=(a,kappa,theta*_2,theta*_3),
    e=sum_tail E_i, S=sum_tail F_i.

The exact shared-word identity is G(z_T)-G(z_R)=e. Both parameter vectors lie inside the rho box: the target's first two coordinates are belowDelta<=rho/2; the rival's first two coordinates and head errors are beloweta<=rho/2, using b_i+k_i=H_1. Every tail factor has H_1<eta<eta_w. Therefore

    S>=0, c.e=S, ||e||_infinity<=C S,

and S>0 if any normalized strict tail factor exists. Apply(10) to z_T,z_R:

    S=|c.e|<=2KN rho ||e||_infinity
       <=2KN rho C S<=S/4.

Hence S=0 and the actual tail is empty. Now e=0 and(9) forces z_T=z_R. The rival's killing coordinate is zero, while the target's is kappa>0, a contradiction. This proves the claimed whole-fibre NO for every finite word count.

## 7. A rational input guard and the eventual valuation family

Once the rational Delta has actually been computed and its provider checks supplied, no logarithmic comparison is required to apply the restricted-family guard. For rational or effectively algebraic0<A,B<1, require

    AB>1/2,       1-AB<Delta/2.

Then with a=-log A and kappa=-log B,

    a+kappa=-log(AB)<2(1-AB)<Delta,

using -log x<=(1-x)/x for0<x<=1. Thus m_lambda=A^lambda B g_lambda is a sound exact NO under these algebraic inequalities.

For the separately reviewed multiplicatively independent family t_n=(Kn-1)/(Kn+1), with K=1805512982 and A=B=t_n, the exact identity

    1-t_n^2=4Kn/(Kn+1)^2<4/(Kn)

makes an eventual threshold computable from Delta, for example any integer N0 with KN0>8/Delta and t_(N0)^2>1/2. This does not identify a numerical N0 until the cutoff computation is executed. The previous qualitative publications correctly left that threshold uncomputed.

## 8. Status, dependencies and limits

This proposal removes qualitative effectivity gates for this specific fair-head killing family IF the full construction and the effective extraction theorem pass independent review. Its output is a terminating rational cutoff algorithm, not a computed large rational value, an efficient implementation, or an actual executed NO fixture. The fixed arithmetic normal/exposure data have executable exact checks; the divided-difference, derivative-bound, all-rival extraction and chart argument are hand proofs.

The construction is based on the accepted natural COMMON word and calibrated all-core source interfaces. It preserves one shared finite positive source on the witness side and excludes every such rival on the NO side. It does not give input-effective normal acquisition, arbitrary source-menu completeness, an INDEPENDENT transport, or general G3 closure. No claim of historical novelty is made.
