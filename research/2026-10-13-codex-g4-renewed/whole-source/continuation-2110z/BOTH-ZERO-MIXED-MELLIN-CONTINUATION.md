# Meromorphic continuation of the both-zero-arm mixed endpoint

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Publisher: Codex lead G4 researcher. **Hand-derived proof; independent
review pending.** No computational or formal verification is asserted.

The all-arity finite combinatorial identity and Jacobi/semicircle moment
representation are inherited from
[BOTH-ZERO-MIXED-ENDPOINT-SOL-AUDIT.md](BOTH-ZERO-MIXED-ENDPOINT-SOL-AUDIT.md).
The spectral density below was also independently derived by that reviewer;
its coefficient formula agrees with the derivation here. This packet proves
the remaining Mellin continuation, including the fair-coin zero support
endpoint. It does not admit zero-arm physical rivals: these are auxiliary
compactification factors in the original source analysis.

## 1. Exact inherited moment and the required conclusion

Fix T>0 and 0<g<1; put q=1-g and R=2sqrt(gq), so 0<R<=1. Let U_T be the
Jacobi diffusion started at zero, with generator

    Lf(u)=(1/2)u(1-u)f''(u)+(1-u)f'(u),

and let V be independent with radius-one semicircle density
(2/pi)sqrt(1-v^2), -1<v<1. The inherited exact identity is

    v_n/kappa_(n+1)=M(n),
    M(n)=E[(1+R sqrt(U_T)V)^n], n=0,1,2,... .           (1)

Equivalently, its finite polynomial expansion is

    M(n)=sum_(r=0)^floor(n/2)
       binom(n,2r) Catalan_r [gq]^r p_(r+1,1)(T).

Let A=1+R and B=1-R. Define, where the integral exists,

    E(z)=A^(-z) E[(1+R sqrt(U_T)V)^z],                 (2)

with positive-real powers on the support. The conclusions are:

* E is bounded holomorphic on Re z>=0, real and positive on the positive
  real axis, E(0)=1, and log E(n)=o(n).
* If g!=1/2, E is entire.
* If g=1/2, E is meromorphic on the whole plane with possible simple poles
  only at -3/2,-5/2,... . The pole at -3/2 is genuine. In particular E is
  holomorphic at -1/2 and has finite pole order at -3/2.

Thus M(n)=A^n E(n) has a known linear normalization and a phase-free,
zero-exponential-type right-half-plane multiplier, with sufficient global
meromorphic control for the existing accumulating-zero argument.

## 2. Explicit analytic density of the Jacobi variable

The boundary u=1 is absorbing. Its atom at time T is

    Xi(T)=P(U_T=1)=lim_(r->infinity)E[U_T^r]
         =lim_(r->infinity)p_(r+1,1)(T)>0.             (3)

The equality of moments is part of the inherited proof. Positivity follows
from the pure-death descent-time argument already given in the strict mixed
packet: the expected time from any sufficiently large number of lineages
to L is at most 2/L, after which there is a fixed positive probability of
reaching one before the remaining time expires. No positivity conclusion
is inferred merely from an alternating series.

We now prove the needed regularity of the interior law by an explicit
spectral series. Let h(u)=1-u. Direct differentiation gives Lh=-h and

    h^(-1)L(h f)+f
       =(1/2)u(1-u)f''+(1-2u)f'=:Jf.                  (4)

This is the Jacobi (2,2) generator with invariant probability density
w(u)=6u(1-u). Its polynomial eigenfunctions and squared norms are

    Q_m(u)=P_m^(1,1)(2u-1),
    J Q_m=-eta_m Q_m,        eta_m=m(m+3)/2,
    d_m=integral_0^1 Q_m(u)^2 w(u)du
         =6(m+1)/[(2m+3)(m+2)],
    Q_m(0)=(-1)^m(m+1).                               (5)

These identities follow directly from the Jacobi polynomial differential
equation, Rodrigues formula and its beta-integral norm. For example the
shifted Rodrigues formula is

    Q_m(u)=(-1)^m/[m! u(1-u)]
                  (d/du)^m [u^(m+1)(1-u)^(m+1)].

The eigenfunctions form a complete orthogonal system in L^2(w): polynomials
are dense there by polynomial approximation on [0,1]. Integration by parts
makes J symmetric with respect to w. The Jacobi diffusion semigroup thus
has, for T>0, the density

    p^J_T(x,u)=w(u) sum_(m>=0)
                   exp(-eta_m T)Q_m(x)Q_m(u)/d_m.     (6)

There is no unproved spatial regularity assertion hidden in (6). On each
compact complex u set, the finite polynomial formula bounds Q_m(u) by
exp(C_K m log(2+m)); the coefficients Q_m(0)/d_m grow only polynomially.
Gaussian spectral decay exp(-eta_m T) therefore gives normal convergence
of (6) and all its u derivatives after removing w(u). The series realizes
the spectral semigroup; its continuous extension in x to the entrance
boundary x=0 follows from the same uniform bounds on [0,1]. Standard Jacobi
diffusion existence, or its polynomial martingale problem, identifies this
semigroup with the generator in (4). Formula (6), not an unsupported
smoothness assumption at a boundary, supplies the analytic continuation.

The generator conjugacy (4) gives the killed interior semigroup of U:
for a bounded test function supported away from u=1,

    P^U_T f(x)=h(x) exp(-T) P^J_T(f/h)(x).

This is the usual eigenfunction/Doob transform; it also follows by
differentiating the two sides and using their identical initial values
and generator equation. At the starting point x=0, (6) yields the
interior density

    rho_T(u)=exp(-T) p^J_T(0,u)/(1-u)=u S_T(u),

    S_T(u)=sum_(m>=0)(-1)^m(2m+3)(m+2)
                 exp[-lambda_(m+2)T] P_m^(1,1)(2u-1)
          =sum_(m>=0)(2m+3)(m+2)
                 exp[-lambda_(m+2)T] P_m^(1,1)(1-2u).  (7)

Here eta_m+1=lambda_(m+2), and parity gives the second form. The Gaussian
spectral estimate proves that S_T is entire in u for each T>0. The law of
U_T consists of rho_T(u)du on (0,1) and the absorbing atom Xi(T) at one.
There is no atom at zero at T>0: the semigroup transform applies to bounded
test functions supported away from one, including approximations of the
indicator of zero, and the Jacobi semigroup in (6) has a density there.
Thus this conclusion does not require an additional unproved regularity
assertion for the original diffusion at its initial boundary.

## 3. Fair coin: an analytic square-root germ at zero

Assume g=q=1/2, so R=1, and write Z=1+sqrt(U_T)V. Given U_T=u>0, its density
at y is

    f(y|u)=2/(pi u) sqrt[u-(y-1)^2],
                 (y-1)^2<u, 0<y<2.                  (8)

The atom U_T=1 contributes

    f_atom(y)=(2 Xi(T)/pi)sqrt[1-(y-1)^2].

Using rho_T(u)=u S_T(u), the interior contribution is

    f_cont(y)=(2/pi) integral_((y-1)^2)^1
                        S_T(u)sqrt[u-(y-1)^2]du.      (9)

Let delta=1-(y-1)^2=2y-y^2. Substitution u=(y-1)^2+delta t gives the exact
formula on 0<y<2

    f(y)=(2 Xi(T)/pi)delta^(1/2)
       +(2/pi)delta^(3/2)
             integral_0^1 S_T(1-delta+delta t)t^(1/2)dt.           (10)

Since S_T is entire, the integral in (10) is an entire function of delta;
normal convergence on compact delta sets justifies termwise integration.
Near y=0 this proves

    f(y)=y^(1/2) H_T(y),                               (11)

where H_T is analytic on a full complex neighborhood of zero. Explicitly,

    H_T(y)=(2 Xi(T)/pi)(2-y)^(1/2)
       +(2/pi)y(2-y)^(3/2)
             integral_0^1 S_T(1-(2y-y^2)+(2y-y^2)t)t^(1/2)dt,

using the branches positive for small real y. In particular

    H_T(0)=2sqrt(2)Xi(T)/pi>0.                         (12)

The absorbing atom gives the leading square-root term; the interior Jacobi
law contributes first at order y^(3/2). This distinction controls the
Mellin pole and prevents a spurious stronger singularity from being assumed.

## 4. Meromorphic Mellin continuation

For the fair coin, M(z)=integral_0^2 y^z f(y)dy converges absolutely and is
holomorphic for Re z>-3/2, by (11). Choose epsilon>0 strictly smaller than
the radius of analyticity of H_T at zero, and write H_T(y)=sum_(m>=0)h_m y^m.
The integral over [epsilon,2] is entire in z. The remaining part equals

    sum_(m>=0) h_m epsilon^(z+m+3/2)/(z+m+3/2).         (13)

This series converges normally on every compact z set avoiding its displayed
poles. Indeed the Taylor coefficients are bounded geometrically by any
radius between epsilon and the analytic radius, while epsilon^m supplies
strict geometric decay; the denominator grows linearly in m. Formula (13)
therefore extends M meromorphically to the whole plane, with only possible
simple poles at -3/2-m. Its first residue is h_0=H_T(0)>0, so that pole is
genuine. Multiplying by 2^(-z) gives exactly the same pole locations and
orders for E. There is no pole at -1/2.

For g!=1/2 the support of Z is contained in [B,A] with B>0. The integral
E(z)=E[exp(z log(Z/A))] is then entire by dominated convergence on arbitrary
compact complex z sets. It is bounded by one on Re z>=0. For the fair coin
the same bound holds on Re z>=0 directly from 0<=Z/A<=1; there is no atom
at Z=0, and the integral is already holomorphic in the larger half-plane
Re z>-3/2. Both cases thus provide the required zero-type right-half-plane
multiplier without any moving phase or quotient by a possibly vanishing
complex function.

## 5. Linear normalization and sublinear remainder

In both coin cases, E(0)=1 and E(n)>0 at every nonnegative integer. Also
E(n)<=1. The atom U_T=1 has mass Xi(T)>0 and supplies a semicircle density
on [B,A] whose upper-end behavior is a positive constant times
sqrt(A-y). Integrating only over [A-1/n,A] for sufficiently large n gives

    E(n)>=c_(T,g) n^(-3/2).                            (14)

For example (y/A)^n is bounded below by a positive constant on this interval,
and the square-root density has integral comparable to n^(-3/2). Thus

    - (3/2)log n +O(1) <= log E(n) <=0,
    log E(n)=o(n).                                    (15)

This is enough for the scalar resource normalization: the both-zero-arm
mixed endpoint contributes linear rate log A and a sublinear logarithmic
remainder. Positivity, rather than a lower bound of one, is all that the
weighted phase-sign induction requires.

## 6. Scope and exact handoff

For T>0 this completes the phase-free analytic endpoint properties that
were left open in
[MIXED-COMB-SINGLE-ZERO-ARM-ENDPOINT.md](MIXED-COMB-SINGLE-ZERO-ARM-ENDPOINT.md),
Section 5. The all-arity physical moment identity is supplied by the
attributed companion proof, not inferred from finite experiments. At T=0
the normalized comb is identically one and requires no Mellin construction.

A finite product of these normalized endpoint functions is holomorphic of
zero exponential type on the right half-plane, positive at the required
integers, has o(n) logarithm there, and is globally meromorphic with finite
pole orders. Consequently it has exactly the properties needed for a
phase-weight multiplier in the existing sign/Carlson/accumulating-zero
argument. In the fair case its pole at -3/2 is finite order; it cannot hide
an accumulating sequence of distinct off-pole zeros.

This establishes an auxiliary analytic component. It does not by itself
prove the original-source factorization, distinguish general finite core
mixtures, control every compactified source geometry, or establish a finite
legal G4 certificate. The classical Jacobi spectral theory, Doob transform,
semicircle moment identity and Mellin continuation retain their mathematical
attribution. No historical-priority, computational, or Lean claim is made.
