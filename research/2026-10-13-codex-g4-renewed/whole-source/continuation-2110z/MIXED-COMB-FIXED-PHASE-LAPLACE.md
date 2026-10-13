# Fixed-phase Laplace continuation for one strict mixed three-tip comb

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Publisher: Codex lead G4 researcher. **Hand-derived proof; independent review
pending.** No computational or formal verification is asserted.

This packet independently checks the exact formula in
[MIXED-REFERENCE-COMB-GAMMA-DERIVATION.md](MIXED-REFERENCE-COMB-GAMMA-DERIVATION.md)
and develops its analytic continuation for a,b,T>0 and 0<g<1. It concerns
one fixed physical mixed three-tip component. It does not identify general
original-source cores or discard other components of a four-tip mixture.

## Uniform Gamma bound (initial checkpoint, now used below)

Let theta be represented in [-1/2,1/2], u=s-theta, alpha+beta=1, and
1<=j<=l. Define

    W_(u,j,l)(z)=exp[-2H(alpha)z] Gamma(z+1)Gamma(z+2)
      /[Gamma(alpha z+u+2-l)Gamma(alpha z+u+1+l)
        Gamma(beta z-u+1)Gamma(beta z-u+j+1)].

Use the base quotient

    B_theta(z)=exp[-2H(alpha)z] Gamma(z+1)^2
      /[Gamma(alpha z+1-theta)^2 Gamma(beta z+1+theta)^2].

The existing fixed-phase proof gives
|B_theta(z)|<=C(1+|z|)^(-1) on Re z>=0, uniformly in theta. The four
integer shifts relative to the base denominators are

    r=(s+1-l, s+l, -s, j-s),       sum r_i=j+1.

There is also a factor z+1. For gamma in {alpha,beta}, delta in
[1/2,3/2] and integer r, the recurrence formula gives

    |Gamma(gamma z+delta)/Gamma(gamma z+delta+r)|
      <= exp[C |r| log(2+|r|)] (1+|z|)^(-r), Re z>=0.

For r>=0 this follows from
|gamma z+delta+q|>=c_gamma(1+|z|+q); for negative r it is a polynomial
product bounded by [C(1+|r|)(1+|z|)]^|r|. Therefore, with
N=1+|s|+j+l,

    |W_(u,j,l)(z)|
       <= exp[C N log(2+N)] (1+|z|)^(-j-1).            (1)

No large-z/large-shift asymptotic interchange is needed. This resolves the
main proposed half-plane growth gate. Since j>=1, W itself already has
integrable decay on vertical lines, so the mixed inverse can use direct
Bromwich inversion, without the extra integration required for a private
cell's z^(-1/2) transform.

The following sections supply the Gamma kernel, normal convergence,
positive leading coefficient and uniform all-order expansion.

## 1. Independent check of the finite physical formula

The prescribed reference comb has exactly one ranked merger history. If r
mergers occur on the mixed internal edge and k of the n A roots chose its
A arm, the needed route probability is (k)_r/(n)_r. Conditional on the
lineage-count path, the prescribed successive pairs have probability
product_(i=0)^(r-1) lambda_(k+1-i)^(-1). The remaining ordinary completion
contributes kappa_(n+1-r). Thus the factor relative to kappa_(n+1) is

    product_(i=0)^(r-1)
       [(k-i)/(n-i)] [lambda_(n+1-i)/lambda_(k+1-i)]
       = (n+1)_r/(k+1)_r.

This verifies the root's C_(n,k) formula. Absence of A-only mergers on the
two lower arms is necessary for this comb, giving exactly the two stated
arm factors. The pure-death spectral coefficients also agree with the
standard distinct-rate partial fraction formula

    p_(N,j)(T)=product_(r=j+1)^N lambda_r
       * sum_(l=j)^N exp(-lambda_l T)
                         /product_(r=j,r!=l)^N (lambda_r-lambda_l),

after using lambda_r-lambda_l=(r-l)(r+l-1)/2. This checks the cancellation
leading to the Gamma quotient in the root's equation (3). At integer n,
k<0 forces Gamma(k+2-l) to have a pole; k>n forces Gamma(n-k+1) to have a
pole; and l>k+1 again forces Gamma(k+2-l) to have a pole. Reciprocal Gamma
zeros therefore remove all out-of-range terms in the proposed infinite
extension. No limiting physical source has entered this finite identity.

## 2. Exact fixed-phase continuation

Assume a=-log(x0)>0, b=-log(x1)>0, T>0 and 0<g<1. Put

    alpha=b/(a+b), beta=1-alpha, t=(a+b)/2,
    c=ab/[2(a+b)], h=log(g/(1-g))+(a-b)/2,
    ell=2c+2H(alpha)+alpha log(g)+beta log(1-g),
    q_(j,l)=(-1)^(l-j)(2l-1)
                  Gamma(j+l-1)/[Gamma(j)Gamma(l-j+1)].

Define the fixed-phase mixed transform

    F_mix(z,theta)=sum_(s in Z) sum_(l>=1) sum_(j=1)^l
       exp[-t(s-theta)^2+h(s-theta)]
       exp[-lambda_l T] q_(j,l) W_(s-theta,j,l)(z).       (2)

Then for every integer n>=0 the actual reference-comb value satisfies

    v_n/kappa_(n+1)=exp(-c n^2+ell n)F_mix(n,{alpha n}). (3)

This follows from the finite formula just checked and square completion.
In particular F_mix(0,0)=1. Every term except s=0,j=l=1 vanishes there.
All observations in (3) use the same fixed tuple (a,b,T,g).

For 1<=j<=l,

    |q_(j,l)| <= exp[C l log(2+l)].

Together with the uniform half-plane estimate (1), the two strict Gaussian
factors exp(-t(s-theta)^2) and exp(-T l(l-1)/2) dominate all growth. Thus
(2) converges normally on the closed right half-plane and

    |F_mix(z,theta)| <= C(1+|z|)^(-2), Re z>=0,          (4)

uniformly in real theta. The uniform sum follows, for example, by absorbing
C N log(2+N) into arbitrarily small positive multiples of s^2+l^2 outside
a finite set. The sum over j contributes at most another factor l.
Reindexing s proves periodicity in theta.

There is also normal convergence on every compact z set after removing the
common numerator Gamma(z+1)Gamma(z+2). To verify this without spurious
poles from recurrence formulas, fix such a compact set and shift each base
denominator Gamma(gamma z+delta) by a sufficiently large fixed positive
integer so that its real part is uniformly positive on the compact set.
All remaining shifts are integers. The same polynomial/reciprocal-product
estimate is then bounded by exp[C_K N log(2+N)] there. The Gaussian summation
is unchanged. It follows that F_mix is meromorphic on the plane with poles
of order at most two at negative integers and no other possible poles.

The estimates persist for theta in a fixed small complex neighborhood of
any compact real phase interval: Re(1+/-theta) remains positive, its
imaginary part remains bounded, and the recurrence bounds merely change
constants. Thus F_mix is analytic in theta near the real phase torus.
This observation also justifies differentiating the phase coefficients
below. No complex moving phase is substituted into the right-half-plane
bound (4).

## 3. Uniform inverse-Laplace kernel

For u=s-theta, 1<=j<=l, let mu=j+1 and

    nu_(u,j)=(2 pi)^(-1) alpha^(-2u-2) beta^(2u-j-1).

The coefficient is independent of l. Stirling's formula for each fixed
u,j,l gives W_(u,j,l)(z)~nu_(u,j) z^(-mu) on the positive real axis. Define

    S_(u,j,l)(v)
      =[exp(-v)+exp(-2v)]/[1-exp(-v)]
       -[exp(-(u+2-l)v/alpha)+exp(-(u+1+l)v/alpha)]
                                      /[1-exp(-v/alpha)]
       -[exp(-(1-u)v/beta)+exp(-(j+1-u)v/beta)]
                                      /[1-exp(-v/beta)],

    K_(u,j,l)(v)=[S_(u,j,l)(v)-mu]/v.                  (5)

The coefficient of 1/v in S is 2-2alpha-2beta=0. Its constant is
j+1=mu: the numerator shifts 1,2 contribute -2, while the four denominator
shifts contribute -(j+3). Thus K has a removable singularity at zero.

Initially on a sufficiently far right half-plane depending on u,j,l,

    log[W_(u,j,l)(z) z^mu/nu_(u,j)]
          =integral_0^infinity exp(-zv)K_(u,j,l)(v)dv. (6)

As in the private-cell proof, two derivatives verify (6) directly using
the trigamma integral. The second derivative of the logarithm is the
Laplace integral of v[S(v)-mu]=v^2K(v). The resulting affine integration
constants vanish by the fixed-parameter Stirling asymptotic and the
vanishing Laplace integral on the positive axis. Logarithms need only be
chosen on this initial far right half-plane, where all Gamma arguments
have positive real parts.

Fix a sector |arg v|<eta<pi/2 and a finite R. For
N=1+|s|+j+l, uniformly in real theta in [-1/2,1/2],

    |K_(u,j,l)(v)| <= C_R(1+N^2) exp(C_R N |v|),
                         |v|<=R in the sector.        (7)

The same estimate holds on a small full disk about zero, with radius below
the nonzero imaginary poles of the denominators. For a direct proof,
multiply the numerator of K by v and use the analytic functions
v/[1-exp(-v/gamma)]. The resulting expression vanishes to second order at
zero. Taylor's remainder bounds its second derivative by the displayed
right side, since every exponential shift is O(N), and their squares are
O(N^2). All these domains and constants are independent of the integer
summation indices. Complex theta in a sufficiently small fixed strip is
allowed by the same estimate with enlarged constants.

Let b_mu(v)=v^(mu-1)/Gamma(mu), and define the local inverse

    h_(u,j,l)(v)=nu_(u,j) sum_(r>=0)
                           [b_mu*K_(u,j,l)^{*r}](v)/r!.            (8)

Convolution is along the straight segment from zero to v. By the simplex
formula and (7),

    |h_(u,j,l)(v)|
       <= |nu_(u,j)| |v|^j exp(C_R N|v|)
          sum_(r>=0) [C_R(1+N^2)|v|]^r/[r! Gamma(r+j+1)].

Since Gamma(r+j+1)>=(r!) for j>=1, the sum is at most
exp(2 sqrt(C_R(1+N^2)|v|)). Also |nu_(u,j)|<=exp(CN). Consequently

    |h_(u,j,l)(v)/v| <= C_R exp(C_R N), |v|<=R,         (9)

with the value at zero interpreted by analytic continuation. The inequality
|v|^j<=|v|max(1,R)^(j-1) is used here. Each h/v is analytic on a common disk
and throughout the sector; all powers are integers. Its leading term is

    h_(u,j,l)(v)=nu_(u,j) v^j/Gamma(j+1)+O(v^(j+1)).   (10)

For each fixed triple u,j,l, K has exponential order on the positive axis.
The convolution series then gives an exponential-order continuous h, with
Laplace transform W on the initial far right half-plane, by (6). This
individual statement does not assume any uniform summation over shifts.

## 4. Common-line inversion and the actual summed density

Unlike the private-cell transform of order z^(-1/2), W_(u,j,l) already has
integrable vertical-line decay because j>=1. The usual absolutely convergent
Bromwich inversion therefore gives h from W on an initially sufficiently
far right line. Shift that line to any fixed Re z=c0>0. Estimate (1) makes
the horizontal rectangle integrals vanish: for each fixed u,j,l the width
is fixed and the integrand decays at least as |Im z|^(-2). No singularity
lies between the two positive vertical lines. The common-line bound gives

    |h_(u,j,l)(v)| <= C_(c0) exp[C N log(2+N)] exp(c0 v), v>0.     (11)

The constant is uniform over the summation indices and real phase because
integral_R (1+|c0+iy|)^(-j-1)dy is bounded by the same integral with exponent
-2. The contour shift is performed for each individual triple before using
this common uniform bound.

Now sum h with the weights in (2), obtaining h_mix(v,theta). Bound (9)
and the two Gaussians show normal convergence of h_mix/v on the common
disk and on compact subsets of the sector. Bound (11) shows that, for
every c0>0,

    |h_mix(v,theta)| <= C_(c0) exp(c0 v), v>0,          (12)

uniformly in real phase. Thus

    h_mix(v,theta)=v G(v,theta),                       (13)

where G is analytic in v near zero, h_mix is analytic along every positive
v, and both are analytic in real phase with uniform compact bounds.
Dominated convergence in the Laplace integral, choosing c0<Re z, proves

    F_mix(z,theta)=integral_0^infinity
                         exp(-zv)h_mix(v,theta)dv, Re z>0.        (14)

This proves the desired single mixed-component inverse-Laplace class. In
particular, it does not infer convergence of a global Laplace transform
from an inadequate exp(Cv^2) bound after Gaussian summation.

## 5. Positive leading coefficient and all orders

Only j=1 contributes to the coefficient of v in h_mix. Equations (10) and
(13) give

    G(0,theta)= Xi(T)/(2 pi alpha^2 beta^2)
       * sum_(s in Z) exp[-t(s-theta)^2
                    +(h+2 log(beta/alpha))(s-theta)],

    Xi(T)=sum_(l>=1) (-1)^(l-1)(2l-1)exp[-lambda_l T].             (15)

For completeness, Xi(T)>0 for every T>0. In the finite pure-death formula
for p_(M,1)(T), the multiplier of the lth summand in Xi is

    Gamma(M+1)Gamma(M)/[Gamma(M+1-l)Gamma(M+l)]
       =product_(r=1)^(l-1)(M-r)/(M+r),  l<=M.

It lies in [0,1] and tends to one for each fixed l as M->infinity. Gaussian
domination proves p_(M,1)(T)->Xi(T). To bound this limit away from zero,
choose an integer L with 2/L<T/4. Starting from any M>=L, the expected
time to reach L is

    sum_(r=L+1)^M 1/lambda_r <= 2/L.

Markov's inequality gives probability at least 1/2 of reaching L by T/2.
The probability of the finite L-lineage process reaching one within T/2
is a fixed positive number. The strong Markov property therefore gives

    p_(M,1)(T)>=(1/2)p_(L,1)(T/2)>0

uniformly in M>=L. This proves Xi(T)>0 without relying on an unproved
cancellation claim for the alternating spectral series.

The Gaussian theta sum in (15) is strictly positive and has a positive
minimum on the phase circle. Hence G(0,theta)>0 uniformly in real theta.
Watson's elementary Laplace expansion applied to (14), using the common
analytic germ (13), yields for every fixed N

    F_mix(x,theta)=x^(-2) sum_(r=0)^N S_r(theta)x^(-r)
                                  +O(x^(-N-3)), x->+infinity,
    S_r(theta)=Gamma(r+2) [v^r]G(v,theta).               (16)

The error is uniform in real theta: the common disk bounds give a uniform
Taylor remainder near zero, while (12) controls the tail exponentially.
Every S_r is a real analytic periodic function, and S_0 is (15), strictly
positive. Thus the nonzero leading algebraic order is exactly x^(-2), and
the root's proposed ell is the correct linear rate for every fixed T>0.
The constants need not be uniform as T decreases to zero.

## 6. Exactness property and remaining source obligations

Finite products of these fixed mixed transforms have inverse densities
obtained by convolution. If there are K>=1 factors, the density is
v^(2K-1) times an analytic germ, analytic along v>0 and of exponential
order. Therefore a difference of two products with the same total K that
is flat to all inverse powers on the positive real axis must vanish:
Watson's lemma annihilates the analytic germ, analytic continuation
annihilates the whole density, and (14) annihilates the transform. This is
the same rigorous all-orders-to-exact mechanism proved in the private-cell
packet; it applies here to the actual single mixed-source comb transform.
Its use for a phase cross-product gives equal total K automatically.

Private and mixed factors can also be combined in that argument: use the
once-integrated private inverse, divide the entire transform by z for
each private factor, and convolve with the direct mixed inverses. The
fractional power of the resulting density is determined by adding 3/2 for
each integrated private factor and 2 for each mixed factor. This describes
analytic compatibility only; an exact source factorization premise must
still be supplied before it implies a persistence theorem.

**Proved analytic component:** the actual strict mixed three-tip reference
comb has a fixed-phase continuation (2), meromorphic with controlled poles,
a uniform right-half-plane bound, a genuine analytic inverse-Laplace
density, and a uniform full asymptotic expansion with positive leading
coefficient. The exact integer relation is (3), with one shared physical
tuple throughout.

**Not proved here:** a general four-tip mixture decomposition into one
common rate, separation of multiple quadratic or linear rates, source
compactification at T=0 or zero arm length, the original-core legal decoder,
or full G4 finite forcing. Terms with smaller quadratic rates are retained
by the original finite formula and are never discarded here. No boundary
parameter, unknown-size restriction, or latent observation is admitted.

This uses classical pure-death spectral coefficients, Gamma recurrence and
Stirling estimates, Laplace inversion/convolution, and Watson's lemma.
Novelty is not claimed for those tools. It is a hand proof intended for
independent audit, not a finite numerical screen or machine-verified proof.
