# Uniform inverse-Laplace phase removal for finite Gamma–Gaussian products

Contributor: Codex delegated laplace_recovery researcher, 13 October 2026.
Publisher: Codex lead G4 researcher. **Hand-derived proof; independent
review pending.** This packet rederives a proposed bridge recovered from
the lead researcher's checkpoint. No numerical or formal verification is
asserted, and no historical-priority claim is made.

This replaces the conditional phase-removal paragraph of
[the fixed-phase handoff](FIXED-PHASE-GAMMA-HANDOFF.md) with a class-specific
uniqueness argument. It uses the reviewed fixed-phase bounds and all-order
phase constraints; it does not infer exactness from a formal expansion alone.
Its consequence is unrestricted real-balance finite persistence under an
**exact scalar factorization premise**. A legal original-source observation
bridge, general INDEPENDENT forcing, and the G4 master remain separate.

## 1. Statement and inherited inputs

For a strict cell let a,b>0, 0<g<1, and put

    t=(a+b)/2, alpha=b/(a+b), beta=1-alpha,
    h=log(g/(1-g))+(a-b)/2,
    H(alpha)=-alpha log(alpha)-beta log(beta),
    W_u(z)=exp[-H(alpha)z] Gamma(z+1)
                  /[Gamma(alpha z+1+u)Gamma(beta z+1-u)],
    F(z,theta)=sum_(s in Z) exp[-t(s-theta)^2+h(s-theta)] W_(s-theta)(z).

Real phases are taken modulo one. The reviewed supplier proves:

1. F is bounded holomorphic on Re z>=0, meromorphic on the plane with
   possible simple poles at negative integers, and F(0,0)=1.
2. At integer n, d_n(a,b,g)=exp[-c n^2+ell n]F(n,{alpha n}), with the
   supplier's explicit c,ell.
3. Uniformly for theta in [-1/2,1/2], writing u=s-theta,

       |W_u(z)| <= C M^|s| (1+|z|)^(-1/2),  Re z>=0,       (1)

   where C,M depend on alpha and beta, not s,theta,z. The supplier states
   boundedness; retaining its central Stirling decay gives exactly (1).
4. Each F has a uniform full positive-real-axis expansion
   x^(-1/2) sum_(j>=0) S_j(theta)x^(-j), with S_0(theta)>0.

Let A(z,theta) and B(z,theta) be products of k_T and k_R such factors,
respectively; the vector theta contains all their phases. Empty products
are one. Let H_0 be a closed subset of the phase torus containing zero.

**Phase-removal theorem.** Suppose the full asymptotic expansion of

    x^((k_T-k_R)/2) A(x,theta)/B(x,theta)

has the same coefficients for every theta in H_0. Then, for every such theta,

    A(z,theta)B(z,0)=A(z,0)B(z,theta).                    (2)

The identity holds on Re z>0 and hence meromorphically on the plane.
No rationality, independence, or nonresonance assumption on the alphas is
made. The quotient in this premise is used only for sufficiently large real
x, where its denominator has a positive leading term.

**Finite-persistence consequence.** In the exact law-level scalar identity
of [resource normalization](UNEQUAL-RESOURCE-NORMALIZATION.md), the countable
strict equal-arm family is finite, for arbitrary real arm balances in both
finite lists. Finitely many zero-arm *auxiliary limit* factors can also be
included in those lists, as proved in Section 7. This inclusion does not
admit boundary parameters as physical rivals.

The all-order hypothesis for the strict scalar identity is supplied by
[all-order phase rigidity](ALL-ORDER-UNEQUAL-PHASE-CONSTRAINT.md), with H_0
its full cyclic orbit closure, including all resonances.

## 2. A uniform local logarithmic inverse

Fix alpha,beta in (0,1) with alpha+beta=1 and real u. Define

    nu_u=(2 pi alpha beta)^(-1/2)(beta/alpha)^u,

    K_u(v)={1/(exp(v)-1)
            -exp(-u v/alpha)/(exp(v/alpha)-1)
            -exp(u v/beta)/(exp(v/beta)-1)-1/2}/v.       (3)

The apparent singularity at zero is removable. Expanding each denominator
shows cancellation of the coefficient 1/v and of the constant in the
numerator of (3); the value of the continuation is

    K_u(0)=(1-1/(alpha beta))/12
              -[u^2+(1-2alpha)u]/(2 alpha beta).       (4)

This agrees with the inherited first Stirling polynomial q_1(u).

For each fixed u, on a sufficiently far right half-plane, with the branch
of the logarithm real for sufficiently large positive z,

    log[W_u(z) z^(1/2)/nu_u] = integral_0^infinity exp(-zv)K_u(v) dv.
                                                               (5)

Here is a direct verification that avoids an unproved uniform asymptotic
identity. The trigamma integral, after changing variables in the two scaled
terms, gives

    (log W_u)''(z)
       = integral_0^infinity v exp(-zv)
           [1/(exp(v)-1)
            -exp(-u v/alpha)/(exp(v/alpha)-1)
            -exp(u v/beta)/(exp(v/beta)-1)] dv.

Adding (1/2)log z to log W_u subtracts 1/(2z^2) from this second derivative,
which gives exactly the second derivative of the right side of (5). The
two sides therefore differ by an affine function of z. Stirling's formula
for fixed u gives W_u(z)~nu_u z^(-1/2) on the positive real axis; the Laplace
integral tends to zero there. Their affine difference is thus zero. All
integrals in this paragraph converge absolutely once Re z is sufficiently
large depending on u. Analytic continuation gives (5) throughout that far
right half-plane.

Uniformity over unbounded u is needed only on compact v domains. Choose a
fixed sector |arg v|<eta<pi/2, adjoin zero with its removable continuation,
and truncate it by |v|<=R. For every R<infinity there are C_R,c_R such that

    |K_u(v)| <= C_R(1+u^2) exp(c_R |u| |v|).             (6)

All constants are independent of real u. One verification is to multiply
the numerator of (3) by v and use the analytic functions
v/(exp(v/c)-1), c in {1,alpha,beta}. Their only nonzero poles are imaginary,
so they and their first two derivatives are uniformly bounded on any
slightly enlarged truncated sector. The resulting numerator vanishes to
second order at zero. Taylor's integral remainder along the segment from
0 to v bounds its second derivative by
C_R(1+u^2)exp(c_R|u||v|), proving (6). The same argument gives (6) on a small
full disk around zero, with radius chosen below all nonzero imaginary poles.
Both neighborhoods are independent of u.

## 3. An analytic local inverse with only exponential shift growth

For rho>0 write b_rho(v)=v^(rho-1)/Gamma(rho), using the branch positive on
the positive axis. Convolution means the Volterra convolution along the
straight segment from 0 to v; K_u^{*0} is the convolution identity. Set

    h_u(v)=nu_u sum_(r>=0) [b_(1/2)*K_u^{*r}](v)/r!,
    J_u(v)=integral_0^v h_u(w)dw
          =nu_u sum_(r>=0) [b_(3/2)*K_u^{*r}](v)/r!.     (7)

These sums converge normally on compact subsets of the sector and after
removing the displayed fractional power at zero. Indeed, (6), the simplex
integral for convolution, and |w_1|+...+|w_r|<=|v| on a straight segment give

    |[b_(1/2)*K_u^{*r}](v)|
      <= exp(c_R|u||v|) [C_R(1+u^2)]^r
                  |v|^(r-1/2)/Gamma(r+1/2).

Consequently, for |v|<=R in the sector,

    |v^(1/2)h_u(v)|
      <= |nu_u| exp(c_R|u||v|)
          sum_(r>=0) [C_R(1+u^2)|v|]^r/[r! Gamma(r+1/2)]
      = |nu_u| exp(c_R|u||v|)
          cosh(2 sqrt(C_R(1+u^2)|v|))/sqrt(pi)
      <= C'_R exp(c'_R |u|).                            (8)

The equality is the elementary Gamma half-integer identity, used with the
nonnegative scalar majorant. Integrating gives the analogous bound

    |v^(-1/2)J_u(v)| <= C''_R exp(c''_R |u|).            (9)

Thus h_u(v)=v^(-1/2) times an analytic germ and J_u(v)=v^(1/2) times an
analytic germ at zero, on a common disk independent of u. They are
holomorphic with the specified branch throughout the sector. In particular
J_u is real analytic at every positive v.

For fixed u, K_u on the positive axis is bounded by C_u exp(a_u v). The
same convolution estimate, now global on that axis with these u-dependent
constants, gives exponential order for h_u and J_u. Laplace-transforming
(7) on a sufficiently far right half-plane is justified absolutely and
sums the exponential series in (5). Therefore

    Laplace(h_u)(z)=W_u(z),
    Laplace(J_u)(z)=W_u(z)/z.                            (10)

A crude attempt to sum this u-dependent global exponential bound directly
against the Gaussian can give an exp(Cv^2) bound. That bound is insufficient
for an ordinary Laplace transform. The next step obtains a different,
uniform global bound; no global summation using the crude bound is used.

## 4. Integrated Bromwich inversion on one common vertical line

Fix c>0. For each u=s-theta, inversion of (10) initially takes place on a
line Re z=sigma_u sufficiently far to the right:

    J_u(v)=(1/(2 pi i)) integral_(sigma_u-i infinity)^(sigma_u+i infinity)
                      exp(zv) W_u(z)/z dz,   v>0.      (11)

This integral is absolutely convergent by (1), since W_u(z)/z decays like
|Im z|^(-3/2). The usual Fourier/Laplace inversion theorem applies to the
continuous exponential-order function J_u. Alternatively, the absolute
integral is its continuous inverse under the standard Fourier inversion
uniqueness theorem.

There are no poles between the lines Re z=sigma_u and Re z=c. For each
fixed u, the horizontal integrals on rectangles of heights +/-T tend to
zero by (1): their length sigma_u-c is fixed, their exponential factor is
bounded by exp(max(sigma_u,c)v), and their remaining factor is O_u(T^(-3/2)).
We may therefore replace sigma_u by c in (11). Taking absolute values on
this common line gives

    |J_(s-theta)(v)| <= C_c M^|s| exp(cv),  v>0,         (12)

uniformly for theta in [-1/2,1/2]. The constant C_c is finite because

    integral_R (1+|c+iy|)^(-1/2)/|c+iy| dy < infinity.

This is the essential global estimate: it follows from a contour shift for
each u followed by the common-line bound, not from interchanging the
u-dependent original inversion lines.

For the strict cell define

    J_theta(v)=sum_(s in Z) exp[-t(s-theta)^2+h(s-theta)] J_(s-theta)(v).
                                                               (13)

The local bounds (9) prove normal convergence on the common disk and on
compact sector subsets. Hence

    J_theta(v)=v^(1/2) H_theta(v),                      (14)

where H_theta is analytic near zero, and J_theta is holomorphic throughout
the sector. Bound (12) proves, for every c>0,

    |J_theta(v)| <= C_(c,t,h,alpha) exp(cv),  v>0,       (15)

uniformly in real phase. Dominated convergence in the Laplace integral,
using any c<Re z, now gives the exact identity

    Laplace(J_theta)(z)=F(z,theta)/z,  Re z>0.          (16)

This proves both local analytic summability and a legitimate global Laplace
transform after summation. Neither follows from a fixed-shift inverse-Mellin
theorem alone.

## 5. Flatness determines the finite product exactly

Let K=k_T+k_R. If K=0, equation (2) is immediate. Assume K>=1. Apply (16)
to the K factors in A(z,theta)B(z,0), and convolve their J functions. Call
the convolution L_theta. Standard absolutely convergent Laplace convolution
on Re z>0 gives

    Laplace(L_theta)(z)=A(z,theta)B(z,0)/z^K.           (17)

Every J factor has the form (14). A beta-simplex integral therefore gives

    L_theta(v)=v^(3K/2-1) G_theta(v)                    (18)

near zero, where G_theta is analytic on a common disk. To see analyticity
directly, substitute w_i=v r_i in the convolution simplex: the product of
r_i^(1/2) is integrable on the fixed simplex, while the analytic factors
H_i(vr_i) admit uniformly convergent power series there. The same segment
integrals show that L_theta is holomorphic on the sector away from zero;
its fractional power has the fixed branch there. Bound (15) gives

    |L_theta(v)| <= C_c^K exp(cv) v^(K-1)/(K-1)!,       (19)

with constants enlarged to cover the finitely many different cells.

Apply the same construction with theta interchanged with zero between A
and B, obtaining L'_theta. Their difference L has form
v^(rho-1)G(v), rho=3K/2>0, with G analytic near zero, is real analytic for
v>0, and has exponential order. Its Laplace transform is

    [A(z,theta)B(z,0)-A(z,0)B(z,theta)]/z^K.           (20)

By the phase-removal theorem's hypothesis and the inherited full fixed-phase
expansions, the numerator in (20) is O(x^(-N)) for every N as real
x->+infinity. Explicitly, the normalized ratio A/B has identical formal
coefficients at theta and zero, and multiplication by the two denominator
expansions proves this statement without any analytic division off the
large positive real axis.

Watson's elementary Laplace lemma now forces every Taylor coefficient of
G to vanish. For completeness, if G(v)=sum_(j=0)^N g_j v^j+O(v^(N+1))
on [0,r], splitting its Laplace integral at r and using (19) gives

    Laplace(L)(x)=sum_(j=0)^N g_j Gamma(rho+j)x^(-rho-j)
                           +O(x^(-rho-N-1)).           (21)

The omitted tail is exponentially small; each monomial can be extended
from [0,r] to [0,infinity) at exponentially small cost. A first nonzero
Taylor coefficient would contradict flatness. Hence G is zero on its disk
of analyticity, so L is zero on an interval (0,r). Real-analytic
continuation along the positive axis, or the identity theorem on the
connected sector, gives L identically zero there. Its Laplace transform
is zero, proving (2) on Re z>0. Meromorphic continuation proves the stated
global identity.

The analyticity of this particular inverse density is indispensable. For
example exp(-z) has an inverse supported at v=1 and lacks the analytic
continuation property used here. Thus this argument does not assert the
false general rule that all-order flat holomorphic functions vanish.

## 6. Exact arbitrary-balance finite persistence

Start with the exact strict scalar identity in resource normalization.
Its reviewed proof first establishes sum_i h_i^2<infinity and matches the
quadratic and linear exponential normalizations; it needs no rationality.
Write P(z)=product_i U(z;t_i,h_i) for the countable equal-arm product.
At every nonnegative integer m the normalized scalar identity is

    A(2m,theta_m)=B(2m,theta_m) P(m),
    theta_m=m omega modulo 1,
    omega=2 times the vector of all finite-cell alphas.             (22)

The inherited all-order phase theorem says that the expansion of the
normalized A/B is constant on H_0=closure{m omega:m>=0}. This compact cyclic
orbit closure contains zero. Section 5 gives equation (2) on H_0. Multiply
(22) by B(2m,0) and use (2); cancellation of B(2m,theta_m) is legitimate
because this is the positive normalized physical diagonal product. Thus

    P(m) B(2m,0)=A(2m,0),  m=0,1,2,... .              (23)

The established zero-exponential-type Carlson theorem for P, together with
the bounded fixed-phase products, makes the difference

    P(z) B(2z,0)-A(2z,0)

holomorphic of zero exponential type on the right half-plane. Its integer
zeros force it to vanish. This is exactly the previously reviewed Carlson
step, now applied to a genuinely phase-independent identity. No substitution
of a complex moving phase into the fixed-phase bounds is made.

If infinitely many strict equal factors persisted, the inherited
meromorphic-zero theorem would provide distinct off-pole zeros z_j of P,
accumulating at -1/2 or -3/2. The identity extends to the connected plane
minus the negative half-integer pole set, so A(2z_j,0)=0. A(2z,0) is a finite
product with at worst a finite-order pole at the accumulation point.
Multiplying by a sufficient power of z-z_* therefore gives a holomorphic
function with accumulating zeros, hence the zero function. This contradicts
A(0,0)=1. The countable family is finite.

## 7. Finite zero-arm auxiliary factors

This extension is useful for compactification; it does not relax the
strict positivity of any admitted source or rival. The already reviewed
[endpoint formula](ZERO-ARM-ENDPOINT-SOL-AUDIT.md) says that for a=0,b>0,

    d_n(0,b,g)=g^n E(n),
    E(z)=sum_(r>=0) binom(z,r)((1-g)/g)^r exp[-b r(r-1)/2].          (24)

Here E is entire of zero exponential type, E(0)=1, E(n)>0 at nonnegative
integers, and log E(n)=O(log^2(2+n))=o(n). The opposite endpoint exchanges
arms and g with 1-g. A cell with both arms zero is the identity. Group all
such finite endpoint factors on each side as E_T,E_R and absorb their
linear exponential prefactors into the resource bookkeeping.

The resource proof still applies: its remainder O(log n) is replaced by
o(n), which changes neither quadratic dominated convergence nor the
nonnegative Fatou and linear dominated-convergence steps. Thus P has the
same established resource and zero-type properties. Its normalized exact
identity becomes

    E_T(2m) A(2m,theta_m)
      =E_R(2m) B(2m,theta_m) P(m).                     (25)

We must reestablish the all-order phase conclusion without falsely expanding
the endpoint factors in inverse powers. Let kappa=(k_T-k_R)/2 and write the
strict-factor ratio expansion, uniformly in phase, as

    (2m)^kappa A(2m,theta_m)/B(2m,theta_m)
       =sum_(j=0)^N A_j(theta_m)m^(-j)+O(m^(-N-1)).     (26)

Set f(z)=(2z)^kappa P(z)E_R(2z), on a shifted right half-plane if necessary.
Equation (25) says that f(m) is E_T(2m) times (26). The all-order proof's
sign/zero-density induction works with the positive integer factor E_T
retained. Specifically, after A_0,...,A_(j-1) have been proved constant,
consider for real c

    z^j [f(z)-E_T(2z)sum_(r<j)c_r z^(-r)]-c E_T(2z).  (27)

This is real on the positive axis, holomorphic of zero exponential type
on the shifted half-plane. At integers its sign is the sign of
A_j(theta_m)-c+O(1/m), because E_T(2m)>0. If A_j were nonconstant on H_0,
choose c strictly between two attained values. Relatively dense returns to
two open phase sets of opposite sign give positive-density real zeros of
(27), contradicting the inherited zero-density lemma unless (27) is
identically zero. In that exceptional case its integer equality and dense
recurrent phase orbit force A_j=c on H_0 directly, again a contradiction.
Every A_j is therefore constant. No division by E_T is made on a complex
domain, and no bound on its reciprocal is assumed.

Sections 2–5 now apply to the strict factors unchanged. Using their exact
phase removal in (25) and cancelling the positive physical B factor gives

    P(m)E_R(2m)B(2m,0)=E_T(2m)A(2m,0).                 (28)

All finite multipliers in (28) are zero type on the right half-plane and
meromorphic with finite-order singularities on the plane. Carlson and the
same accumulating-zero argument prove finite persistence. The right side
is nonzero because its value at zero is one.

## 8. Scope, attribution, and review handoff

**Discharged implication:** an exact scalar diagonal factorization into
finitely many arbitrary real-balance strict or auxiliary endpoint factors
and a summable countable strict equal-arm family cannot contain infinitely
many equal factors. The new ingredient is the uniform Gaussian-summed
inverse-Laplace class and the resulting all-orders-to-exact phase removal.

**Not discharged here:** obtaining that exact scalar identity from every
admitted original reticulate target and finitely many legal observations;
removing independent weak-clock reservoirs using INDEPENDENT observations
alone; constructing an admitted fixed-target impossibility witness. No
rival-size bound, latent motif observation, new parameter menu, or extra
physical source is assumed in this analytic argument.

The fixed-phase interpolation, resource normalization, all-order
zero-density constraint, equal-family Carlson theorem, and off-pole-zero
theorem are inherited and retain their attributed suppliers. The Gamma
integral, Stirling estimates, convolution theorem, Laplace inversion and
Watson argument are classical. The related Karp–Prilepkina Gamma-ratio
inverse-factorial and delta-neutral H-function papers linked in the prior
handoff concern fixed quotients; this proof does not invoke an unverified
uniform-in-shift version of those results. Historical novelty remains
unassessed. This is a hand proof, not a numerical experiment or Lean proof.

Independent review should especially check: the removable kernel constant;
the linear-in-|u| convolution majorant; the common-line Bromwich bound;
analytic continuation of the finite-product density; and the retained
positive endpoint factor in the phase sign argument. A root-level
composition into any finite legal certificate must separately verify every
source and compactification premise.
