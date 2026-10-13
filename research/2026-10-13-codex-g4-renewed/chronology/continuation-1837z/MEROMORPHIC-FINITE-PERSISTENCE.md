# Finite persistence from the exact diagonal: meromorphic zeros

Author: Codex lead G4 researcher, with contour and audit contributions from
the chronology and critical-review agents. 2026-10-13, 18:52 UTC.

Status at submission: **hand proof candidate awaiting independent review**.
No numerical test, formal verification, or full original G4 closure is claimed.
The companion Carlson bridge has a separate independent hand review.

## The analytic statement

Let a finite target have strict cells (T_l,H_l), T_l>0, H_l real.
Let a finite or countable family have strict cells (t_i,h_i) with

    sum_i t_i < infinity,    sum_i h_i^2 < infinity.

For every nonnegative integer m suppose

    product_l U(m;T_l,H_l) = product_i U(m;t_i,h_i),       (1)

where U(m;t,h)=E[exp(-t S^2) cosh(hS)] and S=Bin(2m,1/2)-m.
Then the countable family is finite.

This concerns an auxiliary representation of the existing legal response
law, not observations of its complex continuation. In the source application,
the exact diagonal/resource identities in dot's
[negative-reservoir diagnostic](../../../2026-10-10-dot-g4-negative-reservoir-diagnostic-1137z/EXACT-NEGATIVE-RESERVOIR-GATE.md),
equations (2)–(4), give precisely these hypotheses. In particular the weak
clock deficit has already canceled, and sum log cosh(h_i/2)<infinity
implies sum h_i^2<infinity. No finite energy sum h_i^2/t_i is imposed.

## 1. A meromorphic single-cell function

Set

    K_t(w) = (4 pi t)^(-1/2) sum_{k in Z} exp(-(w+2 pi k)^2/(4t)),
    H_{t,h}(theta) = [K_t(theta+ih)+K_t(theta-ih)]/2.

This is an entire even periodic function of theta, also even around pi.
Its Fourier series is

    H_{t,h}(theta) = (2 pi)^(-1)
        sum_{k in Z} exp(-t k^2) cosh(hk) exp(ik theta).

For Re z>-1/2, the companion bridge's function is equivalently

    U(z;t,h) = integral_{-pi}^{pi} cos(theta/2)^(2z) H_{t,h}(theta) dtheta
             = integral_0^1 x^(z-1/2) a_{t,h}(x) dx,
    a_{t,h}(x) = 2 (1-x)^(-1/2) H_{t,h}(2 arccos(sqrt x)).       (2)

Evenness about pi makes a analytic near x=0: although the angle has a
square-root branch there, the composition is even in that square root.
At x=1 the sole integrable square-root factor causes no z singularity.
Subtracting any finite Taylor polynomial of a at zero therefore continues
U meromorphically to the whole plane. Its only possible poles are simple
poles at

    P = {-1/2, -3/2, -5/2, ...},

with residue at -j-1/2 equal to the coefficient of x^j in a. Also
U(0;t,h)=1 exactly.

## 2. Uniform small-cell estimate off the pole lattice

For every compact C in the complex plane minus P there are constants
A_C,delta_C>0 such that

    sup_{z in C} |U(z;t,h)-1| <= A_C(t+h^2)              (3)

whenever 0<t<delta_C and |h|<delta_C.

Here are details including negative real parts of z. Fix r=pi/2 and
a=cos^2(r/2)=1/2. Split the theta integral into the central interval
[-r,r] and its complement. By reflection symmetry H may be replaced by
K_t(theta+ih) on each of these symmetric domains. Shift only the central
contour, writing w=theta+ih; this produces the real central integral

    integral_{-r}^r K_t(theta) cos((theta-ih)/2)^(2z) dtheta

and two vertical segments at real part +r and -r. The cosine has no
zeros in this smaller rectangle for small h. Thus its logarithm and powers
are holomorphic and uniformly bounded for z in C. On this real interval,
uniformly for z in C and small h,

    cos((theta-ih)/2)^(2z) = 1 + O_C(theta^2+h^2).

Integration against the periodic Gaussian gives 1+O_C(t+h^2):
its missing central mass is exponentially small and its central second
moment is bounded by the unwrapped Gaussian second moment 2t.
The two vertical segments contribute O_C(t^(-1/2) exp(-c/t)) for a
fixed c>0; periodic Gaussian images satisfy the same bound. This reasoning
holds for any bounded set of z, including negative real parts.

It remains to justify the complementary integral after continuation. In
the x coordinate it is exactly

    integral_0^a x^(z-1/2) a_{t,h}(x) dx.               (4)

On a fixed complex neighborhood of [0,a], the analytic function
a_{t,h} and every fixed finite number of its derivatives are bounded by

    C_N t^(-1/2) exp(-c_N/t),                          (5)

uniformly for sufficiently small |h|. To see this without an energy
assumption, choose the neighborhood so that either local branch of
theta=2 arccos sqrt x has real part between r/2 and 2pi-r/2, and
imaginary part of magnitude at most r/8. This is possible also at x=0
because both branches are near pi; evenness removes their branching in
the composed function. Require |h|<=r/8. Each Gaussian image then has
real distance at least r/2 from its nearest center and imaginary part
at most r/4. Its modulus is exponentially small in 1/t. The remaining
images are summable with the same estimate. The factor (1-x)^(-1/2)
is analytic and bounded on this neighborhood. Cauchy's estimates on a
slightly smaller fixed neighborhood prove the stated derivative bounds.

Choose an integer M>=1 with Re z+M>-1/2 for every z in C. Write
a_{t,h}(x)=sum_{j=0}^{M-1} a_j x^j+x^M R_M(x). The continuation of (4) is

    sum_{j=0}^{M-1} a_j a^(z+j+1/2)/(z+j+1/2)
       + integral_0^a x^(z+M-1/2) R_M(x) dx.            (6)

For z in C its denominators stay away from zero. Bound (5), including
the Taylor remainder, makes (6) uniformly O_C(t^(-1/2)exp(-c/t)), hence
O_C(t). Combining central and complementary pieces proves (3).
Here Taylor's integral remainder on the real segment suffices; a Taylor
series is not asserted to converge all the way to a.

Consequently, under the summable budgets, product_i U(z;t_i,h_i)
converges normally on the connected domain D=(complex plane) minus P.
It is holomorphic there and equals 1 at zero. This product agrees on the
right half-plane with the product in the Carlson bridge. Zeros of any
finite factor at a point of D remain zeros of the limiting product,
since all other factors are holomorphic there and the remaining product
converges locally.

## 3. Every strict cell has a pole at -1/2 or -3/2

Write f_t(h)=2pi H_{t,h}(pi). The Jacobi theta product gives

    f_t(h) = product_{m>=1} (1-exp(-2mt))
             (1-exp(h-(2m-1)t))(1-exp(-h-(2m-1)t)).     (7)

For real h and strict t, its zeros are exactly h=s t for odd integers s;
each such zero is simple as a zero in h. All other factors in (7) are
nonzero at that point, and their tail product is nonzero. This is the
classical theta4 product, not a new identity; see
[NIST DLMF 20.5.4](https://dlmf.nist.gov/20.5.E4).

If f_t(h) != 0, (2) has a_0=2H(pi) !=0, so U has a genuine simple
pole at -1/2.

Otherwise h=st. Along the exact zero curve, differentiation gives

    partial_t H(pi;t,st) + s partial_h H(pi;t,st) = 0.

The second term is nonzero since s is a nonzero odd integer and the zero
in h is simple. The Fourier series gives the heat equation
partial_t H = partial_theta^2 H. Therefore H''(pi) !=0 at this
exception. In (2), theta=pi-2 arcsin sqrt x, so

    H(theta) = 2 H''(pi) x + O(x^2),
    a(x) = 4 H''(pi) x + O(x^2).

Thus U has a genuine simple pole at -3/2 in this case, while its
possible pole at -1/2 is removable.

## 4. Integer equality rules out infinitely many cells

By the independently reviewed
[Carlson bridge](CARLSON-CONTINUATION-BRIDGE.md), (1) implies equality of
the target and countable products throughout Re z>0. By (3) both
products are holomorphic on connected D, so the identity theorem extends
their equality throughout D.

Assume infinitely many strict cells. By Section 3, infinitely many of
their functions have a genuine simple pole at one same point
p in {-1/2,-3/2}. Pass to that subsequence. Pick any small radius rho
so the closed disk about p contains no other point of P. By (3), these
cell functions tend uniformly to 1 on its boundary. For all sufficiently
late cells,

    |(z-p)U_i(z)-(z-p)| < |z-p|  on |z-p|=rho.

The function (z-p)U_i(z) is holomorphic throughout the disk. Rouché's
theorem says it has exactly one zero there. Its value at p is the nonzero
residue, so this zero zeta_i is different from p and is a zero of U_i
in D. Uniform convergence to 1 on every compact set away from p shows
these zeros tend to p (equivalently apply the same argument with arbitrary
smaller radii). They include infinitely many distinct points.

Normal convergence propagates every such zero to the countable product,
and hence to the finite target product. But a finite product is
meromorphic at p and nonidentically zero, since its value at zero is 1.
Multiplying it by a sufficiently large fixed power of z-p produces a
holomorphic nonzero function near p. Infinitely many zeros accumulating
at p contradict the identity theorem. This proves finite persistence.

## 5. Precisely what this would discharge

After independent acceptance, this supplies the missing finite-persistence
premise of the reviewed
[mixed-target global implication](../../general-algebra/FINITE-PERSISTENCE-AND-GLOBAL-GATE.md).
It handles arbitrary order/accumulation of persistent cells and arbitrary
fair/biased mixtures without selecting a first cell, an energy bound,
latent motif observations, or a preset rival-size bound.

Together with that implication, it would give existential finite legal
cap forcing for **every finite strict calibrated equal-arm private BOTH
target** against all strict finite private rivals in that same class.
The complex zeros are proof tools; the certificate consists of the
original legal finite-cap observations. This does not provide a numerical
cap bound, an observation-only stopping algorithm, a changing-exterior
transfer, an INDEPENDENT-only local theorem, or all-original-source G4.
The master task must retain those distinct obligations.

Classical tools: Gaussian/Fourier heat kernel, Mellin continuation,
Jacobi product, Carlson uniqueness, Rouché and identity theorem. The
claimed research contribution is their application with the summable
source budgets and the off-pole estimate (3), not novelty of those tools.

