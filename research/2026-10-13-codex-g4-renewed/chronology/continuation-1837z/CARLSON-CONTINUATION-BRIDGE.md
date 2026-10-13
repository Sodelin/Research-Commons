# Exact even-arity continuation under finite clock and bias budgets

Author: Codex chronology subagent; contour strategy developed in exchange with
the Codex lead G4 researcher. Date: 2026-10-13, continuation 1837z.

Status: hand-derived argument, submitted for independent review. No numerical
screen or Lean verification is claimed. This is an analytic bridge for the
existing calibrated equal-arm paired diagonal identity. It is not a new legal
observation menu or a closure claim for the original G4 master question.

## Statement

For a strict cell with clock `t>0` and log odds `h`, define, initially for
`Re z > -1/2`,

\[
 U(z;t,h)=\int_{-\pi}^{\pi}K_t(\theta+ih)
               |\cos(\theta/2)|^{2z}\,d\theta,
 \qquad
 K_t(w)=\frac1{\sqrt{4\pi t}}\sum_{k\in\mathbb Z}
                 e^{-(w+2\pi k)^2/(4t)}.                 \tag{1}
\]

The complex power in the real integral uses the real logarithm of the
nonnegative base. Endpoints are understood by integration. At nonnegative
integers `m`, Fourier expansion gives exactly

\[
 U(m;t,h)=\mathbb E_{S=\mathrm{Bin}(2m,1/2)-m}
                      [e^{-tS^2}\cosh(hS)].              \tag{2}
\]

Suppose a finite or countable cell family satisfies

\[
 \sum_i t_i<\infty,\qquad \sum_i h_i^2<\infty.           \tag{3}
\]

Then its product `P(z)=prod_i U(z;t_i,h_i)` converges locally uniformly on
`Re z>=0`, is holomorphic on the open right half-plane and continuous on its
boundary, and has **zero exponential type** there: for every `epsilon>0`,

\[
 |P(z)|\le C_\epsilon e^{\epsilon |z|}\qquad(\Re z\ge0). \tag{4}
\]

Consequently equality of two such products at every nonnegative integer
implies equality throughout the right half-plane. This follows from Carlson's
theorem, with every growth hypothesis verified below. No bound on
`sum h_i^2/t_i` is needed.

The inherited finite-target resource identity gives `sum t_i<infinity` and
`sum log cosh(h_i/2)<infinity`. The latter implies (3): `h_i->0`, and
`log cosh(h/2)` is bounded below by a positive constant times `h^2` near zero;
only finitely many other terms remain. Thus this analytic statement applies
to the countable carriers in that identity.

## A single-cell growth bound

For all `0<t<=1`, `|h|<=1`, and `Re z>=0`,

\[
 \boxed{|U(z;t,h)|\le\exp(3h^2|z|+8t).}                 \tag{5}
\]

Write `z=x+iy`, `Y=|y|`. The function is even in `h`, so take `0<=h<=1`.
First, directly from (1),

\[
 |U(z;t,h)|\le e^{h^2/(4t)}.                            \tag{6}
\]

Indeed the modulus of the power on the real contour is at most one, and
`|K_t(theta+ih)|<=e^{h^2/(4t)}K_t(theta)`.
If `Y>=pi/(32t)`, (6) is at most `exp((8/pi)h^2 Y)`, which proves (5) in
that regime.

Now assume `Y<=pi/(32t)`. Substitute `w=theta+ih` and shift the contour
to `Im w=0`. Inside the rectangle use the holomorphic branch

\[
 F_z(w)=\cos((w-ih)/2)^{2z},
\]

whose logarithm has argument between `-pi/2` and `pi/2`. The only zeros of
the cosine in the closed rectangle are its upper corners. Small corner
indentations vanish for `x>=0`; their absolute contributions are bounded by
a constant times their radii. Thus the shifted main integral is

\[
 M=\int_{-\pi}^{\pi}K_t(\theta)
                       \cos((\theta-ih)/2)^{2z}\,d\theta, \tag{7}
\]

plus the two vertical edge integrals.

Put `r(theta)=|cos((theta-ih)/2)|` and let `a(theta)` denote its argument.
The functions `r` and `K_t` are even and `a` is odd. Also

\[
 r(\theta)^{2x}\le e^{xh^2/4},\qquad
 |a(\theta)|\le h|\theta|/2\quad (|\theta|\le\pi/2),
 \qquad |a(\theta)|\le\pi/2.                            \tag{8}
\]

The first inequality follows from `r^2=cos^2(theta/2)+sinh^2(h/2)` and
`cosh(h/2)<=exp(h^2/8)`. For the second, use
`|a|=arctan(tanh(h/2)|tan(theta/2)|)` and
`|tan(theta/2)|<=|theta|` on that interval.

Pair `theta` with `-theta` before taking absolute values. The factor from
the argument is then bounded by `cosh(2Y a(theta))`; there is no constant
factor two per cell. On the central interval, periodizing a real Gaussian
and using `|theta+2pi k|>=|theta|` gives

\[
 \int_{|\theta|\le\pi/2}K_t(\theta)
                      \cosh(hY\theta)\,d\theta
 \le e^{t h^2Y^2}.                                    \tag{9}
\]

On the outer interval the periodic Gaussian mass is at most
`2 exp(-pi^2/(16t))`, by the Gaussian Chernoff bound. Hence

\[
 |M|\le e^{xh^2/4}
      \left[e^{t h^2Y^2}+2e^{-\pi^2/(32t)}\right].      \tag{10}
\]

For completeness, the edges obey the same exponentially small estimate.
For `0<=v<=h` and `t<=1`,

\[
 |K_t(\pi+iv)|\le t^{-1/2}
                    e^{-(\pi^2-v^2)/(4t)}.
\]

This follows by summing the Gaussian images at odd multiples of `pi`;
the sum after removing its two leading terms is bounded by the geometric
series with ratio `exp(-2pi^2/t)`. On either edge,

\[
 |F_z(\pm\pi+iv)|
   =\sinh((h-v)/2)^{2x}e^{\mp\pi y}\le e^{\pi Y},
\]

since `sinh(1/2)<1`. Their total absolute contribution is consequently at
most

\[
 2h t^{-1/2}e^{-(7\pi^2-8)/(32t)}
       \le 2e^{-\pi^2/(32t)}.                          \tag{11}
\]

The last inequality holds on `0<t<=1`: after taking logarithms its
nontrivial part is `(t/2)log(1/t)<=(6pi^2-8)/32`, while the left side is
at most `1/(2e)`.

Combining (10) and (11), and using `x>=0`, yields

\[
 |U(z;t,h)|\le
 \exp\left(xh^2/4+t h^2Y^2+4e^{-\pi^2/(32t)}\right).
\]

Here `tY^2<=(pi/32)Y`, and
`4 exp(-pi^2/(32t))<=8t` for `0<t<=1`. Thus this bound is smaller than
the right side of (5). This completes the single-cell estimate.

## Local convergence and Carlson uniqueness

For every compact set `C` in the closed right half-plane there are
`delta_C>0` and `A_C<infinity` such that

\[
 \sup_{z\in C}|U(z;t,h)-1|\le A_C(t+h^2)
       \quad(0<t<\delta_C,\ |h|<\delta_C).              \tag{12}
\]

To verify (12), use the same shifted contour. On `|theta|<=1` and small
`h`, the principal logarithm of the shifted cosine is
`O(theta^2+h^2)`, uniformly, and its `2z`-power differs from one by
`O_C(theta^2+h^2)`. The periodic Gaussian second moment on this interval
is at most the unwrapped moment `2t`. Outside it the shifted power is
uniformly bounded for `z in C`; the Gaussian mass is `O(exp(-1/(4t)))`.
The vertical contribution is `O_C(exp(-c/t))`. These estimates give
(12), including `z=0` (where in fact `U=1` exactly).

Condition (3), (12), and the usual product convergence criterion give
local uniform convergence. Finite factors can have zeros; those do not
affect this argument. For each `epsilon>0`, remove a finite set of indices
so that every remaining `t_i,|h_i|<=1` and
`3 sum_remaining h_i^2<epsilon`. Each removed factor is bounded throughout
the right half-plane by its finite constant in (6). Estimate (5) on the
remaining factors proves (4).

Apply Carlson's theorem to the difference of two products. It is
holomorphic in the open right half-plane and continuous on its boundary,
has exponential type less than any prescribed positive constant, and
vanishes at `0,1,2,...`. Therefore it vanishes identically. If a formulation
of Carlson requires holomorphy across the boundary, apply it instead to
the difference shifted by one; local convergence on the open half-plane
gives the necessary neighborhood of `Re z>=0`, and the same growth bound
holds after that shift. Equality on `Re z>1` then extends to `Re z>0` by
the identity theorem.

## Prior theorem and applicability

The uniqueness theorem used is classical Carlson, not a new theorem here.
Jonathan Pila, *Note on Carlson's theorem* (2003), opening paragraph and
the proof on pp. 1–3, states the relevant right-half-plane version and
attributes it to F. Carlson, *Sur une classe des séries de Taylor* (1914).
Primary research note inspected:
<https://people.maths.ox.ac.uk/pila/carlson.pdf>.

The new candidate contribution is the **source-uniform exponential-type
estimate** (5) and its summable-resource consequence. In particular, a
naive multiplication of the raw bounds `exp(h_i^2/(4t_i))` is invalid in
the allowed infinite-energy reservoir; the contour estimate supplies the
missing replacement.

This discharges only the exact analytic-continuation step. A separate
argument must still establish any claimed meromorphic pole/zero
consequence and connect that consequence to finite forcing. None of
those conclusions is assumed in this note.
