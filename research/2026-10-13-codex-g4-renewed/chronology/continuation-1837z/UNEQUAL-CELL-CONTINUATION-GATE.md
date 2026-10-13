# Unequal private cells: the meromorphic step survives, Carlson does not transfer directly

Author: Codex chronology subagent, 2026-10-13. **Hand-derived continuation
diagnostic**, requested by the lead after the equal-arm finite-persistence
proof. No numerical or formal verification, general impossibility, or
source-valid rival construction is claimed.

Consider one private cell with positive arm coalescent exposures `a,b` and
coin `g in (0,1)`. Put

\[
 t=(a+b)/2,\qquad \delta=(a-b)/2,\qquad
 h=\log(g/(1-g)),\qquad b_g=\log\cosh(h/2).
\]

Thus `|delta|<t`. Its no-merger diagonal is

\[
 d_n=\sum_{k=0}^n\binom nk g^k(1-g)^{n-k}
        e^{-a\binom{k}{2}-b\binom{n-k}{2}}.
\]

For `n=2m`, set `S=k-m`. Direct expansion, with no limiting operation,
gives

\[
 \boxed{d_{2m}=e^{-t(m^2-m)-2mb_g}
        U(m;t,h+\delta-2\delta m).}                    \tag{1}
\]

Indeed the arm exponent is
`-t(m^2-m+S^2)-delta(2m-1)S`, while the binomial weight contributes
`exp(hS-2mb_g)` relative to the fair centered binomial law.

## What the exact continuation does retain

Define

\[
 V(z)=U(z;t,h+\delta-2\delta z).                        \tag{2}
\]

The Mellin-density construction in the reviewed equal-arm proof is
holomorphic jointly in its bias variable and meromorphic in `z`. Its pole
set is contained in the fixed lattice
`{-1/2,-3/2,-5/2,...}`. Substituting the affine bias in (2) therefore still
gives a meromorphic function with only possible simple poles on that same
lattice. Some residues may vanish. Also `V(0)=1`.

Consequently a finite unequal target or rival would not obstruct the
final meromorphic zero-accumulation contradiction **if** its canonical
continuation were known to equal the product continuation from the
integer data. The new issue is that implication, not the location of poles.

## The growth obstruction is exact

Write `z=x+iy`, `H_0=h+delta`. In the periodic heat-kernel integral,

\[
 \theta+i(H_0-2\delta z)
     =\theta+2\delta y+i(H_0-2\delta x).
\]

For `x>=0`, the modulus of the real-contour cosine power is at most one.
Periodicity and positivity of the real heat kernel give the uniform bound

\[
 |V(x+iy)|\le
       \exp\bigl((H_0-2\delta x)^2/(4t)\bigr).         \tag{3}
\]

Thus this function is bounded on the imaginary axis, but its available
right-half-plane growth is quadratic in the real part. That quadratic
growth is genuine whenever the arms differ:

\[
 \lim_{m\to\infty}\frac{\log V(m)}{m^2}
                         =\frac{\delta^2}{t}>0.       \tag{4}
\]

For the upper bound, complete the square in
`-t S^2+(H_0-2delta m)S`; its maximum is
`(H_0-2delta m)^2/(4t)`. For the lower bound choose an allowed integer
`S` nearest `-delta m/t`, which lies strictly inside `[-m,m]` for all
sufficiently large `m`. Its fair binomial mass is at least `2^(-2m)`.
That single term has logarithm `delta^2 m^2/t+O(m)`. Binomial symmetry
identifies the exponential-bias sum with the `cosh` sum, so this lower
bound applies to `V(m)` exactly. This proves (4).

Removing this real-axis quadratic by multiplying by
`exp(-delta^2 z^2/t)` introduces the inverse Gaussian factor
`exp(delta^2 y^2/t)` on the imaginary axis. Thus the equal-arm
zero-exponential-type argument does not carry over by the same
normalization. No claim that this observation rules out a different
uniqueness theorem is made.

The properties "meromorphic with poles only at those half-integers,
bounded on the imaginary axis, and bounded by a Gaussian in `Re z`"
are themselves insufficient for uniqueness from nonnegative integers.
For every `c>0`, the nonzero entire function

\[
 G_c(z)=e^{cz^2}\sin(\pi z)
\]

vanishes at every integer and obeys, throughout `x>=0`,

\[
 |G_c(x+iy)|\le
 e^{cx^2-cy^2+\pi|y|}
 \le e^{cx^2+\pi^2/(4c)}.                             \tag{5}
\]

This is an analytic interpolation counterexample, not an admitted source
or a counterexample to G4. It identifies a missing premise in a direct
extension of the new proof.

## Exact source boundary and the next useful premise

The accepted COMMON divisor palette fixes an unequal private cell's
exposure difference and coin within a finite list. It does **not** fix its
shorter-arm exposure. Hence it does not fix `t`, the unequal saddle
coefficient `delta^2/t`, or the function (2). The original exposure
correction must also be retained: these are coalescent exposures, not
calendar durations.

If an additional legal argument identifies the complete unequal diagonal
product on the two sides, those factors can be canceled at every integer,
and the reviewed equal-arm finite-persistence theorem applies to the
remaining product. That conditional observation does not supply the
identification, and no such cancellation follows merely from the finite
COMMON palette.

Otherwise the precise remaining analytic duty is an integer uniqueness
principle for these affine-bias cell products, using additional structure
stronger than (3), or a legal forest invariant that removes the unequal
finite part before invoking the equal-cell product theorem. Failure of
this one canonical continuation does not imply impossibility of either
private or original G4 forcing.
