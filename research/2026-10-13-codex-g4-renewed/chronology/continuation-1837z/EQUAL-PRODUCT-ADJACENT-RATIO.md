# A summable equal-cell product has asymptotically unit adjacent ratio

Author: Codex chronology subagent, 2026-10-13. **Hand-derived lemma,
review requested.** This is a possible compatibility test for the finite
unequal part after the reviewed equal-arm finite-persistence advance.
It does not identify that unequal part or close the remaining G4 scope.
No numerical or formal verification is claimed.

Write `U_m=U(m;t,h)` in the companion Carlson notation, so its physical
arity is `2m`, and put `b=log cosh(h/2)`. Then for every integer `m>=0`,

\[
 e^{-t/2}\le\frac{U_{m+1}}{U_m}\le e^{2b}.             \tag{1}
\]

For the lower bound let `S=Bin(2m,1/2)-m`, use the equivalent exponential
bias form `U_m=E exp(-tS^2+hS)`, and add two independent fair increments.
Their centered sum is `Y in {-1,0,1}` with probabilities `1/4,1/2,1/4`.
With expectation under the positive tilt proportional to
`exp(-tS^2+hS)`,

\[
 \frac{U_{m+1}}{U_m}
   =\frac12+\frac{e^{-t}}2\mathbb E_*\cosh(h-2tS)
   \ge\frac{1+e^{-t}}2\ge e^{-t/2}.                  \tag{2}
\]

For the upper bound reuse the inherited uniform diagonal transport
inequality `d_{n+2}/d_n<=exp(-nt)` for a strict equal-arm cell. The exact
diagonal normalization gives

\[
 \frac{d_{2m+2}}{d_{2m}}
   =e^{-2mt-2b}\frac{U_{m+1}}{U_m},
\]

which proves the upper bound. At `m=0` it also follows directly from (2),
since `S=0` and `(1+cosh h)/2=exp(2b)`.

For each fixed strict cell,

\[
 U_m\sim\frac{1}{\sqrt{\pi m}}
                 \sum_{k\in\mathbb Z}e^{-tk^2+hk}.
                                                               \tag{3}
\]

This is the standard fixed-cell even-parity saddle estimate: divide each
centered binomial probability by its central probability; its ratio is
at most one and tends to one for each fixed `k`. The Gaussian summand is
summable, so dominated convergence and the central-binomial asymptotic
give (3). In particular each fixed-cell adjacent ratio tends to one.

Now suppose a finite or countable equal-cell family has
`sum t_i<infinity` and `sum b_i<infinity`. Its pointwise positive product
`P(m)=product_i U(m;t_i,h_i)` is well defined by the inherited absolute
residual bound. Equation (1) gives the summable domination

\[
 \left|\log\frac{U(m+1;t_i,h_i)}{U(m;t_i,h_i)}\right|
       \le t_i/2+2b_i.
\]

Taking the countable sum and applying dominated convergence to the
fixed-cell limits proves

\[
 \boxed{\frac{P(m+1)}{P(m)}\longrightarrow1.}          \tag{4}
\]

This allows arbitrary bias-to-clock ratios, arbitrary chronological
positions, and infinitely many cells. It is not a termwise nonnegativity
argument and does not assume finite energy.

## Conditional consequence for a finite unequal saddle signature

Suppose a separate exact saddle analysis has represented a finite
unequal-factor quotient, after its quadratic and linear normalizations,
as

\[
 m^\gamma F(T^m x_0)(1+o(1)),
\]

where `T` is a rotation of a compact torus and `F` is continuous and
strictly positive on the orbit closure. If this quotient equals such a
`P(m)` exactly, (4) forces
`F(T^(m+1)x_0)/F(T^m x_0)->1`.
The function `F(Tx)/F(x)` is continuous on the orbit closure. Every point
there is a limit of orbit points with indices tending to infinity, so it
equals one everywhere. Rotation minimality on its orbit closure then
implies that `F` is constant there.

Thus a genuinely varying positive quasiperiodic leading signature cannot
be canceled by any summable equal-cell product. This implication is
conditional on the stated saddle representation; it is not a proof that
all unequal parameters are identified. Integer-frequency aliases and
theta-product identities must be addressed before using it for that
stronger purpose. COMMON's finite difference/coin palette alone does not
supply the missing identification.

Reused transport provider:
[UNIFORM-DIAGONAL-RATIO-TRANSPORT-1244.md](../../../2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/UNIFORM-DIAGONAL-RATIO-TRANSPORT-1244.md).
Inspected source SHA256:
`9ba886e2a38aed6cb4edc93018a40ad9db34e11a663fdecd7446b226f94ae051`.
