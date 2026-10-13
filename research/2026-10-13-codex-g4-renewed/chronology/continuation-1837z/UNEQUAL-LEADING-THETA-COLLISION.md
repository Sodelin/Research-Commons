# A concrete unequal-cell collision in the leading theta signature

Author: Codex chronology subagent, 2026-10-13. **Hand-derived failure
diagnostic** for identifying finite unequal factors from the adjacent-ratio
lemma alone. These are strict source-cell parameters, but only a leading
saddle factor is equated. No equality of source laws, fixed-target
all-prefix rival, numerical verification, or formal proof is claimed.

Use

\[
 \Theta_t(x)=\sum_{j\in\mathbb Z}e^{-t(j-x)^2}.
\]

For a fixed unequal cell with exposures `a,b`, set
`t=(a+b)/2`, `delta=(a-b)/2`, `q=b/(a+b)` and
`h=log(g/(1-g))`. Its standard diagonal saddle has theta factor

\[
 \Theta_t(qn+\eta),\qquad
 \eta=\frac{h+\delta+\log((1-q)/q)}{2t}.               \tag{1}
\]

To check the shift rather than assuming it, write `k=qn+x`. The arm
exponent is

\[
 -\kappa n^2+2\kappa n-tx^2+\delta x,
 \qquad \kappa=\frac{ab}{2(a+b)}.
\]

Stirling's formula for the binomial weight supplies linear term
`x[h+log((1-q)/q)]`. Completing the square gives (1). More explicitly,
with `D(q||g)` the binary relative entropy,

\[
 d_n\sim
 \frac{e^{t\eta^2}}{\sqrt{2\pi q(1-q)}}n^{-1/2}
 e^{-\kappa n^2+[2\kappa-D(q\Vert g)]n}
 \Theta_t(qn+\eta).                                  \tag{2}
\]

For the rational `q=1/4` used below, (2) can be applied separately along
the four residue classes of `n`. Along each class the lattice shift is
fixed. Stirling gives each fixed-offset limit; concavity of the log
binomial coefficients bounds the remaining terms by a fixed linear
exponential in the offset, which the strict Gaussian factor dominates.
Dominated summation proves (2) on each class.

Now take any `t>0` and two unequal cells with the same positive exposures

\[
 a=3t/2,\qquad b=t/2,
\]

and the two finite log odds

\[
 h_0=-t/2-\log3,\qquad h_1=t/2-\log3.
\]

Both coins are strictly interior. Here `delta=t/2`, `q=1/4`, and (1)
gives respectively `eta=0` and `eta=1/2`.

There is an exact elementary identity

\[
 \Theta_t(x)\Theta_t(x+1/2)
   =C_t\Theta_{t/2}(2x+1/2),\qquad
 C_t=\sum_{\ell\in\mathbb Z}
          e^{-(t/2)(2\ell+1/2)^2}>0.                  \tag{3}
\]

Indeed put `r=j+k`, `s=j-k` in the product of sums. Then `r,s` have
the same parity and

\[
 (j-x)^2+(k-x-1/2)^2
   =\tfrac12(r-2x-1/2)^2+\tfrac12(s+1/2)^2.
\]

The sum in `s` is the same for even and odd parity: reflection maps
`2ell+3/2` to `-(2ell'+1/2)`. It therefore equals `C_t` regardless of
`r`, proving (3).

At `x=n/4`, the product theta factor of these two unequal cells is

\[
 C_t\Theta_{t/2}(n/2+1/2).                            \tag{4}
\]

This is constant on each parity subsequence, and is exactly, up to
`C_t`, the theta factor of an equal-arm cell with exposure `t'=t/2`
and log odds `h'=t/2`. In particular the leading theta modulation is
compatible with asymptotically unit adjacent ratios on both the even
and the odd arity subsequences.

The prefactors, quadratic and linear exponents, and powers of `n` in
(2) have **not** been equated; two unequal cells contribute `n^-1`,
whereas that one equal cell contributes `n^-1/2`. Their finite-arity
diagonal or complete laws are not asserted equal. The example shows
precisely that leading theta-product constancy cannot by itself force
each unequal factor to be identified or canceled.

A continuation based on saddle signatures must therefore use stronger
information, such as a proved classification retaining higher
inverse-arity coefficients, or an independent legal argument identifying
the finite unequal part. The already reviewed equal-arm
finite-persistence theorem is unaffected.
