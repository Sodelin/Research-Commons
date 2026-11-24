# Two product-cell moments preserve the conductor-23 detector

2026-11-24. Research Commons / Dot. Scoped hand deduction for the exact dilated kernel and actual arithmetic weights, not a prime-cancellation estimate or new Lean verification.

Use the [pinned scalar detector](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3), with locked P,U and Y <= x <= X=Y^(1+o(1)), and fixed B>0. Group by the full product t=ph in the discrete sum, not by the companion index h. Define the signed measure

    d nu(t) = sum_(U<h<=e^B X/P) beta_U(h)
      [sum_(p>P, p splits completely) log(p) delta_(ph)(dt)
       - 1_(t>=Ph) dt/(6h)].

All statements about this measure may be restricted to t<=e^B X. The exact normalized scalar is F(x)=x^(-1/2) integral K_B(t/x) d nu(t). The sign and strict prime cutoff are unchanged. The argument works too after any restriction on the companion index independent of x, for instance fixed roughness, squarefreeness, or a balanced H cutoff. For the scalar detector with every a priori comparison in the cited result, use the full measure. No pairwise mask is discarded or claimed to hold inside an arbitrary modified covariance: this acts before the square.

## The arithmetic local-mass bound

For a real interval I of length d in [1,e^B X], the variation satisfies |nu|(I) <<_(B,epsilon) (d+1) X^epsilon for every epsilon>0. At an integer n<=e^B X, only divisors h|n occur; summing |beta_U(h)| <= d_4(h) over h|n gives <= d_5(n) and log(p) <= log(e^B X). For the continuous density sum |beta_U(h)|/h <= sum_(h<=e^B X) d_4(h)/h <<_epsilon X^epsilon. This bound uses no cancellation and includes exact product coincidences.

## Compressing a cell to its endpoints

Split [1,e^B X] into half-open cells of maximum length D>=1, including fixed cut points at 1 and e^B X with the last endpoint included. For a cell [l,r] away from zero record only its signed mass M and reciprocal moment R, integrals of 1 and 1/t under nu restricted to that cell (using the specified disjoint convention when assigning atoms). Put this mass on the two endpoints with weights A,C solving A+C=M and A/l+C/r=R. In particular

    A = integral_cell (1/t-1/r)/(1/l-1/r) d nu(t),
    C = integral_cell (1/l-1/t)/(1/l-1/r) d nu(t).

The fractions are nonnegative and sum to one, so the variation of the two endpoint atoms is at most |nu|(cell), even when M is zero. The measure has no support below 1 for sufficiently late windows. Endpoint atoms from different cells can be kept as separate contributions.

The exact kernel equals 1-e^(-B) below t=x, x/t-e^(-B) on x<t<e^B x, and zero above e^B x, with agreement at the breakpoints. On any cell that does not cross a breakpoint, one or both moments evaluate its integral exactly. Only the at most two cells containing a breakpoint in their interior can err. For D<=Y/4, the oscillation of the kernel across either such cell is O_B(D/x): use continuity and the derivative bound on its active reciprocal branch. The original and compressed cell have equal mass. Hence the unnormalized error from one such cell is O_B((D/x)|nu|(cell)); it follows uniformly that

    |F(x)-F_compressed(x)| <<_(B,epsilon) D(D+1) X^epsilon / x^(3/2).

This also proves the same bound for any two signed cell measures which match these two moments and satisfy the indicated variation bound. An elementary piecewise-constant approximation would pay an error on all active cells, not just the two at the breakpoints.

## Consequence at the scale that matters

One can use D=Y^(3/4) (or a slightly smaller power for an error tending to zero). The uniform normalized error is then subpower. With equal-width cells the storage consists of O_B(X/Y^(3/4))=X^(1/4+o(1)) pairs of signed moments. This does not bound the time to compute them exactly, nor make the moments independent. Since the log-window length is subpower, the L2 norm of the error is subpower as well. Thus the required subpower L2 criterion for the scalar and its off-line lower signal are unchanged by the compression. Equivalently, an off-line zero cannot require resolving every prime product or companion pair individually for this particular detector. The signed cancellation of the aggregate cell moments remains open. The cell indices in this claim refer to product size, not the prior additive-gap tests on output primes or companion indices.
