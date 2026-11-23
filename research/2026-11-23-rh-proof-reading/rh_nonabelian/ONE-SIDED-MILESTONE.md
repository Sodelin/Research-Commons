# Closer to the original proof: a one-sided ceiling suffices for the S₃ factor

**Status:** classical analytic implication applied to one factor, not a bound on the actual prime sum. No all-height zero claim or Lean run.

## Real-axis zero-freeness from a positive eta product

The [LMFDB modular form 108.1.c.a](https://www.lmfdb.org/ModularForm/GL2/Q/holomorphic/108/1/c/a/#) gives the expression f(z)=η(6z)η(18z) for the weight-one form whose L-function is this Artin factor. See also K. Ono's [Twists of elliptic curves, pp. 357–358](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/DD0C8330A44D86EE41EC0A75D87282F8/S0010437X97000316a.pdf/twists_of_elliptic_curves.pdf), or the LMFDB record without relying on the numerical coefficient check below. For every y>0 the eta factors are strictly positive: the convergent product is a positive real power of e^(−2πy) times factors 1−e^(−2πny)>0. The eta transformation gives

    f(iy) = (sqrt(108) y)^−1 f(i/(108y)).

Thus f(iy) decays exponentially as y→∞ and, up to the displayed power prefactor, exponentially in 1/y as y→0. The Mellin integral

    I(s) = ∫₀^∞ f(iy) y^(s−1) dy

is entire. It equals Γ(s)(2π)^(−s)L(s,ρ) for Re(s)>1 by termwise integration and then as a continued identity. In particular **L(s,ρ)>0 on the entire positive real axis**, including s=1. This claim is independent of whether any complex zero is off the line.

## From a one-sided upper bound to zero-freeness

Set D(s)=−L′(s,ρ)/L(s,ρ), and define exact coefficients c(p^k)=log p·tr ρ(Frob_p^k) for p≥5, zero at the bad primes and off prime powers. Put

    A(X) = Σ_{n≤X} c(n) (X/n−1),
    E(X) = A(X) − D(1) X.

For Re(s)>1 the Mellin transform of E with measure X^(−s−1)dX is

    D(s)/[s(s−1)] − D(1)/(s−1).

Indeed each summand of A integrates to c(n)n^(−s)/[s(s−1)], and the linear term removes the removable pole at 1. D(1) is defined separately via the analytic L-function; the proof does not assert absolute convergence of its prime series at 1.

Fix 1/2<θ<1. Suppose **E(X)≤CX^θ for every sufficiently large X**. The Mellin transform of CX^θ−E(X), with a sufficiently large lower cutoff X₀, is a finite-cutoff entire correction to

    C/(s−θ) − D(s)/[s(s−1)] + D(1)/(s−1).

The integrand is nonnegative. Its abscissa of convergence, if finite, must be a real singularity. For completeness: if it were analytic on a disk about the real abscissa, expand at a nearby point to its right inside the disk. At real arguments to the left of that point, all integrated Taylor terms arising from X^t are nonnegative. Tonelli's theorem then forces convergence slightly to the left of the abscissa, a contradiction. This is the classical Landau argument for eventually nonnegative transforms.

An L-zero with Re(s)>θ would give a genuine pole there, hence an abscissa at least its real part (and at most 1). But at every real point above θ the meromorphic expression is regular: the eta argument gives no real zeros, and at 1 the two D(1) residues cancel. Contradiction. Therefore the upper bound rules out zeros to the right of θ. Prove it with θ=1/2+ε for every small ε>0 and functional symmetry gives RH for this factor.

**What's missing:** establish that one-sided arithmetic ceiling, or prove a windowed criterion for this factor and then provide bounds on the required windows. Mere agreement of coefficients, real-axis positivity, numerical zeros, or the existence of an eta formula does not supply it.

## Exact finite check

The checker also multiplies the eta product as a truncated integral power series and compares the first 999 coefficients with those built independently from the Artin Euler polynomials. This validates the finite arithmetic, not the classical identification used in the proof or its all-height premise.
