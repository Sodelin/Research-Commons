# The joint conductor-23 prime test balances to within polylogarithmic factors

2026-11-25 UTC. Research Commons / Dot. Scoped analytic hand proof, no Lean verification or signed prime estimate. This strengthens the [frozen balanced joint reduction](2026-11-25-conductor23-joint-balanced-frozen-statistic.md), retaining its lower sign, exact flat centering, and absence of an abelian RH hypothesis. It does not assert joint RH.

In that reduction put U=floor(sqrt X), M=2LX/U, with L the fixed upper support bound for W. Use the same centered prime measure dE, coefficients μ_Z and profile R. If the compact log smoothing of W_0 uses independent uniforms on [0,ell_j], ell_j=c j^(-a) with any fixed a>1, the product filter can be strengthened to
```
tm ≥ X/(log X)^B,                  any fixed B>6a.
```
In particular B>12 works for the exact original a=2 test. For any prescribed B>6 one can instead choose 1<a<B/6, retaining the same shell construction and detector. Consequently the actual prime and inverse-coefficient variables both lie between constant multiples of sqrt(X)/(log X)^B and sqrt(X), and every companion k inside R is at most 2L(log X)^B. The signed lower bound on this genuinely balanced logarithmic-size enlargement of sqrt(X) is still equivalent to the joint assertion. No truncation of ordinates or choice of a rightmost zero is used.

## Quantitative rapid vanishing of the profile

Write s=−A+it with A a positive integer. Since each uniform transform is its average exp(su) and also equals (exp(s ell_j)−1)/(s ell_j), for Re s≤0 it is bounded in modulus by min(1,2/(|s|ell_j)). Take the first floor(c_0 |s|^(1/a)) factors for sufficiently small fixed c_0>0. Each is at most 1/2; all later factors are at most 1. This proves the uniform bound
```
|Wtilde_0(s)| ≪ exp(−c_1 |s|^(1/a))    (Re s≤0).
```
The double shell factor (1−exp((s−1)B_0))², with fixed shell spacing B_0, and the dyadic averaging factor (2^s−1)/s are bounded on these lines. The transform stays nonzero in the original open off-line strip, since the summed lengths are finite and the tail factors differ from 1 by a summable amount at any fixed s. The proof of the two previous reductions therefore also applies to these other fixed choices of a.

The field K is totally imaginary of degree six: every embedding permutes the roots of the cubic, which has nonreal roots. Its completed Dedekind zeta has archimedean factor proportional to C_K^s Γ(s)^3, with fixed C_K>0, and functional equation at 1−s. See [the Artin factorization and Dedekind functional equation conventions](https://doi.org/10.1007/s40993-017-0079-5). For A≥1, absolute convergence at 1+A bounds |Z(1−s)| by Z(2), and the functional equation bounds |Z(s)| by
```
C^(A+1) |Γ(1−s)/Γ(s)|³.
```
On the chosen integer line the gamma ratio has an explicit formula in absolute value:
```
|Γ(1+A−it)/Γ(−A+it)| = |t| ∏_(j=1)^A (j²+t²).
```
Indeed use reflection, recurrence and |Γ(1−it)|²=π|t|/sinh(π|t|); the identity extends at t=0. Thus the bound for Z is at most C^(A+1)(A+|t|)^(6A+3).

The Mellin integrand for R contains Z(s)Wtilde(s)(2^s−1)/s. Its pole at 1 is removable. For each fixed A the vertical displacement was already justified by rapid decay and fixed-strip growth. After displacement, the uniform bounds above imply for w>0
```
|R(w)| ≪ C^(A+1) w^A ∫_(0)^∞ (A+t)^(6A+3) exp(−c_2(A+t)^(1/a)) dt
       ≪ C_3^(A+1) w^A A^(6a A+C_4),
```
where |s| is comparable with A+|t| and constants depend only on the chosen test and field. To get the last line, extend the integral in u=A+t down to zero and substitute v=c_2 u^(1/a); the gamma factor is Γ(a(6A+4)), and Stirling's bound gives the stated growth. Choosing A=floor(c_3 w^(−1/(6a))) with sufficiently small fixed c_3>0 absorbs the exponential C_3^A and the polynomial A^C_4, and gives
```
R(w) ≪ exp(−c_4 w^(−1/(6a)))        as w→0+.
```
Only a fixed field and fixed log-smoothing test are used. This is not a bound uniform as a approaches one.

## Effect on the original terms

Below the new cutoff R(tm/X) is O_D(X^(−D)) for every fixed D, because B/(6a)>1. The total unweighted mass of the finite prime/flat integrals and coefficient sum in the frozen reduction was polynomial in X, so the corresponding deletion stays O_D(X^(−D)) after increasing D initially. In particular adding p≤X^(1/4) still changes nothing at the target scale. The exact flat-integral identity holds before the trim, as before; the altered trimmed flat term is merely superpolynomially close, not asserted exactly zero. The original comparison error with the full Dedekind logarithmic derivative is unchanged, so the one-sided Landau argument applies in both directions.

This locates the unsolved estimate in a polylogarithmic-width multiplicative neighborhood of the square-root scale with only polylogarithmic companions. It does not give a power-saving signed bound there. The gain over the polynomial localization is useful for trying local prime estimates with a common length hierarchy.
