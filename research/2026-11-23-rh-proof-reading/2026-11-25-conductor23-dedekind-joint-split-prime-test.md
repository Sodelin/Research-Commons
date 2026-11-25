# An assumption-free joint RH criterion using only the conductor-23 split primes

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof of an equivalence, not a proof of any of the conjectures and not Lean-verified. This is a separate route from the fixed Artin factor with assumed Dirichlet GRH. It tests the simultaneous critical-line assertions for the three constituent functions by changing the inverse coefficients. The signed estimate in the criterion remains open.

Let K be the splitting field of x^3-x-1 (Galois group S_3, quadratic resolvent Q(sqrt(-23))). Write Z=ζ_K. By the regular representation [Artin factorization](https://www.math.iitb.ac.in/~dprasad/artin.pdf),
    Z(s)=ζ(s)L(s,χ_{-23})L(s,ρ_std)^2.
In the open critical strip the factors have no poles, so the nontrivial zeros of the product are precisely their union with multiplicities. For unramified primes p,
    Λ_Z(p)=6 log(p) * 1_(p splits completely in K).
Indeed the prime-ideal residue degrees are all equal to the Frobenius order, so the coefficient of p itself is zero except when that order is one. As usual Λ_Z denotes the coefficients of -Z'/Z, and |Λ_Z(p^k)|<=6 log p, including ramified primes.

Fix u,alpha>0 with u+alpha<1, set U=floor(x^u) and P=x^alpha, let a_Z and μ_Z be the coefficients of Z and 1/Z, and set b_U=μ_{Z,>U}*a_Z. Choose a fixed nonnegative smooth compactly supported function W_0 on t in [1,exp(d)] whose Mellin transform is nonzero on Re s>0. For instance take the density on v=log t of a convolution of positive uniforms of lengths proportional to j^(-2), with sum d. It is smooth because the Fourier transform decays to arbitrary polynomial order; its Mellin transform is a convergent product of (exp(s ell_j)-1)/(s ell_j), nonzero there by absolute convergence of the deviations of the tail factors from one. Take B>d and set
    W(t)=W_0(t)-2 exp(-B) W_0(exp(-B)t)+exp(-2B) W_0(exp(-2B)t).
Its Mellin transform is Wtilde_0(s)(1-exp((s-1)B))². Thus it has a double zero at 1, and no zeros for 1/2<Re s<1. It is rapidly decreasing on each fixed vertical strip. This test uses three disjoint fixed shells.

The criterion is
    |∑_{p>P, p splits completely} log p ∑_{h>U} b_U(h) W(ph/x)|
      = O_epsilon(x^(1/2+epsilon))     for every epsilon>0, all sufficiently large x.      (C)
It is equivalent to the critical-line assertion for the union of the three factors above. Nothing is assumed about either abelian factor in the direction from (C) to that assertion. This note uses all-large-x bounds; it does not establish a sparse-window detector for this changed coefficient model.

## Analytic comparison with the full Dedekind logarithmic derivative

Put β=max(1/2,sup Re ρ of the nontrivial zeros of Z) and M_U(s)=∑_{m<=U} μ_Z(m)m^(-s). Let D(s)=∑_p Λ_Z(p)p^(-s) on Re s>1. The same sharp twisted-prefix Perron argument as in the [degree-two proof, display (2)](https://github.com/Sodelin/Research-Commons/commit/89d1c3233e8cdcdbac25dab42c512b1768d9cefd) gives, for any fixed 0<σ<1/2 and every ε>0,
    |M_U(σ+it)| << U^(β-σ+ε)(3+|t|)^ε,
    ∑_{p<=P} Λ_Z(p)p^(-s) = P^(1-s)/(1-s)
                          + O(P^(β-σ+ε)(3+|t|)^ε).
In the second line D(s) continues to Re s>β except for its pole at 1 of residue 1, from -Z'/Z; the prime-power part is absolutely holomorphic on Re s>1/2. For clarity, run the Perron shifts to Re(s+w)=β+δ for small δ at the prefix endpoint rounded to the half integer, using |μ_Z(n)|<=d_6(n), |Λ_Z(p)|<=6 log p and a height at least the cube of that endpoint times (3+|t|). Subtract 1/(s+w-1) from D(s+w) before the shift. For β<1 choose δ so β+δ<1; shift this polar term separately. Between the initial and new lines its only crossed pole is w=1-s (both lines have Re w>0), giving the displayed power; the new-line polar integral has the same prefix-error bound. Rounding changes the term by O(P^-σ) uniformly by its integral representation for differences. For β=1 the same bounds follow by elementary absolute estimates, because the explicit main term itself has magnitude O_σ(P^(1-σ)). For the inverse on Re s>β+δ use the classical logarithm/Borel–Carathéodory and three-lines argument in the pinned proof on the pole-removed nonvanishing function (s-1)Z(s)/(s+1), which is polynomially bounded on fixed strips and admits a bounded logarithm on Re s=2. This gives (3+|t|)^ε for 1/Z(s); the pole at 1 is a removable zero for the reciprocal. These are the same fixed-degree estimates, with more rapid decay from W so no degree-two restriction on vertical integrability.

The exact convolution identity Λ_Z=μ_{Z,<=U}*(a_Z log)+b_U*Λ_Z shows which parts must be removed. The first term has Mellin integrand -M_U(s) Z'(s) Wtilde(s)x^s; the possible double pole at 1 disappears. Shift to the fixed σ just above zero to obtain O(x^σ U^(β-σ+ε)). For the low-prime portion of b_U*Λ_Z, use b_U=δ_1-μ_{Z,<=U}*a_Z. The δ_1 part vanishes because W(t)=0 below 1 and P<x. The other part has integrand -M_U(s)Z(s) Wtilde(s)x^s times the finite prime prefix. The pole of Z at 1 is removable after multiplication by Wtilde. On the line σ use the second prefix estimate. Its error term costs O(x^σ(UP)^(β-σ+ε)); its separate P^(1-s)/(1-s) main term can shift to any fixed -A after cancellation by the same **double** zero at 1. Its size is O_A(P U^(1+ε)(PU/x)^A), superpolynomially small for fixed u+alpha<1. All such shifts use rapid decay and fixed-strip polynomial growth of Z and Z'.

For higher prime powers in the b_U term, the δ_1 piece is O(x^(1/2+ε)) by elementary counting. In the -M_U Z piece use absolute convergence of the prime-power series on a fixed line just right of 1/2, and the corresponding twisted inverse-prefix estimate O(U^((β-σ)_++ε)(3+|t|)^ε) there, proved the same way. This costs O(x^(1/2+u(β-1/2)+ε)). For sufficiently large x all retained p>P are unramified. Combining the estimates gives
    ∑_n Λ_Z(n) W(n/x) = 6 D_raw(x) + O_eps(x^(max{β(u+alpha), 1/2+u(β-1/2)}+eps)),
where D_raw denotes the sum in (C), and σ was taken sufficiently close to zero in terms of eps. No continuous prime reference remains. The comparison error is subcritical in any off-line case and square-root scale when β=1/2.

## Both directions of the criterion

Under the joint RH, shift the full smoothed logarithmic derivative to Re s=1/2+ε. Its pole at 1 is cancelled, and its local-zero bound on that line is at most polynomial in height; rapid decay suffices. The comparison proves (C).

Conversely, if β>1/2, choose ε small enough so the comparison exponent and the exponent in (C) are both below some fixed γ<β. Then F(x)=∑ Λ_Z(n)W(n/x)=O(x^γ). Since F vanishes for sufficiently small x, its x-Mellin transform ∫_0^∞ F(x)x^(-s-1)dx is holomorphic for Re s>γ. For Re s>1 it equals Wtilde(s)(-Z'/Z)(s) by absolute convergence. Choose a nontrivial zero with Re ρ>γ, which is possible even without attainment of β. Its multiplicity makes a nonzero residue, since Wtilde does not vanish in the open off-line strip. Meromorphic uniqueness contradicts holomorphy. The functional equations give the other side of the line. This implication uses no auxiliary zero-free assertion other than the definition of the actual supremum.

## Optional separated-pair form

The [shared-prime argument](2026-11-25-conductor23-shared-prime-covariance.md) also transfers. For fixed p on active support, the inner b_U sum can move to an arbitrarily small positive Mellin line, since Z's pole is cancelled by Wtilde. The bound is U^β x^ε via the inverse-prefix estimate, with p<=exp(2B+d)x/U. After normalization by sqrt x, same or subpower-close prime pairs cost O(U^(2β-1)x^ε). Under β=1/2 this is subpower. If the remaining signed separated-prime square were subpower for every sufficiently large x, (C) would follow: a contrary β>1/2 gives the square an envelope with exponent u(2β-1)+ε, so the raw first moment would be O(x^(1/2+u(β-1/2)+ε)), still strictly below x^β, and the same Mellin contradiction applies. The separated-pair bound is not proved here.
