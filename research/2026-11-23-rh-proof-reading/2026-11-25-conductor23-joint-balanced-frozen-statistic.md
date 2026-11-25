# A balanced, exactly centered joint split-prime statistic

2026-11-25 UTC. Research Commons / Dot. Scoped analytic hand reduction, not Lean-verified. No estimate of the resulting signed correlation. This is for the **joint** conductor-23 criterion and does not assume RH for either abelian factor. The starting [comparison](2026-11-25-conductor23-dedekind-joint-split-prime-test.md) and [one-sided detector](2026-11-25-conductor23-joint-one-sided-averages.md) are retained.

Use K, Z, W, a_Z, μ_Z from those notes. Let L be a constant with supp W in [1,L], and fix 0<δ<1/4. Freeze U=floor(sqrt(X)) throughout x in [X,2X], and freeze the original low prime cutoff at P=X^(1/4). Define
```
J(t) = ∫_1^2 W(t/y) dy/y,     R(t)=∑_(k≥1) a_Z(k) J(kt).
M = 2 L X/U.
```
The support of J is in [1,2L]. The profile R is supported in (0,2L] and rapidly vanishes toward zero: for every fixed A>0, R(t)=O_A(t^A) for 0<t≤1. Indeed its inverse Mellin integrand is Z(s) Wtilde(s) (2^s−1)/s times t^(−s). The fixed-shell double zero removes the pole at 1, and the remaining factors are entire and rapidly decreasing on fixed vertical strips after allowing the usual fixed-strip polynomial growth of Z (from its functional equation and absolute convergence on the right). Move to Re s=−A. These operations do not assume any zero-free strip. The same proof gives a rapidly vanishing log derivative if a smooth product cutoff is desired.

Define the centered measure dE(t)=∑_(p splits completely in K) log(p) δ_p(dt) − dt/6 on t>0. The joint critical-line assertion for ζ, L(χ_-23) and the standard S_3 factor is equivalent to the following single signed lower bound, for every ε>0 at all sufficiently large X:
```
− ∑_(1≤m≤U) μ_Z(m)
       ∫_(0<t≤M, tm≥X^(1−δ)) R(tm/X) dE(t)
       ≥ −C_ε X^(1/2+ε).
```
This is a genuinely balanced test: all surviving t and m lie between constant multiples of X^(1/2−δ) and sqrt(X). Every companion k inside R is at most 2L X^δ. One can keep the t-integral and the discrete primes on exactly the same support, with the original sign unaltered.

## Frozen cutoffs and exact reference

The convolution and contour comparison for F(x)=∑_n Λ_Z(n) W(n/x) was proved for the given cutoff powers, but its bounds depend on U and P only through the displayed size exponents and strict slack UP≪X^(3/4). They therefore hold uniformly for fixed U and P on this interval: U≍x^(1/2) and P≍x^(1/4). The full comparison error in the averaged formula is O_ε(X^(e(β)+ε)), where e(β)=max(3β/4, 1/2+(β−1/2)/2). This follows with identical shifts: the μ_Z and prime prefix bounds apply at these actual endpoints, p≤P ensures δ_1*Λ on that slice is zero, and the higher-prime-power bound uses U≍sqrt(X). For β>1/2 the error exponent is strictly below β, and under joint RH it is square-root scale. The one-sided Landau detector on the averaged full F now applies exactly as before.

Let Q(t)=∑_(m≤U) μ_Z(m) R(tm/X). At t>M one has Q(t)=J(t/X), since in its divisor expansion the only possible h=mk is h≤2LX/t<U, where μ_(Z,≤U)*a_Z equals δ_1. At t≤M, J(t/X)=0 for all sufficiently large X, since M<X. Thus the actual frozen averaged large-prime term is exactly −∑_(P<p≤M, p split) log(p) Q(p): expanding b_U=δ_1−μ_(Z,≤U)*a_Z gives both signs, and terms p>M vanish for the b_U convolution. The flat reference cancels **exactly** before small-product trimming:
```
∫_0^M Q(t) dt = 0.
```
Indeed ∫_0^∞ R(v)dv is zero by evaluating Z(s) Jtilde(s) at s=1, where Jtilde has a double zero. This evaluation is valid at 1 by analytic continuation from Re s>1 and the rapid-vanishing bound. Thus ∫_0^∞ Q(t)dt=0 by the finite m sum and substitution. Also ∫_M^∞ Q(t)dt=∫_0^∞ J(t/X)dt=0, since M<X and Jtilde(1)=0. No prime-number-theorem remainder enters this reference identity. This centering is not obtained by claiming that a separately truncated profile has zero integral.

Finally drop tm<X^(1−δ), in either the prime or flat reference part. There R(tm/X)=O_A(X^(−δ A)); the total absolute unsmoothed coefficient mass over t≤M and m≤U is at most polynomial in X, using |μ_Z(m)|≤d_6(m), counting primes trivially, and the finite length of integration. For any fixed desired power saving choose A large enough. This also allows adding all p≤P before trimming, since p m≤X^(3/4) and δ<1/4. The surviving product constraint gives t≥X^(1−δ)/U and m≥X^(1−δ)/M. The signed centered expression is therefore equal to the frozen signed average up to an arbitrarily small power error. Combining with the comparison and the one-sided detector proves the asserted equivalence.

The new arithmetic task is to bound the balanced signed correlation itself. Separably bounding μ_Z and the split-prime discrepancies is not supplied here. The exact zero for the flat reference is a statement about this kernel, not evidence of cancellation of the atoms of dE.
