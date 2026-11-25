# Finite geometric sampling of the rightmost-zero conductor-23 detector

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof, no Lean verification. Uses the two-thin-shell version with the original arithmetic comparison hypotheses. It replaces continuous checking by a finite number of geometric samples when a zero attains the rightmost real part. Neither an arithmetic bound at those samples nor a treatment of an unattained supremum is proved here.

Let u=log x, and let S_X(u) be the signed normalized retained [two-shell detector](2026-11-25-conductor23-two-thin-product-shells.md) with cutoffs locked at X; fixed extra smoothing is allowed. Use its prior zero expansion and uniform power-gap comparison on the interior of its locked windows. Suppose beta_*>1/2 is attained and put a=beta_*-1/2. In that setting the expansion gives
```
exp(-a u) S_X(u) = P(u) + o(1),
P(u) = sum_{Re rho=beta_*} c_rho exp(i Im rho u).
```
Here coincident zeros are combined into one nonzero coefficient, the coefficients are absolutely summable, P is real, and its constant coefficient b is nonnegative (zero if there is no real zero on that line). The error from other real parts tends to zero uniformly as the left endpoint of the locked window tends to infinity: keep a finite head with strictly smaller real parts and bound the rest by the absolute coefficient tail. This reasoning does not require a gap between the rightmost real part and the next real parts. The arithmetic comparison and explicit-formula remainder are used only where their previously proved power gap against exp(a u) is uniform.

**Claim.** There are h0>0, L>0 and c>0 depending on this rightmost zero series, but not on X or the start v, such that for any 0<h<=h0, sufficiently late, whenever [v,v+L+h] is inside the admissible interior,
```
max_{0<=k<=ceil(L/h)} S_X(v+kh) >= c exp(a v).
```
Thus one may fix a single sufficiently fine geometric ratio exp(h) and a finite number of sampled scales per window. Moving the start off a globally anchored grid costs at most one extra step if that version is desired.

## A finite trigonometric argument

Put C=sum |c_rho|>0 and W=sum |c_rho|^2>0. Take a real finite conjugation-symmetric head Q of P containing its constant term, retaining squared coefficient sum W_Q>=W/2 and with uniform tail at most W/(64C). Write its frequencies as distinct real numbers including 0 if present. Choose h0 so small that h0 times the absolute value of any difference of two head frequencies, or any individual head frequency, is at most pi. If there are no nonzero such numbers this requirement is vacuous.

For any such nonzero number t, a shifted sample average of exp(i t u) over M consecutive steps satisfies
```
|average| <= 2/(M |1-exp(i t h)|) <= pi/(M |t| h).
```
The estimate is uniform in the start. For the mean of Q use the nonzero individual frequencies; for the mean of |Q|² use the nonzero pairwise differences. Since both sets are finite, increasing L gives, for M=ceil(L/h)+1,
```
average Q >= b-W/(16C),
average |Q|² >= W_Q-W/4 >= W/4.
```
Since |Q|<=C, average |Q|>=W/(4C). Realness gives average Q_+=(average |Q|+average Q)/2>=3W/(32C). At least one sampled Q value is therefore at least 3W/(32C). Subtract the tail of P and the uniform o(1) to get a positive constant at the same sample; exp(a(v+kh))>=exp(a v). This proves the claim.

The small-step condition is imposed only on a finite coefficient head. There is no global lower bound on zero spacing, no need to exclude aliases involving the arbitrarily large ordinates in the tail, and no assumption of randomly or independently sampled primes. A prescribed coarse grid cannot be justified by this argument: the real exponential polynomial cos(2 pi u/h)-cos(4 pi u/h) vanishes on uh^{-1} integral despite being nonzero. This is a model aliasing warning, not a claim about conductor-23 ordinates.

An upper square-root-scale bound at these samples on arbitrarily late eligible locked windows would rule out an attained off-line rightmost real part. The number of necessary samples is fixed once h is fixed, but the proof does not extract a uniform explicit h from present zero data or address the unattained case. The original signed weighted split-prime estimate remains open.
