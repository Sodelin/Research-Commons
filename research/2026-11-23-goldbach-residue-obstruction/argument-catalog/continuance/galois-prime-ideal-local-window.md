# Galois prime-ideal windows and local Chebyshev deficits

This note gives a hand reduction for any finite Galois extension \(M/k\). It generalizes the conductor-\(23\) ideal-prime identity and accounts for ramified primes exactly.

For a number field \(F\), let \(B_F(x)=\sum_{\mathrm N\mathfrak a\le x}\Lambda_F(\mathfrak a)(x/\mathrm N\mathfrak a-1)\), where \(\Lambda_F\) is the ideal von Mangoldt weight. Set \(\psi_F(x)=\sum_{\mathrm N\mathfrak a\le x}\Lambda_F(\mathfrak a)\), \(c_F=\operatorname{FP}_{s=1}(\zeta'_F/\zeta_F)\), and \(G_F(x)=B_F(x)-x(\log x-1-c_F)\). For a fixed \(\lambda>1\), put
\[
D_{F,\lambda}(x)=G_F(x)-\lambda^{-1}G_F(\lambda x).
\]
The identity \((G_F(x)/x)'=(\psi_F(x)-x)/x^2\) holds away from its discrete norm discontinuities in the derivative, and \(G_F(x)/x\) is locally absolutely continuous. Thus
\[
D_{F,\lambda}(x)=x\int_x^{\lambda x}\frac{t-\psi_F(t)}{t^2}\,dt .
\tag{1}
\]
In particular, this difference is a local deficit with no normalization constant or tail at infinity.

## Exact splitting identity

Write \(g=[M:k]\). At a prime ideal \(\mathfrak p\) of \(k\), choose a place over it in \(M\), inertia group \(I_{\mathfrak p}\), and a Frobenius lift \(\tau_{\mathfrak p}\). For each \(j\ge1\) let
\[
u_{\mathfrak p,j}=\frac{1}{|I_{\mathfrak p}|}\sum_{i\in I_{\mathfrak p}}
 \mathbf1_{\tau_{\mathfrak p}^j i=1}.
\]
This is \(1/e_{\mathfrak p}\) if the residue degree \(f_{\mathfrak p}\) divides \(j\), and zero otherwise. In particular it is independent of the choice of place or lift. For \(v=\mathrm N\mathfrak p^j\) define the positive observable
\[
A_{M/k,\lambda}(x)=
 \sum_{\mathfrak p,j}\log\mathrm N\mathfrak p
 \left[u_{\mathfrak p,j}(x/v-1)_+
 +(1-u_{\mathfrak p,j})\lambda^{-1}(\lambda x/v-1)_+\right].
\]
There are \(g/(e_{\mathfrak p}f_{\mathfrak p})\) primes above \(\mathfrak p\) of norm \((\mathrm N\mathfrak p)^{f_{\mathfrak p}}\). Consequently \(g u_{\mathfrak p,j}\log\mathrm N\mathfrak p\) is exactly their combined Dedekind logarithmic-derivative weight at \(v\). This gives \(A_{M/k,\lambda}=\lambda^{-1}B_k(\lambda x)+[B_M(x)-\lambda^{-1}B_M(\lambda x)]/g\), hence
\[
 A_{M/k,\lambda}(x)-x\bigl(\log x-1-c_k+(1-g^{-1})\log\lambda\bigr)
 =\lambda^{-1}G_k(\lambda x)+g^{-1}D_{M,\lambda}(x).
\tag{2}
\]
All formulas include ramification. The same inertia average appears in the class-weighted Chebotarev function. [Grenié–Molteni, equation (1.1)](https://sites.unimi.it/molteni/research/papers-pdf/44-molteni-An_explicit_Chebotarev_density_theorem_under_GRH.pdf).

## Exact window criterion and a smooth variant

For any fixed \(\lambda>1\) and \(\kappa>0\), Dedekind RH for \(\zeta_M\) is equivalent to the following condition: for every sufficiently small \(\epsilon>0\) and every \(\eta>0\), there are arbitrarily large \(Y\) with
\[
 \int_Y^{Y^{1+\kappa}}\bigl(D_{M,\lambda}(x)\bigr)_+\,x^{-1/2-\epsilon}\,\frac{dx}{x}\le Y^\eta .
\tag{3}
\]
In particular, an upper bound \(O_\epsilon(x^{1/2+\epsilon})\) pointwise on arbitrarily late such windows suffices. Equation (3) retains the integral envelope of the pinned theorem.

To prove sufficiency, the Laplace transform of \(G_M(e^u)\) has the strip poles of \(-\zeta_M'/\zeta_M(s)/(s(s-1))\). The centering removes both poles at \(1\). Passing to \(D_{M,\lambda}(e^u)\) multiplies the transform by \(1-\lambda^{s-1}\), plus the entire term from the finite translation across \(u=0\). This multiplier is nonzero in the open strip and positive on its real segment. Thus all strip poles survive and the real positive residues stay positive. The remaining growth and measurability conditions follow from the corresponding properties of \(G_M\). Taking the positive part as the envelope, (3) is the hypothesis of the pinned generic Landau theorem with \(\theta=1/2+\epsilon\). Let \(\epsilon\) tend to zero and use the functional equation. [Pinned pole and envelope hypotheses](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauZeroFreeCriterion.lean#L15-L29) · [Pinned Landau theorem](https://github.com/Deicyde/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/landauWindow.lean#L83-L84).

For the converse use the conditional prime ideal theorem and (1). For fixed \(\lambda\) and \(x\ge100\) this gives
\[
 |D_{M,\lambda}(x)|\ll_\lambda \sqrt x\big[(1+\log x)\log |D_M|+[M:\mathbb Q](1+\log^2x)\big].
\]
The same dependence bounds \(|G_k(x)|\) under RH for \(\zeta_k\), by integrating \(\psi_k(t)-t\) against \(-x\,dt/t^2\) from \(x\) to infinity. The tail identity follows by partial summation of \(-\zeta_k'/\zeta_k\) and its Laurent expansion at \(1\). Thus, assuming RH for the base \(\zeta_k\), the centered positive observable in (2) can replace \(D_{M,\lambda}\) in (3), with the same sufficiency and converse. For abelian \(k/\mathbb Q\), the checked Dirichlet result supplies the base input. The new estimate for general \(M\) remains open. [Grenié–Molteni, Corollary 1.2](https://doi.org/10.1090/mcom3031).

The local comparison may also be smoothed over a fixed compactly supported probability distribution of \(v=\log\lambda\ge0\) with positive mass on \(v>0\). Averaging (1) gives a local integral weighted by the survival function of \(v\). Its pole multiplier is \(1-\int e^{(s-1)v}\,d\mu(v)\), which is nonzero for \(\Re s<1\) and is positive there on the real axis. Indeed the modulus of the integral is bounded above by \(\int e^{(\Re s-1)v}\,d\mu(v)<1\). The initial-interval corrections remain entire by compact support. The same criterion and converse therefore hold for these nonnegative decreasing log-scale kernels.


## A limitation for same-target Goldbach correlations

A finite model shows what the one-prime conclusions can leave undetermined. Fix an even congruence wheel \(Q\), including any fixed tested moduli, and for each unit residue \(r\bmod Q\) fix class probabilities \(w_r(C)\). These can be the genuine Frobenius class probabilities conditional on \(r\) from the compositum with \(\mathbb Q(\zeta_Q)\). Take a large \(N\) divisible by \(Q\). For a wheel-eligible \(x\) above a fixed \(x_0(Q)\), set \(p_x=Q/(\varphi(Q)\log x)\le1/4\), and set it to zero otherwise. Each pair \(\{x,N-x\}\) gets an independent uniform random number \(U\). In the first model select each endpoint when \(U\le p_x\) for that endpoint. In the second use the lower \(U\)-tail for one endpoint and the upper \(U\)-tail for the other. The second model has no selected complementary pair. In either model assign the colors independently of selection with probabilities \(w_r\).

Each coordinate has identical one-point marginal \(p_x w_r(C)\) in both models. For each residue and color, the expected prefix count is \(w_r(C)\operatorname{Li}(X)/\varphi(Q)+O_Q(1)\), by summing the decreasing function \(1/\log x\) on that progression. The count to \(X\) is a sum of at most \(X\) independent contributions from pairs that meet the prefix, with summands bounded by two. Hoeffding's inequality and a union bound over integer \(X\le N\) and the finitely many tested residue-color categories show that, with probability bounded away from zero, all prefix discrepancies are \(O_Q(\sqrt{X\log(2X)})\). To see uniformity in \(N\), choose the tolerance constant so the summed failure bound \(2\sum_{X\ge1}(2X)^{-A}\) times the number of categories is less than \(1/4\). Partial summation gives the corresponding logarithmically weighted prefix and interval estimates.

In the first model the expected number of complementary pairs is \(\sum_{\{x,N-x\}}\min(p_x,p_{N-x})\asymp_Q N/\log N\). For the lower bound restrict to \(N/3<x<N/2\) on eligible residues, and for the upper bound use \(\max(x,N-x)\ge N/2\). The pair events are independent, so with probability tending to one the number is of this order. Therefore the two models have realizations with the same stated one-prime estimates and with, respectively, \(\asymp_Q N/\log N\) and zero same-target pairs. This is a limitation of finite marginal estimates on their own. It makes no claim of logical independence for actual primes or for the full family of GRH statements. Moving from (3) or its Chebotarev consequences to the exact signed Goldbach remainder would still require a theorem for linked summands.

## Two rescalings remove the smooth-base assumption

With the full arithmetic base term \(\lambda^{-1}B_k(\lambda x)\) in (2), one scale suffices unconditionally as a reduction: \(A_{M/k,\lambda}(x)-\lambda^{-1}B_k(\lambda x)+(x/g)\log\lambda=D_{M,\lambda}(x)/g\). With only the smooth main term, two fixed distinct choices of \(\lambda>1\) suffice to deduce RH for both fields from their versions of (3). At a strip zero \(z\) of either function, the pole numerator of the centered transform is
\[
 m_M(z)/g+\lambda^{z-1}\bigl(m_k(z)-m_M(z)/g\bigr),
\]
before the common factor \(-1/[z(z-1)]\). The multiplicities are nonnegative. This numerator is positive at real strip zeros and can vanish at a complex strip zero for at most one \(\lambda\), since \(|\lambda^{z-1}|\) decreases strictly. Apply Landau separately to each rescaling, taking the strip poles surviving in that transform. Their union contains all the strip zeros of both fields. The converse follows under RH for both fields by the same smoothed bounds.
