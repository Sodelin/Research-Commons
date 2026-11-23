# Squarefree reduction of the actual separated \(S_3\) covariance

Keep the locked cutoffs \(U=\lfloor Y^u\rfloor\), \(P=Y^\alpha\), \(H=Y^{u+\kappa}\), with \(u+\alpha<1\), \(0<\kappa<1-u-\alpha\) and \(X=Y^{1+o(1)}\). Use the original \(g_P(v-\log h)\), \(b_h=\beta_U(h)/\sqrt h\) and \(z=(\log X)^2\). The separated covariance is already restricted to
\[
 U<h<k\le H,\qquad k-h>H_0,\qquad (h,k)=1,
 \qquad P^-(h),P^-(k)>z .
\]
Here \(H_0=X^{o(1)}\). One may add \(\mu^2(h)=\mu^2(k)=1\). The difference of the two actual signed covariance sums is below the off-line exponent \(2\beta_*-1\) by a fixed power when \(\beta_*>1/2\), and is \(O_\varepsilon(X^\varepsilon)\) when \(\beta_*=1/2\). No product term is moved to a different pair support. [Divisibility-lane estimates and exact rough reduction](https://github.com/Sodelin/Research-Commons/commit/cee389512c24de3ea6d0a90bb3c82f3b0c1e7ecc)

## Squarefree projection in the signed companion weights

Write
\[
 S_d(v)=\sum_{\substack{U<h\le H\\ d\mid h,\ P^-(h)>z}}
               b_hg_P(v-\log h).
\]
The prior exact rough reduction supplies, for \(d>1\),
\[
 |S_d(v)|\ll X^{\beta_*-1/2-c}d^{-\sigma},\quad
 c>0,\ \sigma>1/2\qquad(\beta_*>1/2).
\tag{1}
\]
At \(\beta_*=1/2\) and every prescribed tolerance \(\varepsilon>0\), its analogue is \(O_\varepsilon(X^\varepsilon d^{-\sigma_\varepsilon})\), with \(\sigma_\varepsilon>1/2\). These estimates use the actual Artin inverse coefficients and the same strictly cut off split-prime measure.

Let \(S_d^{\rm sf}\) be \(S_d\) with the added squarefree restriction. The exact squarefree identity gives
\[
 S_d^{\rm sf}(v)=\sum_{a\ge1}\mu(a)S_{\operatorname{lcm}(d,a^2)}(v).
\tag{2}
\]
All sums are finite on the original companion support. At \(d=1\),
\[
 S_1^{\rm sf}-S_1=\sum_{a>1}\mu(a)S_{a^2}.
\]
The \(a>1\) terms are bounded by (1), with the absolutely convergent weight sum \(\sum_{a>1}a^{-2\sigma}\). Thus the aggregate signed companion contribution with at least one repeated prime factor has a strict off-line gap, or a subpower bound at the critical line.

For \(d>1\), the lane \(S_d^{\rm sf}\) vanishes unless \(d\) is squarefree. In that case (2) and (1) give the same \(X\)-power bound and the \(d\)-weight
\[
 \begin{split}
 \sum_{a\ {\rm squarefree}}\operatorname{lcm}(d,a^2)^{-\sigma}
 &=d^{-\sigma}
     \prod_{p\nmid d}(1+p^{-2\sigma})
     \prod_{p\mid d}(1+p^{-\sigma})\\
 &\ll_{\sigma,\delta}d^{-\sigma+\delta}
 \end{split}
\]
for every \(\delta>0\). The first product converges because \(2\sigma>1\), and the second is subpower by separating the finitely many small primes from the factors bounded by \(p^\delta\). Choose \(\delta<\sigma-1/2\). The new weights are square summable in \(d\), including at the critical line after making the corresponding choice with \(\sigma_\varepsilon\).

The all-pair moments differ by \(\int ((S_1^{\rm sf})^2-S_1^2)\,dv\). This has the same strict off-line gap in the squared scale by the bound on \(S_1^{\rm sf}-S_1\) and the known envelope \(S_1=O_\varepsilon(X^{\beta_*-1/2+\varepsilon})\). Its critical-line bound is subpower. For each of the two all-pair moments, the signed noncoprime contribution is exactly \(-\sum_{d>1}\mu(d)\int S_d(v)^2\,dv\), with \(S_d^{\rm sf}\) used in the squarefree case. The squared \(d\)-weights just proved make both noncoprime contributions smaller by fixed powers, or subpower. Finally the absolute short-gap estimate applies unchanged to either support, since removing terms cannot enlarge that absolute estimate. This proves the comparison for the two exact separated coprime covariance sums.

## Exact Frobenius sign of a surviving pair

For a squarefree \(h>U\), multiplicativity gives the exact formula
\[
 \beta_U(h)=\mu_L(h)C_U(h),\qquad
 C_U(h)=\sum_{\substack{r\mid h\\r<h/U}}\mu(r).
\]
It follows by writing \(h=mr\) in \(\mu_{L,>U}*a\), using \(\mu_L(m)=\mu(m)a(m)\), and substituting \(\mu(m)=\mu(h)\mu(r)\). The inequality \(r<h/U\) is strict. All ramified primes are excluded from the rough band for sufficiently large \(X\). Any transposition prime dividing \(h\) forces \(a(h)=0\) and thus \(\beta_U(h)=0\). At split primes \(\mu_L(p)=-2\), and at three-cycle primes \(\mu_L(p)=1\). Consequently each nonzero retained pair has \(hk\) squarefree, made up entirely of split and three-cycle primes, and has signed coefficient
\[
 \beta_U(h)\beta_U(k)
 =(-2)^{\,\#\{p\mid hk:\ p\ {\rm splits\ completely}\}}\,
       C_U(h)C_U(k).
\]
The two finite cutoff sums are still on the actual individual factors \(h\) and \(k\). This identity leaves both their signs and the original shifted-prime kernel in the residual covariance. Its subpower upper bound remains open. These are hand arguments.

## A conditional signal on the actual prime–prime companion pairs

Suppose \(\beta=\beta_*>1/2\) is attained at finitely many distinct zeros \(\zeta\in Z_\beta\), and that all other zeros have real part at most \(\beta-g\) for a fixed \(g>0\). Let \(m_\zeta\) be the multiplicity. Under this additional spectral assumption, the actual surviving subregion with both \(h\) and \(k\) prime has separated covariance of order \(X^{2\beta-1}\). In particular a fixed power narrower companion band still has a prime–prime subregion with the same off-line exponent. [Finite top-line prime-density calculation](https://github.com/Sodelin/Research-Commons/commit/e45ea21dfa688721ac46d1c0814820321d6b89e1)

Define
\[
 S_{\rm p}(v)=\sum_{\substack{U<q\le H\\q\ {\rm prime}}}
                   b_q g_P(v-\log q)
             =-x^{-1/2}\sum_{\substack{U<q\le H\\q\ {\rm prime}}}
                     a(q)E_P(x/q),\qquad x=e^v.
\]
The second equality uses the exact prime coefficient \(\beta_U(q)=-a(q)\). Then uniformly for \(\log Y\le v\le\log X\),
\[
 S_{\rm p}(v)=
 -\frac{\log((u+\kappa)/u)}{3}
    \sum_{\zeta\in Z_\beta}
       m_\zeta^2 H_B(\zeta)e^{(\zeta-1/2)v}
      +O\left(\frac{e^{(\beta-1/2)v}}{\log Y}\right).
\tag{3}
\]
Indeed the gap permits truncated Perron for the prime trace, so its cumulative function is
\(-\sum_{\zeta\in Z_\beta}m_\zeta t^\zeta/\zeta+O(t^{\beta-c})\)
for some \(c>0\). Verified Dirichlet centering gives the same expression divided by \(3\) for the split-prime logarithmic measure, up to a strict lower power. These give the model densities \(-\tfrac13\sum m_\zeta t^{\zeta-1}\,dt\) in the outer \(p\) variable and \(-\sum m_\zeta t^{\zeta-1}\,dt/\log t\) in the companion variable. Their errors under the original hard cutoffs retain a fixed off-line gap by double Stieltjes integration against the finite mixed variation of \(K_B\) in logarithmic coordinates. In the error factor a log variable is at least \(\min(u,\alpha)\log Y\), while the two variables sum to \(\log x+O_B(1)\) on the support of that variation. The upper cutoff \(H\) only makes the companion cumulative functions constant past \(H\), which preserves the same bound.

For the model term put \(s=\log q\) and \(w=\log(pq/x)\). Since \(P H\le Y^{u+\alpha+\kappa}\) with \(u+\alpha+\kappa<1\), the constraint \(p>P\) allows the entire interval
\([u\log Y,(u+\kappa)\log Y]\) for \(s\), whenever \(w\ge-c'\log Y\) for a fixed \(c'>0\). The remaining \(w\) tail is exponentially small in \(\log Y\). Equal top ordinates give the integral \(\int ds/s=\log((u+\kappa)/u)\). Distinct top ordinates give \(O(1/\log Y)\) by a single integration by parts in \(s\). Integration in \(w\) produces \(H_B(\zeta)\). The signs and the \(1/3\) normalization give (3).

Let \(\mathcal C_{\rm pp}(Y,X)\) denote the original signed separated covariance with the extra condition that \(h,k\) are both prime. Such distinct primes are coprime and all are already in the rough, squarefree band. Therefore \(\mathcal C_{\rm pp}\) is \(\int S_{\rm p}(v)^2\,dv\) with precisely the original diagonal and short-gap pairs removed. Their total absolute cost is a fixed lower power by the known short-gap bound for \(H_0=X^{o(1)}\). Equation (3) gives
\[
 \mathcal C_{\rm pp}(Y,X)=
 \frac{\log^2((u+\kappa)/u)}9
 \int_{\log Y}^{\log X}
 \left(\sum_{\zeta\in Z_\beta}
       m_\zeta^2 H_B(\zeta)e^{(\zeta-1/2)v}\right)^2dv
 +O\left(\frac{X^{2\beta-1}}{\log Y}\right).
\]
The finite trigonometric polynomial after dividing its summand by \(e^{(\beta-1/2)v}\) is real and nonzero. Its mean square is bounded below uniformly on all intervals of sufficiently large fixed length by separating the finitely many distinct ordinates. On the last such interval the exponential factor is comparable to \(X^{2\beta-1}\). Thus for \(\log X-\log Y\to\infty\), the same lower bound holds for the displayed covariance. This is a conditional obstruction in an exact surviving pair sector. It supplies no square-root estimate or further zero exclusion.
