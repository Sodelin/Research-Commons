# The retained base cutoff tightens the explicit Goldbach Type II cap

**Unconditional hand refinement at sufficiently large powers of two.** Use the positive Type II stress strip \(L/20\le\log(u/v)\le L/10\), \(L=\log N\), all original masks and signs, and keep the already retained base condition \(\ell w>N^{13/40}\). Group and take negative parts exactly as in the pinned polynomial edge bound. Write \(p=P^-(d/w)\), \(J=3/8-(\log2)/2\), and \(\Pi=\prod_{r>2,\ r\ {\rm prime}}(1+1/(r(r-1)))\). Suppose \(0<\alpha\le1/40\) is fixed and the fixed Selberg square is one on the slice \(p>N^\alpha\). The doubled negative charge on this slice is bounded by \(N(C_{\mathrm{base}}(\alpha)+o(1))\), where
\[
\begin{split}
 C_{\mathrm{base}}(\alpha)
 &=J\Pi\left[
 \frac47\left(K I_0(\alpha)+2I I_1(\alpha)\right)
 +\frac5{14}\left(\frac{69}4I-\frac5{16}\right)\right],\\
 I&=\log(36/35),\qquad K=\frac{51}{40}I-\frac1{40},\\
 I_0(\alpha)&=\frac1\alpha-\frac{136}5,\qquad
 I_1(\alpha)=\log\frac1{40\alpha}+\frac15+\frac45\log\frac{32}{25}.
\end{split}
\tag{1}
\]
At \(\alpha=1/100\), the doubled charge is at most \(N/45\), improving the previous \(N/40\) bound on this retained-base support. At \(\alpha=1/200\) it is at most \(N/21\). At \(\alpha=17/5000\), the coefficient is less than \(7/100\). [Pinned exact signed edges, CRT, and explicit integrals](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md) · [Pinned rough harmonic refinement](https://github.com/Sodelin/Research-Commons/blob/bc292106d03065e910b8dc6d2bbca1589313169b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-harmonic-cap.md).

## Edge geometry with actual \(\ell\)

Let \(x=\log\ell/L\in(1/10,1/8]\), \(t=\log p/L\), and take the pinned signed pairs with \(d/w=pab\). On the edge where \(s=b\), the admitted term has \(v=wb\) and \(\log(u/v)\ge L/20\), so \(\log v/L\le 19/40-x/2\). Since \((\log w)/L>13/40-x\), the bound on \(b\) is now
\[
 b\le N^{c_-(x)},\qquad c_-(x)=\frac3{20}+\frac x2 .
\]
On the edge with \(s=pb\), the admitted \(\rho=\log(u/v)\) is at least \(\max(L/20,L/10-2\log p)\). If \(t\le1/40\), this gives \((\log v)/L\le9/20-x/2+t\). Subtracting the exponents of \(p,w\) gives \(b\le N^{1/8+x/2}\). If \(t\ge1/40\), the bound \(19/40-x/2\) on \(v\) instead gives \((\log b)/L\le 3/20+x/2-t\le1/8+x/2\). Thus the second exponent is \(c_+(x)=1/8+x/2\), and \(c_+(x)+c_-(x)=11/40+x\). These are inequalities on the exact signed edges, before the positive upper count.

Use the pinned harmonic bound \(\mathcal H(c_\pm(x)/t)\le(4/7)(c_\pm(x)/t+1)\) for squarefree \(b\). The fixed-exponent harmonic convergence is uniform here by the same fixed mesh argument, varying the upper exponent over a compact interval as well as the lower exponent. Keep \(\log d\ge(1-x)L-B\log L\) after the pinned trim. The prime-\(\ell\) harmonic sum with this denominator tends to \(dx/(1-x)\) on \(1/10\le x\le1/8\), by Mertens and partial summation. Hence the two \(\ell\) integrals are
\[
 \int_{1/10}^{1/8}\frac{dx}{1-x}=I,
 \qquad
 \int_{1/10}^{1/8}\frac{c_+(x)+c_-(x)}{1-x}\,dx=K.
\]
The edge \(w\)-window and auxiliary roughness sieve still give \(e(t)/d(t)\), where \(e(t)=\min(t,1/40)\) and \(d(t)=\min(t,1/32)\). Integrating the least prime with measure \(dt/t\) therefore yields the first term in (1), using the pinned \(I_0,I_1\) integrals. The exact CRT error powers are unchanged.

## Direct charge above \(N^{1/25}\)

Use the pinned direct cap on this slice. For actual \(\ell\), the retained base and \(\rho\ge L/20\) give \(s=v/w\le N^{3/20+x/2}\). With \(\sigma=1/25\), replace its squarefree rough harmonic mass by
\[
 \frac47\left(\frac{3/20+x/2}{\sigma}+1\right)+o(1).
\]
The direct prime-\(w\) log width remains \(L/40+o(L)\) and the sieve denominator uses \(\sigma L\). Integrating \(x\) as above yields \(J\Pi(40\sigma)^{-1}(4/7)((69/4)I-5/16)\), the second term in (1). The same external factor two is included throughout. [Pinned direct rough cap and CRT](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-rough-negative-cap-2234z.md).

For the numerical enclosures use \(I\le7247/257250\), the alternating upper truncation for \(\log(1+1/35)\), \(J<57/2000\) and \(\Pi<34/25\). As in the pinned bound, \(I_1<178/125\) at \(\alpha=1/100\) and \(I_1<531/250\) at \(\alpha=1/200\). At \(\alpha=17/5000\), use \(I_1<303/125\). Exact rational arithmetic gives upper enclosures \(0.021782535\), \(0.046838041\), and \(0.069971919\), respectively. The strict slack absorbs the \(o(1)\) terms. This refinement applies to the retained-base strip with the same fixed square and original signs.


In the separately chosen equivalent expansion with \(\kappa=23/500\), \(\delta=17/5000\), and lower Vaughan cutoff \(U=N^{1/100}\), this retained base is present. Its forced-square charge below \(z=N^\delta\) is less than \(3N/5000\). The upper coefficient in (1) at \(\alpha=\delta\) was checked as the exact fraction \(2100032191539/30012500000000<7/100\). Together these give a doubled charge below \(71N/1000\) for its entire positive stress strip at sufficiently large powers of two. The other signed rows for that expansion still require bounds with its own square. The \(N/45\) and \(N/21\) bounds above also apply directly to the original square whenever their respective thresholds are beyond its support or level. [Pinned separate equivalent expansion and its low-prime bound](https://github.com/Sodelin/Research-Commons/commit/3894f49a36cb7cc752bdf1002b8f465253d3fafe)
