# The two complementary ratio rows in the rebalanced Goldbach expansion

**Unconditional hand proof at each sufficiently large power of two.** Keep \(U=N^{1/100}\), \(V=N^{1/5}\), \(D_s=N^{23/500}\), \(z=N^{17/5000}\), and the retained base \(\ell w>N^{13/40}\) from the exact rebalanced expansion. Keep its original odd-\(m\) paired \(q<h\) support, actual prime \(N^{1/10}<\ell\le N^{1/8}\), strict divisor cutoff, endpoint tests, and \(m\) masks. Use the same optimal square \(W_N\) and the exact opened signed weights. Let \(T_<,T_0,T_>\) be the expanded terms with \(\rho=\log(u/v)<L/20\), \(L/20\le\rho\le L/10\), and \(\rho>L/10\), respectively. Both expanded endpoint parities belong to each row. Let \(S\) be the original prime-tested paired signed weight on this same prime-\(\ell\) band. The equivalence proves
\[
 S=T_<+T_0+T_>+O_A(N/L^A).
\]
With the external factor two from the original semiprime endpoint row, one has
\[
 |2S|<.004N,\qquad |2T_0|<.071N,\qquad
 |2(T_<+T_>)|<.075N.
\]
Thus the two complementary expanded rows have a joint signed bound under exactly the same parameters. The individual signed values of \(T_<\) and \(T_>\) remain unspecified by this deduction. For the full narrow band, the direct \(.004N\) charge covers all three rows together. [Exact equivalent expansion and parameters](https://github.com/Sodelin/Research-Commons/blob/3894f49a36cb7cc752bdf1002b8f465253d3fafe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rebalanced-expansion.md) · [Retained-base cap](https://github.com/Sodelin/Research-Commons/blob/483ffd44dc87b1ca58b1b22c9a721f242699ebfe/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-base-aware-rough-cap.md).

## A direct upper count on the narrow prime-tested band

The prime-tested endpoints are \(n=\ell d\) with \(d>D_0>H\) prime. The signed paired weight is \(F(m)\mu(h)\log(h/q)\log\ell\) for \(q<h\), \(\mu(m)=-1\). For its upper count drop the sign, the \(m\) mask and the arithmetic parity test on \(\mu(m)\). At fixed odd prime \(\ell\) count the unit hyperbola \(qh=N\bmod\ell\) in the square-root block with continuous nonnegative weight \((\log(h/q))_+\). Impose the candidate prime \(d=(N-qh)/\ell\) by an auxiliary one-dimensional optimal Selberg square of level \(D_*=N^{1/4}\), omitting the prime \(\ell\) from its support. Every candidate prime \(d\) exceeds the level, so the square equals one there.

The local densities for an auxiliary sieve prime \(p\ne\ell\) are \(3/4\) at \(p=2\) and \((p-1)/p^2\) at odd \(p\). The pinned quadratic minimizer has coefficients of magnitude at most one and main value
\[
 Q_\ell=(1+o(1))\frac{\Pi}{2\log D_*},
 \qquad
 \Pi=\prod_{p>2,\ p\ {\rm prime}}\left(1+\frac{1}{p(p-1)}\right)
\]
uniformly for this band. Indeed its unrestricted denominator is \(2\Pi^{-1}\log D_*+O(1)\) by the pinned convolution with \(1/a\). Omitting \(\ell\) changes it by at most \(b(\ell)\sum_{a\le D_*/\ell}b(a)=O(L/\ell)\), where \(b(\ell)=g(\ell)/(1-g(\ell))=O(1/\ell)\). [Pinned one-dimensional Selberg denominator](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-rough-negative-cap-2234z.md#main-term-with-its-constant).

For each opened pair of indices use the unit hyperbola at the combined odd modulus \(\ell c_{\rm odd}\), where \(c=[a,b]\), \(c_{\rm odd}\) is its odd part, and \((c,\ell)=1\). Since \(N=2^k\), the odd modulus is coprime to \(N\). If \(2\mid c\), count the three allowed parity pairs for \(q,h\) separately, using the shift and scaling by \(2\) in their progressions. The resulting translated unit-hyperbola bound gives error
\[
 O\!\left(N^{o(1)}\big((\ell c)^{1/2}+H/(\ell c)^{1/2}\big)\right).
\]
The grids for the continuous weight cost polylogarithmic factors and converge from above to
\[
 J=\int_{1/2}^1\int_x^1\log(y/x)\,dy\,dx=\frac38-\frac{\log2}{2}.
\]
The first opened error uses \(\sum_{a,b\le D_*}[a,b]^{1/2}\le D_*^3\). For the second use
\[
 \sum_{a,b\le D_*}[a,b]^{-1/2}
 \le\sum_{c\le D_*^2}\tau(c)^2c^{-1/2}=D_*^{1+o(1)}.
\]
Summing over \(\ell\le N^{1/8}\) gives \(N^{15/16+o(1)}+N^{13/16+o(1)}\), including the log weights. This keeps both parts of the rectangular completion below \(N\). [Pinned rectangular unit-hyperbola bound](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md#count-at-a-fixed-composite-modulus).

The main term is at most \(N(J+o(1))Q_\ell/\ell\) at each \(\ell\), using \(\varphi(\ell)/\ell\le1\). Since \(\sum_{\ell\ \mathrm{prime}}\log\ell/\ell=(1/40+o(1))L\), the doubled prime-tested absolute weight is at most
\[
 \left(\frac{J\Pi}{10}+o(1)\right)N.
\]
Using \(J<57/2000\) and \(\Pi<34/25\), its coefficient is at most the rational enclosure \(969/250000=.003876<.004\) before the \(o(1)\) term. This count makes no change to the prime-tested band or the selected \(m\) masks used to define \(S\).

## The stress cap already bounds absolute grouped weight

Fix a group \((q,h,\ell,w)\) and its least prime \(p=P^-(d/w)\). In the part \(p\le z\), the rebalanced proof pairs allocations of \(p\), with identical \(W_N(n)\) and opposite \(\mu(u)\). Its upper count bounds the **absolute** weight of the surviving terms on both edges of the closed stress interval. The same statement applies to the pinned edge proof on \(z<p\le N^{1/25}\), and the retained-base harmonic refinement changes only positive counts. In each case the absolute value of the exact signed group subtotal is at most the sum of those surviving absolute weights. For \(p>N^{1/25}\), the direct bound instead counts the raw termwise absolutes, which again dominate the grouped absolute value. Thus the stated numerical bounds apply to \(2\sum_{\rm groups}|G_{q,h,\ell,w}|\), as well as to its negative mass. Numerically the low portion has explicit upper enclosure \(21875/38071296<.0006\), and the retained-base upper enclosure for the high portion is \(2100032191539/30012500000000<.07\). Their sum is strictly below \(.071\), with slack for the asymptotic errors.

Finally, the complement identity is exact with the two strict inequalities defining \(T_<,T_>\). It follows that \(2(T_<+T_>)=2S-2T_0+O_A(N/L^A)\). The strict displayed enclosures give the claimed \(.075N\) bound, and the external factor two is included once. The original even-\(m\) semiprime cells and the prime-\(\ell\) ranges outside the narrow band belong to the original-level ledger. The other model and actual outer-window rows also retain their original supports. The present deduction accounts for the three rebalanced Type II ratios solely within this narrow original odd-\(m\) semiprime band.
