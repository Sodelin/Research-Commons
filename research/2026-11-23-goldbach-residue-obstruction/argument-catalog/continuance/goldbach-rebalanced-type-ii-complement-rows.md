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

## Individual estimates on the two complementary ratios

On the upper row \(\rho>L/10\), the doubled sum of absolute grouped weights is at most \(.041N\) for all sufficiently large powers of two. On the lower row the signed weight satisfies \(|2T_<|<.115N\). These estimates keep the same parameters, base, signs and strict partition.

For \(T_>\) put \(p=P^-(d/w)\) as before. At fixed \(q,h,\ell,w\) and fixed pair \(d/w=pab\), the greater ratio belongs to the allocation \((u,s)=(pa,b)\). The other allocation is \((a,pb)\). The strict cut \(\rho>L/10\) leaves just one unmatched possibility, with exact sign \(-\mu(a)\) and
\[
 L/10<\rho\le L/10+2\log p.
\]
An allocation that remains above \(L/10\) meets the \(u\) threshold. Every other group condition stays fixed. For \(p\le z\), the forced-prime proof applies to this single moving edge. Here \(x=\min(u,v)=v>N^{1/5}\) and \(\ell x\le N^{41/80}\). The original stress proof bounds the magnitude and the number of dyadic \(x\) scales. Its CRT transfer is still power-saving with \(\ell x\le N^{41/80}\). The harmonic floor error is \(O(N^{1+2\kappa+\delta-1/5+o(1)})=O(N^{.8954+o(1)})\), using \(x>N^{1/5}\). Hence its doubled charge is at most the previous \(.0006N\), with the same strict rational enclosure.

For the rest put \(\delta=17/5000\), \(\beta=7/100\), \(g=41/1000\), and \(x=\log\ell/L\in(1/10,1/8]\). Set
\[
 c(x)=\tfrac18+\tfrac x2,\qquad
 I=\log(36/35),\qquad
 K=\tfrac58 I-\tfrac1{80},\qquad
 K_2=\tfrac{25}{64}I-\tfrac{129}{12800}.
\]
These are the integrals of \(1,c(x),c(x)^2\) against \(dx/(1-x)\) over the prime-\(\ell\) exponent band, respectively.

On \(z<p\le N^\beta\), retain the exact unmatched allocation \(s=b\) and put \(M=\ell p w b\). From \(\rho>L/10\) we have \(v\le N^{9/20-x/2}\). The base \(\ell w>N^{13/40}\) gives \(b\le N^{c(x)}\), and \(M\le N^{41/80+\beta}\). The original square equals one. At fixed \(\ell,p,w,b\), sieve \(a=(N-qh)/M\) with the auxiliary square of level \(\min(p/2,N^g)\) and section density as in the pinned edge count. Its indices avoid the prime factors of \(M\), since those are \(p\) or greater. For any opened pair, count the unit hyperbola at the combined odd modulus, handling the factor \(2\) by the three parity choices when necessary. Thus the CRT errors at a fixed \(M\) are bounded by
\[
 N^{o(1)}\big(N^{3g}M^{1/2}+N^{2g}H/M^{1/2}\big).
\]
The modulus multiplicities are divisor-bounded, as in the pinned edge count. Summing up to \(N^{41/80+\beta}\) gives exponents \(.99675\) and \(.87325\), respectively. The main reciprocal sieve factor is \((1+o(1))\Pi/(2L\min(t,g))\) at \(t=\log p/L\in[\delta,\beta]\). At fixed \(\ell,p,b\) the edge permits \(w\) in a log interval of width \(\log p+O_B(\log L)\) after the standard endpoint trim. Thus \(\sum_w(\log w)/w\le(1+o(1))tL\). The squarefree \(b\) has all prime factors greater than \(p\), so its reciprocal size is at most \((4/7)(c(x)/t+1)+o(1)\). The original weight denominator yields \(\log d\ge(1-x)L-B\log L\). Using the pinned log-weight integral \(J\) for \(q,h\), and keeping the original external factor two, bounds the doubled charge by \(N(C_{\rm edge}+o(1))\), where
\[
 C_{\rm edge}
 =J\Pi\frac47
 \left[K\left(\frac1\delta-\frac1g+\frac1g\log\frac\beta g\right)
 +I\left(\log\frac g\delta+\frac{\beta-g}{g}\right)\right].
\]
The two \(t\) integrals here are respectively \(\int_\delta^\beta dt/(t\min(t,g))\) and \(\int_\delta^\beta dt/\min(t,g)\). This follows directly from the prime harmonic measure \(dt/t\), the \(w\) factor \(tL\), the displayed \(b\) upper bound and the reciprocal sieve. [Pinned signed-edge count and auxiliary square](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md) · [Pinned rough harmonic law](https://github.com/Sodelin/Research-Commons/blob/bc292106d03065e910b8dc6d2bbca1589313169b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-harmonic-cap.md).

On \(p>N^\beta\) bound all termwise absolute weights in this row. Set \(M=\ell w s=\ell v\le N^{41/80}\), use the auxiliary square at level \(N^\beta\) for the \(N^\beta\)-rough factor \(u\), and count at the combined odd modulus as above. The opened CRT powers are \(.97875\) and \(.89625\). The sifting primes are coprime to \(M\), since \(\ell,w>N^\beta\) and \(s\) is \(p\)-rough. For fixed \(\ell,s\), the \(w\) harmonic log window has width at most \(c(x)L\), from the same upper bound on \(v\) and the retained lower base. The \(s\) reciprocal size is at most \((4/7)(c(x)/\beta+1)+o(1)\). The sieve main factor is \((1+o(1))\Pi/(2\beta L)\). The same \(\ell\) integration now bounds this doubled charge by \(N(C_{\rm dir}+o(1))\) with
\[
 C_{\rm dir}=J\Pi\frac47\left(\frac{K_2}{\beta^2}+\frac K\beta\right).
\]

Use \(I\le7247/257250\), \(J<57/2000\), \(\Pi<34/25\), \(\log(70/41)<27/50\), and \(\log(205/17)<5/2\). The last two strict inequalities follow from the positive exponential series through degree seven. Exact rational arithmetic gives \(C_{\rm edge}\le10459343953/307628125000\) and \(C_{\rm dir}\le136527901/23529800000\) as upper enclosures. Adding the low-prime \(.0006\) gives the strict enclosure \(4872122457201/120590225000000<.041\); the asymptotic errors fit the slack. Finally, \(|2T_<|\le|2S|+|2T_0|+|2T_>|+o(N)\) by exact equivalence. The more precise upper enclosures \(.003876,.070546498,.040402301\) sum to less than \(.115\). These individual bounds are valid for the expanded partition. The complete narrow-band charge remains the direct bound on \(S\).
