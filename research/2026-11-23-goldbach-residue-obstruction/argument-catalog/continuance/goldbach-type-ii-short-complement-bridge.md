# A fixed-square bridge on the short complementary factor in Goldbach Type II

**Unconditional hand proof at each sufficiently large power of two.** Use the exact positive stress interval \([L/20,L/10]\), \(L=\log N\), in the pinned paired odd-\(m\) Type II expansion. In particular \(q h+\ell u w s=N\), \(v=ws\), \(d=uv>D_0\) strictly, \(q<h\) are in the original square-root block, \(m=qh\) and \(n=N-m\) are squarefree, and the original \(m\) masks, \(Y_0\)-roughness, prime band \(N^{1/10}<\ell\le N^{1/8}\), prime \(w>N^{1/5}\), and previously retained base cuts all stay in force. Keep the original optimal square \(W_N(n)\), whose prime support is at most \(z=N^\delta\) and whose level is \(N^\kappa\). The exact weight is
\[
 F(m)W_N(n)\mu(h)\mu(u)\log(h/q)\frac{\log\ell\log w}{\log d}.
\]
[Pinned stress interval, grouped signs, and coefficient](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md).

At fixed \(q,h,\ell,w\), let \(p=P^-(d/w)\). For each admitted allocation \(us=d/w\), let \(b=s/p\) if \(p\mid s\) and \(b=s\) otherwise. Fix \(C\ge1\) and restrict the subtotal \(G^{(C)}_{q,h,\ell,w}\) to \(b\le p^C\). The restriction shares both allocations of \(p\), so it is imposed before grouping. Define \(J=3/8-(\log 2)/2\), \(\Pi=\prod_{r>2,\ r\text{ prime}}(1+1/(r(r-1)))\), and
\[
 \mathcal H(C)=1+\sum_{j\ge1}\frac1{j!}
       \int_{\substack{x_i\ge1\\\sum x_i\le C}}
              \frac{dx_1\cdots dx_j}{x_1\cdots x_j}.
\]
For fixed \(\delta\le\alpha<\beta\le1/200\), the doubled negative weight of these subgroups satisfies
\[
 2\sum_{\substack{q,h,\ell,w\\N^\alpha<p\le N^\beta}} (G^{(C)}_{q,h,\ell,w})_-
 \le N\left[2J\Pi\,\mathcal H(C)\log(36/35)\log(\beta/\alpha)+o(1)\right].
 \tag{1}
\]
Here \(x_-=\max(0,-x)\). In particular \(\alpha=\delta,\ \beta=1/200\) covers the entire previously unbounded least-prime interval on this restricted support. When \(C=1\), \(b=1\), so the paired choices have \(s=1\) and \(s=p\). When \(1\le C\le2\), \(\mathcal H(C)=1+\log C\). The coefficient in (1) grows logarithmically as \(\alpha\) decreases. The unrestricted polynomial edge bound instead grows like \(1/\alpha\). The complementary part \(b>p^C\) still needs a same-target bound.

## The exact difference and its upper count

Trim \(n<N/L^B\) at arbitrary logarithmic cost by the pinned fixed divisor moments. Fix the group and write \(d/w=p a b\), with \(a,b\) free of primes at most \(p\), using squarefreeness. The two choices are \((u,s)=(a,pb)\) and \((pa,b)\). Their signs in the \(u\) summand are \(\mu(a)\) and \(-\mu(a)\). With \(R=\log(a/(wb))\), their ratios are \(R-\log p\) and \(R+\log p\). All other weights and each group-level cutoff coincide, including the condition \(b\le p^C\). A choice on the stress interval automatically meets \(u>N^{1/5}\) on the trimmed range, and the \(v\) cutoff follows from \(w\). Thus the signed pair is the fixed weight times
\[
 \mu(a)\left(\mathbf1_{[L/20+\log p,L/10+\log p]}(R)
              -\mathbf1_{[L/20-\log p,L/10-\log p]}(R)\right).
\]
The surviving edges each have log width \(2\log p\), since \(\beta\le1/200\), with endpoints fixed by these closed intervals. The negative grouped weight is bounded by the sum of the absolute surviving weights. This uses the same original signs in each expanded endpoint parity.

All prime factors of \(n\) exceed \(z\), so the fixed \(W_N(n)=1\) on this slice. At fixed \(\ell,w,p,b\), put \(M=\ell w p b\), hence \(a=(N-qh)/M\). On the edge where the admitted term has \(s=pb\), \(M=\ell v\le N^{43/80}\); on the other edge \(M=p\ell v\le N^{43/80+\beta}\). Use the pinned auxiliary one-dimensional Selberg square with level \(D_p=p/2\) to upper bound the roughness of \(a\). Its sieve primes are coprime to \(M\), and its reciprocal quadratic main coefficient is \(\Pi/(2\log p)(1+o(1))\), uniformly for \(p\) in the fixed exponent range. The fixed-\(M\) upper count with the original positive log weight enlarged to \((\log(h/q))_+\) has main term
\[
 N(J+o(1))\frac{\varphi(M)}{M^2}\frac{\Pi}{2\log p}.
\]
The weighted rectangular completion errors are bounded as in the pinned proof. Summing \(D_p^4N^{o(1)}(M^{1/2}+H/M^{1/2})\) over all moduli and divisor multiplicities costs at most \(N^{129/160+11\beta/2+o(1)}+N^{123/160+9\beta/2+o(1)}=o(N)\), since \(\beta\le1/200\). All endpoint and count masks may be relaxed for this upper count after the exact paired differences. [Pinned Selberg and rectangle calculation](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md#counting-at-a-modulus-that-includes-p).

For fixed \(\ell,p,b\), the relation \(2\log w=\log n-\log(\ell p b^2)-R\) puts \(w\) in a logarithmic interval of width at most \(\log p+O_B(\log L)\) on each edge. The resulting prime harmonic weight is \(\sum_w(\log w)/w\le(1+o(1))\log p\), since \(w>N^{1/5}\) and \(\log p\ge \alpha L\). After bounding \(\varphi(M)/M\le1\), this cancels the factor \(1/\log p\) from the sieve. For each edge the squarefree \(b\)-sum is at most \(\mathcal H(C)+o(1)\), uniformly in \(p\), by the fixed-exponent prime-product harmonic limit. [Pinned rough harmonic law](https://github.com/Sodelin/Research-Commons/blob/bc292106d03065e910b8dc6d2bbca1589313169b/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-rough-harmonic-cap.md).

Finally \(\log d\ge L-\log\ell-B\log L\), and the prime-\(\ell\) sum with weight \((\log\ell)/(\ell\log d)\) is bounded by \(\int_{1/10}^{1/8}dx/(1-x)+o(1)=\log(36/35)+o(1)\) using this lower bound. The remaining prime harmonic sum is \(\sum_{N^\alpha<p\le N^\beta}1/p=\log(\beta/\alpha)+o(1)\). The two edges each give \(\mathcal H(C)\), and the prefactor \(2\) in the charge cancels the \(2\) in the sieve coefficient. This proves (1). The original grouped negative weight is bounded by the sum of the two charges for \(b\le p^C\) and \(b>p^C\), by subadditivity of \(x_-\).
