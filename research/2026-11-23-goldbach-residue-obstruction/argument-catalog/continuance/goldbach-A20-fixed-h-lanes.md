# The fixed-cofactor constants behind the finite \(A_{20}\) replay

Let \(N=2^k\), \(H=\sqrt N\) and \(\alpha=H/(\log N)^{K_0}\). The raw cell \(A_{20}\) has \(q>H\), \(\alpha<h\le H/2\), and \(qh<N\). Its divisor weight contains \(\mu(q)\mu(qh)\log(1/h)\). For an odd squarefree \(h\), the contribution at this \(h\) is exactly
\[
1_{\{\alpha<h\le H/2\}}(-\mu(h)\log h)
\sum_{\substack{H<q<N/h\\q\text{ odd},\ \mu^2(q)=1,\ (q,h)=1}}
\Lambda(N-hq).
\tag{1}
\]
Indeed \(\mu(q)\mu(qh)=\mu(h)\) on the displayed squarefree coprime support, and the weight is zero off that support. A nonsquarefree \(h\) vanishes. An even squarefree \(h\) can only give \(N-hq=2\), since subtraction of any higher power of two leaves a multiple of four. Such a lane costs at most \(\log h\log 2\) before normalization.

For each fixed odd \(h\), the inner sum in (1) is
\[
\frac{N}{h}\prod_{p\nmid 2h}\left(1-\frac1{p(p-1)}\right)+o_h(N).
\tag{2}
\]
To prove this, temporarily extend \(q\) down to 1, costing \(O(H\log N)\), and set \(n=N-hq\). The parity and base progression give \(n\equiv N-h\pmod{2h}\), a reduced class of density \(1/\phi(h)\) among von Mangoldt weights. Fix \(Y\) greater than every prime divisor of \(2h\). For \(p\mid h\), the coprimality condition for \(q\) excludes exactly one of the \(p\) extensions of the base class to modulus \(hp\). For odd \(p\nmid h\), the condition \(p^2\nmid q\) excludes precisely the reduced class \(n\equiv N\pmod{p^2}\) out of \(p(p-1)\). The Chinese remainder theorem and prime number theorem in arithmetic progressions for fixed modulus therefore give
\[
\frac{N}{\phi(h)}\prod_{p\mid h}(1-1/p)
\prod_{\substack{p\le Y\\p\nmid 2h}}
\left(1-\frac1{p(p-1)}\right)+o_{h,Y}(N).
\]
The fixed-modulus asymptotic is uniform over the finitely many reduced classes even though \(N=2^k\) changes the particular classes. The first two factors simplify to \(N/h\).

Remove the remaining forbidden squares by a union bound. Proper prime powers contribute \(O(\sqrt N\log^2N)\) to the entire lane. For \(Y<p\le N^{1/4}\), Brun–Titchmarsh in \(n\equiv N\pmod{hp^2}\), with the prime weight at most \(\log N\), bounds the contribution by \(O_h(N\sum_{p>Y}p^{-2})\). For \(p>N^{1/4}\), there are at most \(N/(hp^2)\) positive multiples of \(p^2\) in the \(q\) range. Their total cost is \(O_h(N^{3/4}\log N)\). First take \(N\to\infty\) at fixed \(Y\), then \(Y\to\infty\), to obtain (2).

The constants below are a numerical comparison between (2) times the prefactor in (1) and the identical raw fixed-\(h\) slices at \(2^{28}\). The product was taken through \(2\cdot 10^6\). Its omitted relative factor is between \(1-1/(2\cdot10^6)\) and 1 by the all-integer telescoping bound. The reported decimals use floating-point arithmetic.

| \(h\) | Per-\(N\) asymptotic coefficient with indicator kept | Observed at \(2^{28}\) | First excluded \(k\ge20\) for \(K_0=5\) |
|---:|---:|---:|---:|
| 3 | +0.328666 | +0.328608 | 56 |
| 5 | +0.253414 | +0.253370 | 58 |
| 7 | +0.212981 | +0.212884 | 60 |
| 11 | +0.164533 | +0.164360 | 61 |
| 13 | +0.148518 | +0.148427 | 62 |
| 15 | −0.170559 | −0.170435 | 63 |
| 21 | −0.133290 | −0.133166 | 64 |

The last column checks \(2^{k/2}/(k\log 2)^5\ge h\) numerically. All fixed \(h\) eventually fail the strict \(\alpha<h\) mask for every fixed \(K_0\).

## The signed fixed-cofactor coefficients sum to the singular series

Put \(u_p=1/[p(p-1)]\), \(B=\prod_{p>2}(1-u_p)\), and let
\[
w(h)=\mu(h)1_{2\nmid h}\prod_{p\mid h}(1-u_p)^{-1},
\qquad c_h=-B\,w(h)\,\frac{\log h}{h}.
\]
The coefficients in (2) with the divisor weight are \(c_h\). Their signed total in the ordinary order is exactly
\[
\sum_{h\ge1}c_h=2\prod_{p>2}\left(1-\frac1{(p-1)^2}\right)=\mathfrak S(2^k).
\tag{3}
\]
For \(\Re s>1\), the Dirichlet series of \(w\) equals \(G(s)/\zeta(s)\), where
\[
G(s)=(1-2^{-s})^{-1}\prod_{p>2}
 \frac{1-(1-u_p)^{-1}p^{-s}}{1-p^{-s}}.
\]
This \(G\) has an absolutely convergent Dirichlet series \(\sum_d g(d)d^{-s}\) for \(\Re s>0\), since the deviations of the local coefficients from 1 are \(O(p^{-2})\) and are multiplied by a geometric sum of \(p^{-s}\). Thus \(w=\mu*g\). The classical prime number theorem bound \(\sum_{m\le x}\mu(m)\ll x e^{-c\sqrt{\log x}}\) yields the same bound with a possibly smaller \(c\) for \(\sum_{h\le x}w(h)\). Split the convolution at \(d=\sqrt x\), use the prime number theorem on the shorter part, and use \(\sum_d|g(d)|d^{-1/2}<\infty\) on the rest. Partial summation gives ordinary convergence of \(-\sum_h w(h)\log h/h\) and identifies its value with the limit at 1 from the right of the differentiated Dirichlet series. Since \(\zeta(s)^{-1}\) has a simple zero of derivative 1 at 1, that limit is \(G(1)\). At each odd prime the localized factor of \(B G(1)\) is \(((1-u_p)-1/p)/(1-1/p)=1-(p-1)^{-2}\), proving (3).

The finite replay takes place while the lower cutoff permits the smallest \(h\), and (3) explains the appearance of the singular series in those data. The tail of this coefficient series with \(h>\alpha\) tends to zero as the cutoff moves to infinity. Applying that cancellation to the actual \(A_{20}\) would require an error estimate uniform on the moving support, beyond the fixed-\(h\) statement (2). Hand proof for (1)–(3), finite computation for the table, and no Lean verification.
