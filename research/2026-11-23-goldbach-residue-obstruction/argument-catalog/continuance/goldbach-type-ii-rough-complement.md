# Retaining endpoint roughness in the Goldbach Type II expansion

Keep the pinned fixed-target semiprime band. Write \(L=\log N\), \(H=\sqrt N\), and \(Y=\exp(L^{.005})\). Keep \(q,h\in(H/2,H]\), squarefree \(m=qh\), \((m,N)=1\), the exact count and mark masks, the prime \(N^{1/10}<\ell\le N^{1/8}\), the sharp condition \(d=(N-m)/\ell>D_0\), and any original lower endpoint cutoff. The ordered weight is \(\tfrac12 F(m)\mu(h)\log(h/q)\log\ell\) on prime \(d\). It equals the original odd-\(m\) sum after pairing and cancels on even \(m\). [Pinned Vaughan reduction and masks](https://github.com/Sodelin/Research-Commons/blob/8e0260adeb1507379110f428ad925065c64fae51/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-semiprime-type-i-2121z.md).

## An equivalent expansion on the original endpoint support

Keep \(n=N-m\) squarefree and \(Y\)-rough before replacing the prime test on \(d\) by \(\Lambda(d)/\log d\). On the original prime support these conditions already hold. Conversely, on the retained support a proper prime power \(d\) is excluded by squarefreeness, so the replacement is exact. Apply Vaughan's identity with the same parameters and these masks in place.

For either Type I term, use the pinned grouping \(n=rs\) with \(r\le H^{20/19-\delta_1}\) for fixed \(\delta_1>0\), a bounded arithmetic coefficient on \(r\), and a smooth complementary weight on \(s\). On \(Y\)-rough support, dropping squarefreeness of \(n\) in these two Type I sums costs arbitrary logarithmic savings. The exceptional endpoint set has size \(O(N/Y)\), by the union of multiples of \(p^2\) for \(p>Y\), and the pinned divisor-moment bound handles the absolute weights. Keep roughness itself. It gives an arithmetic condition on \(r\) and a separate condition on \(s\).

For the latter, expand the exclusion of primes at most \(Y\) as \(\sum_{b\mid s,\,p\mid b\Rightarrow p\le Y}\mu(b)\). Truncate the number of chosen primes at a large fixed multiple of \(\log L\). On a dyadic scale \(S\), the number of exceptional \(s\) is at most a constant times \(S(\sum_{p\le Y}p^{-1})^k/k!\), where \(k\) is one above the truncation. The paired \(r,s\) count adds only a factor \(O(R)\) at scale \(R\), with \(RS\ll N\). The truncated expansion at an exceptional \(s\) has magnitude at most \(\tau(s)\), so the same divisor-moment bound gives arbitrary logarithmic savings. Every retained period \(b\) and the number of periods are \(N^{o(1)}\). Use the pinned Type I expansion of the masks on \(q,h\), with period \(a\mid q\).

With \(q=a q'\), \(s=b s'\), the equation is \((ah)q'+(br)s'=N\). Exact solutions force \((h,b)=(a,r)=(h,r)=1\), since \((h,N)=(r,N)=1\). Thus \(g=(ah,br)=(a,b)\) and \(g\mid N\); otherwise the row is empty. After imposing these conditions on the separated coefficients, Poisson uses a single class modulo \((b/g)r\) for \(q'\). The nonzero-mode power budget of the pinned two-period calculation is unchanged because the periods remain subpower. At frequency zero the exact reciprocal factor is \(g/(ab)=1/[a,b]\), and the normalized kernel is \(O(H/R)\) with polylogarithmic variation in \(h\) on the retained boxes \(RS\gg N/L^B\). The \(h\) prefix includes \((h,rNb)=1\) and the existing residual divisibility test, both allowed in the masked Möbius input. The absolute mask sum with denominator \([a,b]\) is polylogarithmic. Prime by prime a nonempty selection pays at least \(1/p\), with boundedly many patterns and bounded local coefficients. Thus the same zero-mode cancellation applies. [Pinned two-period determinant and masks](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-asymmetric-range.md) · [Pinned joint Poisson frequency bound](https://github.com/Sodelin/Research-Commons/blob/9a77141e26f67c56ec8c61102ce6516f5ed24f12/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-joint-frequency-cutoff.md).

Both Type I sums on this support are therefore \(O_A(N/L^A)\). The prime-tested sum equals the Type II sum **with \(n\) squarefree and \(Y\)-rough retained**, up to that error. This follows by rerunning the expansion and the Type I proof with these masks. With the same Vaughan thresholds, subtracting the two proved reductions bounds the aggregate signed contribution of the omitted endpoints on the full band. The subtraction yields no absolute estimate for those endpoints. Opening \(B_V\) now gives
\[
 qh+\ell uws=N,\qquad
 \tfrac12 F(m)\mu(h)\mu(u)\Lambda(w)\log(h/q)
              \frac{\log\ell}{\log(uws)}.
\]
The retained endpoint masks force \(w\) prime, \(\ell,w\) distinct, \((\ell w,us)=1\), and \(s\) \(Y\)-rough. The same strict cutoff on \(uws\) remains in the equation.

## Thin ratio intervals at arbitrary locations

In this expansion require \(u,w\) both prime. For each fixed \(\ell,s\), restrict \(\log(u/w)\) to an interval of length at most \(\Delta\), whose location can depend on \(\ell,s,N\). Impose also
\[
 M=\ell s\min(u,w)\le N^{2/3-\varepsilon},\qquad 0<\varepsilon<1/6\text{ fixed}.
\]
It suffices that \(\max(u,w)\ge N^{1/3+\varepsilon}\). The absolute contribution is
\[
 O_A\!\left(N\frac{1+\Delta+\log L}{\log Y}+\frac{N}{L^A}\right).
\tag{1}
\]
In particular it is \(o(N)\) for \(\Delta=o(\log Y)\). This allows unbalanced ratios without a separate upper bound or reciprocal restriction on \(s\).

For the proof, trim \(n<N/L^B\) with error \(O_A(N/L^A)\). For fixed \(\ell,s\), \(\log(uw)=\log(n/(\ell s))\) now varies by at most \(B\log L\). With \(x=\min(u,w)\) and \(y=\max(u,w)\), the identity \(2\log x=\log(uw)-|\log(u/w)|\) confines the prime \(x\) to a log interval of width \(O(\Delta+\log L)\). It is at polynomial scale by the original thresholds on \(u,w\). Its reciprocal prime sum is therefore \(O((1+\Delta+\log L)/L)\), by Chebyshev and partial summation.

Fix \(\ell,s,x\) and sieve the prime \(y=(N-qh)/M\) at fixed modulus \(M\). Count both possible placements of \(x,y\) in \(u,w\) in the upper bound. The pinned composite-modulus estimate gives \(O(N/(ML))\) for the main count. Its \(\varphi(M)/M\) factor cancels the reciprocal loss from omitting primes dividing \(M\). For a small fixed level exponent \(\eta\) the summed error after restoring the weights is
\[
 O\!\left(N^{1-3\varepsilon/2+2\eta+o(1)}\right),
\]
using the multiplicity \(d_3(M)=N^{o(1)}\) and the sum of \(M^{1/2}(1+H/M)\) through the displayed cap. Choose \(2\eta<3\varepsilon/2\). The original signed weight has magnitude \(O(\log\ell)\). Summing the main term uses \(\sum_{\ell}\log\ell/\ell\ll L\), the reciprocal sum for \(x\), and \(\sum_{s\le N,\ s\ Y\text{-rough}}1/s\ll L/\log Y\) by the Euler product. This proves (1). The two primes are exchanged only for this absolute count. [Pinned composite-modulus sieve, density and error](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md).

On the balanced slice \(u/w\asymp1\) with \(s\le N^\sigma\), fixed \(\sigma<5/24\), one can instead allow at most a fixed \(j\) prime factors in \(u\). Fix \(u\) and sieve \(w\) as in the pinned balanced proof. Mark the largest prime of \(u\), which is at polynomial scale, and sum the other factors by their reciprocal weights. The reciprocal sum for \(u\) is \(O_j((1+\log L)^j/L)\) on its polylogarithmic ratio interval. The modulus bound and power error are unchanged. Automatic roughness of \(s\) gives the absolute bound \(O_j(N(1+\log L)^j/\log Y)+O_A(N/L^A)=o(N)\) on this slice.


## Both rough factors in a fixed dyadic box

The peer's balanced-box completion can be combined with the retained endpoint masks to bound the entire chosen box of this expansion, including all its remaining \(\Lambda(w)\) weights. Fix dyadic \(\ell\) and \(u\) intervals at polynomial scale, and keep any compatible dyadic \(v\) interval, where \(v=ws\). Assume \(M=\ell u\le N^{2/3-\varepsilon}\) throughout for a fixed \(0<\varepsilon<1/6\). In particular this includes \(\ell\asymp N^{1/8}\) and \(u,v\asymp N^{7/16}\). The absolute weight is
\[
 O\!\left(\frac{N}{(\log Y)^2}+N^{1-3\varepsilon/2+2\eta+o(1)}\right)
\]
for a fixed sieve-level exponent \(\eta>0\) with \(2\eta<3\varepsilon/2\). This is \(o(N)\) with no prime or factor-count restriction on \(u\) and no separate restriction on \(s\).

Indeed at fixed \(\ell,u\), the exact \(v=(N-qh)/M\) is determined. The sum over all admitted \(w\mid v\) is bounded in absolute value by \(O(\log\ell)\), since \(\sum_{w\mid v}\Lambda(w)=\log v\le\log(uv)\) and the log ratio of \(h,q\) is bounded. In the retained expansion both \(u,v\) are \(Y\)-rough. For the count of \(v\), use the pinned fixed-modulus sieve with \(z=Y\). The Euler-product denominator and the \(\varphi(M)/M\) cancellation give \(O(N/(M\log Y))\); the same CRT error is \(N^{2\eta+o(1)}M^{1/2}(1+H/M)\). A Selberg level \(N^\eta\) is admissible because \(\log Y=o(\log N)\). Summing the error over moduli and their \(N^{o(1)}\) representations gives the stated power term. For the main term, one dyadic prime \(\ell\) interval contributes \(\sum_\ell \log\ell/\ell\ll1\). One dyadic \(u\) interval at polynomial scale contributes \(\sum_{u\ Y\text{-rough}}1/u\ll1/\log Y\) by the elementary one-dimensional Selberg upper sieve on the integers in the interval. This proves the two roughness savings. [Peer fixed-box weight and completion](https://github.com/Sodelin/Research-Commons/blob/6e1fa1e477a161e3e36c652bd3f353997bb82c22/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-balanced-type-ii-marks-2141z.md) · [Pinned composite-modulus sieve](https://github.com/Sodelin/Research-Commons/blob/909738e51f1ea4abe94c119276375481f85abc56/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/goldbach-type-ii-balanced-two-prime-sieve.md)

This bound is for the expansion with the endpoint masks retained. The signed comparison of full expansions above does not compare corresponding individual unrestricted Type II boxes. Summing these absolute dyadic estimates over the entire polynomial band also leaves the required signed lower bound open. All statements are hand proofs. No numerical or Lean check is used.
