# An adaptive Type I cutoff for the unmatched Goldbach outer row

At each fixed \(N=2^k\), write \(L=\log N\), \(H=\sqrt N\), \(Q=N^{1/4}\), \(\alpha=H/L^{K_0}\), and put
\[
 \mathcal J=\{q:Q\le q\le\min(\alpha,H/2),\ q\text{ odd},\ \mu^2(q)=1\}.
\]
The unmatched \(A_{02}\) keeps \(H<h<N/q\) and \((h,2q)=1\) after removing the single possible even prime-power endpoint \(N-qh=2\). That exception costs \(N^{o(1)}\). The signed weight on the odd support is \(-\mu(h)\log h\,\Lambda(N-qh)\). [Exact unmatched row and progression centering](https://github.com/Sodelin/Research-Commons/commit/eda6bd32ba1e1d7f5e92106fc70037b0aeb2a375)

For any fixed \(A>0\), choose a sufficiently large fixed \(B\) and let
\[
 X_q=N/q,\qquad D_q=\frac{\sqrt{X_q}}{L^B}.
\]
The exact equation \(qh+rs=N\) can be restricted to \(r>D_q\) in the divisor expansion of this row with signed error \(O_A(N/L^A)\). The cutoff ranges in polynomial order from \(N^{1/4}\) at the upper \(q\) edge to \(N^{3/8}\) at the lower edge, with the displayed logarithmic factors. There is also an exact reflected Vaughan version on \(qh+wbs=N\), with \(wb>D_q\) and \(w\) an actual prime.

## A maximal Möbius estimate with the original coprimality mask

For odd \(r\) coprime to \(q\), let
\[
 M_q(r)=\max_{0\le y\le X_q}\max_{(a,2r)=1}
 \left|\sum_{h\le y\,;\,h\equiv a\ (2r)}\mu(h)\mathbf1_{(h,q)=1}\right|.
\]
The bound sufficient here is
\[
 \sum_{q\in\mathcal J}\sum_{\substack{r\le D_q\,;\,(r,2q)=1}}M_q(r)
       \ll_A N/L^A. \tag{1}
\]
Use the maximal Bombieri–Vinogradov theorem for \(\mu\). For every requested log saving \(A_1\) there exists \(B_1\) such that the sum over moduli \(m\le\sqrt x/(\log x)^{B_1}\) of the maximum of \(|\sum_{j\le y,\ j\equiv a\bmod m}\mu(j)|\) over \(a\) and \(y\le x\) is \(O_{A_1}(x/(\log x)^{A_1})\). This is a theorem about averaging the modulus, applied below with \(N\) fixed. [Siebert–Wolke, Corollary 1](https://doi.org/10.1007/BF01110168) · [Maximal formulation in Murty–Vatwani, Proposition 3](https://www.mathjournals.org/jrms/2018-033-002/2018-033-002-001.html)

Convolve \(\mu\mathbf1_{(\cdot,q)=1}=\mu*g_q\), where \(g_q(t)\) is the indicator that every prime factor of \(t\) divides \(q\), with \(g_q(1)=1\). Since \((r,2q)=1\), each contributing \(t\) has an inverse modulo \(2r\). The residual variable has length at most \(X_q/t\) and lies in a unit class modulo \(2r\).

Take \(T=L^C\), with \(C\) sufficiently large in terms of \(A\). At each fixed \(q,t\le T\) with \(g_q(t)=1\), choose \(B>B_1+C/2+2\), so \(2D_q\) lies within the maximal theorem's range at \(x=X_q/t\). Both \(\log X_q\) and \(\log(X_q/t)\) are comparable to \(L\) uniformly. The sum over \(r\) is \(O_{A_1}(X_q/(tL^{A_1}))\). Since \(\sum_{t\le T}g_q(t)/t\le 1+\log T\) and \(\sum_qX_q\ll NL\), the contribution is \(O_A(N/L^A)\) after choosing \(A_1>A+3\).

For \(t>T\), bound the progression by \(X_q/(2rt)+1\). The term with \(X_q/(2rt)\) is at most
\[
 \ll NL^2 \sum_{t>T}\frac{1}{t\operatorname{rad}(t)}
       \ll NL^2 T^{-1/2}.
\]
Here \(g_q(t)=1\) implies \(\operatorname{rad}(t)\mid q\), so the reciprocal sum over \(q\) is \(O(L/\operatorname{rad}(t))\). The series \(\sum_t t^{-1/2}/\operatorname{rad}(t)\) converges by its Euler product. For the error \(+1\), fix \(\varepsilon=1/8\) and use
\[
 \sum_{t\le X_q}g_q(t)\le X_q^{\varepsilon}\prod_{p\mid q}(1-p^{-\varepsilon})^{-1}
        =X_q^{\varepsilon}N^{o(1)}.
\]
The last bound is uniform by splitting the primes dividing \(q\) at \(L\). The small-prime sum of \(p^{-\varepsilon}\) is \(O(L^{1-\varepsilon})\) even over all integers, and the larger primes contribute at most \(O(L^{1-\varepsilon})\). The full floor cost is bounded by
\[
 N^{o(1)}\sum_{q\le H}(N/q)^{1/2+\varepsilon}
        \ll N^{3/4+\varepsilon/2+o(1)}.
\]
With \(C>2A+6\), these tail bounds prove (1).

## Application to the exact signed equation

If \(r\mid N-qh\) then \((r,q)=1\), since \(q\) is odd and \(N\) is a power of two. The oddness of \(h\) and the equation put \(h\) in one unit residue class modulo \(2r\). On every interval inside \(H<h<N/q\), the signed sum of \(\mu(h)\mathbf1_{(h,q)=1}\) is bounded by \(2M_q(r)\). The absolute size plus variation of \(\log h\) is \(O(L)\). For the divisor weight \(\log((N-qh)/r)\) impose \(N-qh\ge r\), which leaves all solutions with \(s\ge1\). The absolute size plus variation of the product of the two logs is \(O(L^2)\), by their individual monotonicity on the resulting interval. Thus (1), with a stronger requested logarithmic saving, applies to each of these weights, to bounded additional power-of-log coefficients at \(q,r\), and to individual sharp interval endpoints. In particular, the part \(r\le D_q\) of \(\Lambda(n)=\sum_{rs=n}\mu(r)\log s\) costs \(O_A(N/L^A)\), including the actual \(\log h\) and the original sign of the row.

## Reflected Vaughan remainder with one actual prime

Choose \(U=V=N^{1/10}\) in the unmatched row. The prior center parameters are separate. Vaughan's identity in convolution notation is
\[
 \Lambda=\Lambda_{\le V}+\mu_{\le U}*\log
       -\mu_{\le U}*\Lambda_{\le V}*1+\mu_{>U}*\Lambda_{>V}*1.
\]
The term \(\Lambda_{\le V}(N-qh)\) costs \(O(N^{1/10+o(1)})\) by the fixed-endpoint divisor bound. The next two terms use \(r\le UV\), within \(D_q\), and their coefficients are bounded by \(1\) and \(\sum_{w\mid r}\Lambda(w)=\log r\), respectively. The same log savings apply.

In the last term, fix an admitted \(w>V\), \(w\mid n=N-qh\). For \(n/w>U\), the full tail of \(\sum_{u\mid n/w}\mu(u)\) equals the negative of the head \(\sum_{b\mid n/w,\ b\le U}\mu(b)\). For \(n/w\le U\), there was no tail. The reflected sign in the raw row is therefore positive in front of \(\mu(h)\mu(b)\Lambda(w)\log h\). At fixed \(r=wb\le D_q\), the surviving test \(n>Uw\) is a sharp upper endpoint on \(h\) for each divisor \(w\mid r\). Applying (1) with that interval and summing the coefficient weights \(\Lambda(w)\) over \(w\mid r\), of total at most \(\log r\), removes all these small indices without an endpoint trim.

The remaining proper prime powers \(w>V\) of exponent at least two have total cost \(\ll N^{1+o(1)} \sum_{w>V,\ w=p^j,\ j\ge2}1/w=N V^{-1/2+o(1)}\). Indeed each fixed \(w\) divides at most \(N/w\) endpoint integers, and the divisor multiplicities in the two factorizations \(qh=N-n\) and \(bs=n/w\) are \(N^{o(1)}\). A dyadic count of prime powers bounds their reciprocal tail. Consequently the following identity holds at each sufficiently large target, for every fixed \(A>0\) with the stated \(B\):
\[
 A_{02}^{\rm unmatched}(N)=
 \sum_{\substack{q\in\mathcal J,\ H<h<N/q,\ (h,2q)=1\\
       qh+wbs=N,\ w>V\ {\rm prime},\ b\le U,\ bs>U,\ wb>D_q}}
       \mu(h)\mu(b)\log h\log w
       +O_A(N/L^A). \tag{2}
\]
All variables are positive integers. The strict inequalities in (2) keep the original \(h\) condition and the exact open side of the removed divisor band. Since \(b\le U\), the actual prime satisfies \(w>D_q/U\). When \(w>D_q\), every \(b\le U\) automatically passes the adaptive cut. If the product of the distinct primes at most \(U\) dividing \(n/w\) lies in \((1,U]\), the whole \(b\)-group then sums to zero exactly by the complete Möbius sum. The remaining terms still need a signed lower bound in (2). The result is an unconditional hand proof using classical Möbius distribution, with no new Lean or finite-target verification.
