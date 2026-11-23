# A positive slice of the rough coprime separated Artin covariance

Fix the standard \(S_3\) factor, a dilation \(B>0\), and the original windows \(v_0=\log Y\le v\le V=\log X\) with \(V-v_0\to\infty\) and \(V-v_0=o(V)\). Use the original locked parameters
\[
 U=\lfloor Y^u\rfloor,\qquad P=Y^\alpha,\qquad H=Y^{u+\kappa},
 \qquad u,\alpha,\kappa>0,\quad u+\alpha+\kappa<1.
\]
The retained companions are \(U<h<k\le H\), are coprime and have no prime factor at most \(z=(\log X)^2\), and satisfy \(k-h>H_0\), where \(\log H_0=o(\log X)\). The proof below also works for any fixed polynomial \(H_0=X^\omega\) with \(\omega<u\). Put
\[
 \begin{split}
 E_P(y)&=\sum_{\substack{p>P\\p\ {\rm splits\ completely}}}
              (\log p)K_B(p/y)-\frac16\int_P^\infty K_B(t/y)\,dt,\\
 g_P(w)&=e^{-w/2}E_P(e^w),\qquad
 b_h=\beta_U(h)/\sqrt h,\qquad \beta_U=\mu_{L,>U}*a .
 \end{split}
\]
Here \(K_B(t)=e^{-B}(e^B/t-1)_+-(1/t-1)_+\) is unchanged. A pair's actual covariance contribution is
\(2b_hb_k\int_{v_0}^V g_P(v-\log h)g_P(v-\log k)\,dv\).
[Original covariance](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3) · [Sharp rough and coprime support](https://github.com/Sodelin/Research-Commons/commit/cee389512c24de3ea6d0a90bb3c82f3b0c1e7ecc)

Let \(\beta_*=\sup_\rho\Re\rho\) be the actual Artin zero supremum. Assume the off-line case \(\beta_*>1/2\), without an assumption that it is attained. There is an exact subset of retained pairs, with both \(h,k\) completely split primes in \((U,2U]\), for which every covariance contribution is positive and whose sum is
\[
 X^{(1-u)(2\beta_*-1)+u+o(1)}.
\tag{1}
\]
The gaps in this subset satisfy \((k-h)/U=X^{-o(1)}\) and tend to zero relative to \(U\). If \(\beta_*<1\), (1) is larger by a fixed power than the upper envelope \(X^{2\beta_*-1+o(1)}\) of the entire retained signed covariance. At \(\beta_*=1\) it still gives an actual positive slice of exponent \(1\). In particular additive separation alone cannot provide a uniform power decay of the individual kernel correlation.

## A uniform uncut prime lower bound on the shifted windows

Let \(F(t)=\sum_{p\le t,\ {\rm split}}\log p-t/6\) for \(t\ge0\). The pointwise prefix envelope from the actual Artin zero supremum and the verified Dirichlet inputs gives, for every \(\epsilon>0\),
\[
 F(t)=O_{L,\epsilon}((1+t)^{\beta_*+\epsilon}).
\tag{2}
\]
The completely split trace identity is \(a(p)=3\mathbf1_{\rm split}-(1+\chi(p))/2\) at unramified primes, with \(\chi\) the resolvent character. Partial summation with \(K_B\) and the two Dirichlet prefixes therefore give
\[
 E_0(y)=-\frac43 C_{0,B}(y)+O_{L,B,\epsilon}(y^{1/2+\epsilon}),
 \qquad C_{0,B}(y)=-\tfrac14\mathscr K_y(\Lambda_L).
\tag{3}
\]
Here \(E_0\) is the same centered prime sum with all primes and with continuous reference from zero. The higher Artin prime powers omitted in the trace identity cost \(O_B(\sqrt y)\) by the local bound \(|\Lambda_L(p^j)|\le 2\log p\); finitely many ramified assignments cost \(O_B(1)\) in the prime sum. This does not use a zero hypothesis for the Artin factor. [Dirichlet centering and Artin prime prefix](https://github.com/Sodelin/Research-Commons/commit/1dcdd242401023541592d0126a999ae6cb43c8c5)

For every real \(h\in[U,2U]\), the shifted original interval ends at \(W_h=V-\log h\) and has length \(V-v_0\). Uniformly on this range, \(W_h=(1-u+o(1))V\), and \(y=e^v/h\ge Y/(2U)\gg P\). The strict cutoff and the unchanged continuous reference then give the exact equality
\[
 E_P(y)=E_0(y)-(1-e^{-B})F(P).
\tag{4}
\]
Indeed \(K_B(t/y)=1-e^{-B}\) throughout \(0<t\le P\). Thus after dividing by \(\sqrt y\), (4) has error \(O(P^{\beta_*+\epsilon}y^{-1/2})\).

For any fixed real part \(\sigma_0<\beta_*\) sufficiently close to \(\beta_*\), choose a zero with real part at least \(\sigma_0\). The fixed-length Artin detector gives a terminal log interval of length \(L_{\sigma_0}\), independent of \(X,h\), on which the positive part of \(C_{0,B}(y)/\sqrt y\) has integral \(\gg e^{(\sigma_0-1/2)W_h}\). The detector is uniform over all sufficiently late terminal arguments. Since \(V-v_0\to\infty\), this whole interval lies in every tested shifted window. The two errors in (3) and (4) have strictly smaller exponents on that terminal interval. For (4), choose \(\sigma_0\) sufficiently close that \(\alpha\beta_*<(1-u)\sigma_0\), which is possible since \(\alpha+u<1\); for (3) take \(\epsilon<\sigma_0-1/2\). These choices hold uniformly because \(h/U\) lies in \([1,2]\). Cauchy–Schwarz on the fixed terminal interval and (3)–(4) imply
\[
 \inf_{h\in[U,2U]}\|g_P(\,\cdot-\log h)\|_{L^2([v_0,V])}
       \ge (X/U)^{\beta_*-1/2-o(1)} .
\tag{5}
\]
In passing to the \(o(1)\), keep each chosen zero and its filter length fixed before letting \(X\) go to infinity, then take its real part toward \(\beta_*\). The prime-prefix envelope gives the matching upper exponent, because the log-window length is \(X^{o(1)}\). This argument applies at \(\beta_*=1\), including nonattainment. [Fixed-length detector for each chosen off-line zero](https://github.com/Sodelin/Research-Commons/commit/304b341ad0a4a99eb16055613bfafceb7c476850)

## The kernel has no decorrelation at small relative gaps

The normalized function \(g_P\) is locally absolutely continuous. Differentiating the original \(K_B\) almost everywhere yields
\[
 \frac{d}{dw}E_P(e^w)
  =\int_{\substack{t>P\\ e^w<t<e^{w+B}}}\frac{e^w}{t}\,dF(t).
\]
The endpoints are harmless because \(K_B\) is continuous, including at its two transition points. The integral is zero below the active support and is \(O_{L,B,\epsilon}(y^{\beta_*+\epsilon})\) at \(y=e^w\) by (2) and partial summation. Thus on the shifts in (5),
\[
 |g'_P(w)|\ll_{L,B,\epsilon} e^{(\beta_*-1/2+\epsilon)w}
 \quad\text{almost everywhere}.
\tag{6}
\]
Let \(A_X\) be the infimum on the left of (5), and put
\[
 D_X=(V-v_0)^{1/2}
      \operatorname*{ess\,sup}_{v_0-\log(2U)\le w\le V-\log U}|g'_P(w)|,
 \qquad
 \delta_X=\min\left\{\frac1{\log X},\,\frac{A_X}{4(1+D_X)}\right\}.
\]
Equations (5)–(6) give \(\delta_X=X^{-o(1)}\) and \(\delta_X\to0\). The logarithmic shifts obey \(|\log h-\log k|\le |h-k|/U\). With \(Q_X=U\delta_X\), all \(h,k\in[U,2U]\) with \(|h-k|\le Q_X\) therefore satisfy
\[
 \|g_P(\cdot-\log h)-g_P(\cdot-\log k)\|_2
      \le D_X\delta_X\le A_X/4.
\]
Write \(f_h(v)=g_P(v-\log h)\). By Cauchy–Schwarz,
\[
 \int_{v_0}^V f_h(v)f_k(v)\,dv
 \ \ge\ \|f_h\|_2^2-\|f_h\|_2\,A_X/4
 \ \ge\ \tfrac34 A_X^2.
\tag{7}
\]
Thus the estimate compares the actual shifted kernel values, before any companion arithmetic cancellation.

For a fixed \(0<\tau<u\), the same argument applies with \(Q_X=X^\tau\), since its relative shift \(X^{\tau-u+o(1)}\) is smaller than \(\delta_X\). Consequently even at polynomial additive gaps, the individual correlations can have the full single-kernel power \((X/U)^{2\beta_*-1-o(1)}\). This excludes a uniform extra factor \((1+|h-k|)^{-c}\) for any fixed \(c>0\) on that scale in the off-line case.

## Counting actual same-sign companions

There are \(\sim U/(6\log U)\) completely split primes in \((U,2U]\) by fixed-field Chebotarev. Partition this interval into \(O(U/Q_X)\) cells of length at most \(Q_X\), and let \(n_j\) be their counts of these primes. Cauchy–Schwarz gives
\[
 \sum_j \binom{n_j}{2}
  =\frac12\sum_j n_j^2-\frac12\sum_j n_j
  \gg \frac{U Q_X}{(\log X)^2} .
\]
The subtracted \(\sum_j n_j\) is smaller since \(Q_X=X^{u-o(1)}\). Set the lower gap \(q_X=Q_X/(\log X)^3\). At most \(O((1+q_X)U/\log X)\) pairs can have gap at most \(q_X\), since for each first prime the number of eligible integers that close is at most \(1+q_X\). This is smaller by logarithmic powers. Thus there are \(\gg UQ_X/(\log X)^2\) completely split prime pairs with
\[
 q_X<k-h\le Q_X,\qquad U<h<k\le2U .
\tag{8}
\]
This count needs no short-interval Chebotarev theorem. The lower gap exceeds \(H_0\), and \(2U<H\) for all sufficiently large windows. Both primes are rough and, being distinct, coprime. Since \(h>U\) is prime, only the divisor \(h\) enters its inverse tail, so \(\beta_U(h)=\mu_L(h)=-a(h)=-2\) at every completely split prime. Thus \(2b_hb_k=8/\sqrt{hk}\asymp U^{-1}>0\) on (8). [Fixed-field Chebotarev, Lagarias–Odlyzko Theorem 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf)

Combine (5), (7), (8) and this exact sign to get
\[
 \sum_{\text{pairs in (8)}}2b_hb_k\int f_h f_k
 \gg \frac{Q_X}{(\log X)^2}(X/U)^{2\beta_*-1-o(1)}
 =X^{u+(1-u)(2\beta_*-1)-o(1)}.
\]
For the matching upper exponent use at most \(O(UQ_X)\) integer pairs, the same bound on \(b_hb_k\), and the individual upper envelope from (2). This proves (1), with all pairs also satisfying the original strict restrictions. A deterministic fixed-power variant takes \(Q_X=X^\tau\) and has exponent \(\tau+(1-u)(2\beta_*-1)\); the same counting proof works. For \(\beta_*<1\) one may choose \(u(2\beta_*-1)<\tau<u\) to force the strict comparison with the whole signed covariance even with a predetermined gap exponent.

## The cancellation already occurs among prime companions in the same cells

Fix the cells used for (8). Restrict to all prime companions in the same cell and keep the original additive separation \(k-h>H_0\), with \(\log H_0=o(\log X)\). For each cell \(I_j\), the exact signed scalar sum is
\[
 S_j(v)=-x^{-1/2}\sum_{q\in I_j,\ q\ {\rm prime}}a(q)E_P(x/q),
 \qquad x=e^v.
\]
The signed Artin prime prefix has \(\sum_{q\le t}a(q)=O_\epsilon(t^{\beta_*+\epsilon})\), by partial summation from the logarithmically weighted prefix. On \(q\in[U,2U]\), (2) and the derivative calculation in (6) give the supremum plus total variation of \(x^{-1/2}E_P(x/q)\) on any cell as
\[
 O_\epsilon(X^{\beta_*-1/2+\epsilon}U^{-\beta_*+\epsilon}).
\]
Indeed its derivative in \(q\) is at most this bound times \(O(U^{-1})\), and the cell has length at most \(U\). Thus partial summation gives \(S_j(v)=O_\epsilon(X^{\beta_*-1/2+\epsilon})\) uniformly. There are \(O(U/Q_X)=X^{o(1)}\) cells. The same-cell covariance of all prime companions, including the diagonal and close pairs, is \(\sum_j\int_{v_0}^V S_j(v)^2\,dv\), so it is \(O_\epsilon(X^{2\beta_*-1+\epsilon})\). Removing the pairs with \(|h-k|\le H_0\) costs at most
\(O(H_0 X^{(1-u)(2\beta_*-1)+o(1)})\) by the individual envelope. The exact same-cell separated signed covariance therefore has upper exponent \(2\beta_*-1\). For a polynomial separation this last comparison still holds if \(H_0=X^\omega\) and \(\omega\le u(2\beta_*-1)\).

The split prime pairs counted in the cell proof of (8) already supply the positive exponent in (1). All kernel correlations within a cell are positive by (7). A prime companion has trace \(2\), \(-1\), or \(0\) according as it is an identity, 3-cycle, or transposition prime. Hence the negative same-cell terms are precisely the mixed identity–3-cycle pairs. When \(1/2<\beta_*<1\), their magnitude is \(1+o(1)\) times the sum of the positive terms on the same-cell separated prime support, since the total signed sum has strictly smaller exponent. This is a cancellation between actual prime companions on the same retained support.

## The critical-line case also has a large positive slice

Now suppose \(\beta_*=1/2\), in addition to the verified Dirichlet critical-line input for \(\zeta\) and \(L(s,\chi)\). At every unramified prime power, the identity indicator of \(\mathrm{Frob}_p^{\,j}\) is its regular-character proportion
\((1+\chi(p)^j+2\operatorname{tr}\rho(\mathrm{Frob}_p^j))/6\). The associated smoothed prime-power count is therefore controlled by
\[
 D(s)=-\frac16\frac{\zeta'}{\zeta}(s)
      -\frac16\frac{L'}{L}(s,\chi)
      -\frac13\frac{L'}{L}(s,\rho).
\]
The finitely many ramified primes change the smoothed count by \(O(\log y)\). The pole at \(s=1\) contributes \(\tfrac16 yH_B(1)\), which is exactly the uncut continuous reference in \(E_0(y)\). All nontrivial zeros now have real part \(1/2\). Shifting the original \(H_B\) contour to a fixed line \(0<\sigma<1/2\) crosses their logarithmic-derivative residues. The \(O((1+|\Im s|)^{-2})\) kernel and local zero count give an absolutely convergent zero sum. Horizontal segments can be taken at heights avoiding all ordinates by an inverse log distance, so the local logarithmic-derivative bound and kernel imply their vanishing. The remaining vertical integral is \(O(y^\sigma)\). [Original explicit formula and local zero count](https://github.com/Sodelin/Research-Commons/commit/e00069c40dd17f50a10f57bb76d7300c8f0e3cdf)

To obtain the prime-only \(E_0(y)\), subtract the higher powers. For squares, the condition \(\mathrm{Frob}_p^2=e\) holds on the identity and transposition classes, of total density \(2/3\). Fixed-field Chebotarev and partial summation give
\[
 \sum_{\mathrm{Frob}_p^2=e}\log p\,K_B(p^2/y)
    =\frac23\int_0^\infty K_B(t^2/y)\,dt+o(\sqrt y)
    =\frac13 H_B(1/2)\sqrt y+o(\sqrt y).
\]
For the first equality use the \(o(t)\) Chebotarev prefix error on the moving support \(t\le e^{B/2}\sqrt y\); a bounded initial range is negligible. Powers \(j\ge3\) cost \(O(y^{1/3}\log y)\) by Chebyshev. Thus uniformly as \(w\to\infty\),
\[
 e^{-w/2}E_0(e^w)
 =-\frac{H_B(1/2)}3
  -\sum_{\rho=1/2+i\gamma} c_\rho H_B(\rho)e^{i\gamma w}+o(1),
\tag{9}
\]
where \(c_\rho\) is the sum of the positive weighted multiplicities from the three \(L\)-functions in \(D\). The trigonometric series converges absolutely and uniformly. Noncentral frequencies average to zero uniformly in the interval start as the interval length tends to infinity. Central coefficients, if present, have nonpositive sign in (9), so the average is at most \(-H_B(1/2)/3+o(1)<0\). Formula (4) changes the normalized function by \(o(1)\) uniformly on these shifts, since \(\alpha+u<1\) and the prime-prefix exponent is \(1/2+\epsilon\). Hence with \(L_0=V-v_0\), all the shifted norms in (5) are bounded above and below by positive constants times \(\sqrt{L_0}\).

The absolute convergence in (9) makes its limiting trigonometric series uniformly continuous. Choose a sufficiently small fixed \(\delta>0\). On \(|h-k|\le\delta U\), the pointwise difference \(g_P(v-\log h)-g_P(v-\log k)\) is uniformly smaller than a fixed quarter of the lower normalized norm, for sufficiently late windows. Thus the same Cauchy–Schwarz argument as in (7) bounds every such kernel covariance above and below by positive constants times \(L_0\). Take cells of length \(Q_X=\delta U\) and discard gaps at most \(Q_X/(\log X)^3\) in the positive split-prime subset. Its positive covariance has order
\[
  \frac{U(V-v_0)}{(\log U)^2}.
\]
The lower bound follows from the same count as (8), and the upper bound uses at most \(O((U/\log U)^2)\) split-prime pairs. This is \(X^{u+o(1)}\). Yet the exact signed same-cell separated prime covariance is subpower by the preceding scalar bound at \(\beta_*=1/2\). Therefore the mixed identity–3-cycle terms cancel the positive prime-companion mass also in the critical-line case.

These are hand arguments. The whole retained signed covariance bound remains open. No numerical checks or new Lean verification are used.
