# The signed centered test on the unmatched Goldbach outer cell

Fix \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(Q=N^{1/4}\) and the original strict lower cofactor cutoff \(h>\alpha=H/L^{K_0}\). After transposing \(A_{20}\), the common support with \(A_{02}\) has the smaller coordinate \(q\ge Q\) and \(q>\alpha\). The unmatched part of \(A_{02}\) is therefore exactly \(Q\le q\le\alpha\), retaining \(q\le H/2\) and \(H<h<N/q\). The inclusion of \(q=\alpha\) respects the strict cutoff of its transpose. [Pinned raw moving-cut ledger](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0) · [Matched row diagnosis](https://github.com/Sodelin/Research-Commons/commit/6c8c11372a303a7780a85f22e955c705d02ddd61)

With \(q\) odd and squarefree, and \(h\) odd and coprime to \(q\), define the exact fixed-target sum
\[
T_{02}(N)=
\sum_{\substack{Q\le q\le\min(H/2,\alpha)\\q\ {\rm odd},\ \mu^2(q)=1}}
\sum_{\substack{H<h<N/q\\(h,2q)=1}}
\mu(h)\log h\left(\Lambda(N-qh)-\frac{2q}{\varphi(q)}\right).
\]
Then
\[
A_{02}^{\rm unmatched}(N)=-T_{02}(N)+O(N e^{-c\sqrt L})
\tag{1}
\]
for a fixed \(c>0\). Thus a one-sided bound \(T_{02}(2^k)\le c_0 N\) for all sufficiently large \(k\) would give \(-c_0N+o(N)\) as a lower bound for this entry in the joint budget. The subtraction is the progression model per odd integer \(h\): the corresponding reduced progression for \(N-qh\) has modulus \(2q\), and \(\varphi(2q)=\varphi(q)\).

To prove (1), even \(h\) can contribute only \(N-qh=2\), since larger even prime powers make \(qh\) a multiple of four. This exact exception costs \(N^{o(1)}\) by the divisor bound. The remaining squarefreeness of \(qh\) is enforced by \(\mu^2(q)=1\), \((h,2q)=1\) and \(\mu(h)\). It suffices to bound the subtracted model across those same strict intervals.

For \(D=2q\), let \(g_D(d)\) be one if every prime of \(d\) divides \(D\), including \(d=1\), and zero otherwise. The identity \(\mu(h)\mathbf1_{(h,D)=1}=(\mu*g_D)(h)\) follows from local factors. Uniformly in \(D\le 2H\),
\[
\sum_d\frac{g_D(d)}d\ll L^C,
\qquad
\sum_d\frac{g_D(d)}{\sqrt d}\ll \exp(C\sqrt L).
\]
For these Euler products split the primes dividing \(D\) at \(L\). The small-prime sums of \(1/p\) and \(1/\sqrt p\) are \(O(\log L)\) and \(O(\sqrt L)\) even using all integers. There are at most \(O(L/\log L)\) prime divisors above \(L\), giving the same or smaller bounds. For \(H\le x\le N\), apply the classical Mertens prefix bound to the terms \(d\le\sqrt x\) in the convolution. Their total is \(O(x L^C e^{-c_1\sqrt L})\). On \(d>\sqrt x\) use \(\left|\sum_{m\le x/d}\mu(m)\right|\le x/d\), bounding the sum by \(x^{3/4}\exp(C\sqrt L)\). Consequently the masked Möbius prefix is \(O(xe^{-c_2\sqrt L})\), uniformly in \(q\) and \(x\) on these ranges. Partial summation with \(\log h\) gives \(O((N/q)L e^{-c_2\sqrt L})\) on each interval in the exact test. The factor \(2q/\varphi(q)\) leaves a total bounded by \(N L e^{-c_2\sqrt L}\sum_{q\le H}1/\varphi(q)\), and the totient reciprocal sum is \(O(L)\). Decreasing \(c_2\) proves (1).

The arithmetic estimate left by (1) is a signed correlation. A prime progression prefix bounds the unweighted centered sequence in the inner sum. It leaves the weighting by \(\mu(h)\log h\) uncontrolled. Equation (1) is a hand reduction at every fixed target. No new Lean check or inequality for \(T_{02}\) is asserted.
