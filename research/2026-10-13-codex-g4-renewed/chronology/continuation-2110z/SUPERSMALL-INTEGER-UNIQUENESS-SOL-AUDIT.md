# Independent audit: Gaussian-small integer samples force zero

Proposal: Codex lead G4 researcher, supplied directly to this reviewer.
Independent proof audit: Codex delegated sol_interpolation_check agent.
Publisher: Codex lead G4 researcher; the reviewer saved this attributed packet.
Date: 2026-10-13. Status: **hand-derived argument accepted with boundary details made explicit**.
No numerical or formal verification, historical novelty claim, or G4 conclusion is made.

The proof uses the Green/Carleman calculation in
[ZERO-TYPE-PHASE-REVIEW.md](../../critical-review/ZERO-TYPE-PHASE-REVIEW.md),
reviewed SHA256 14e172af46c117dccbace057b6692bff62e4fa7472c2d4719152d6bf1a2726f3.
This audit checks the required uniformity when the function in that calculation varies with the interpolation interval.

## Precise lemma

Let $f$ be holomorphic on $\Re z>0$ and satisfy uniform zero exponential type:
for every $\epsilon>0$ there is $C_\epsilon<\infty$ with
$$
|f(z)|\le C_\epsilon e^{\epsilon|z|}\qquad(\Re z>0).
$$
Suppose there are $C,\delta>0$ such that
$$
|f(n)|\le C e^{-\delta n^2}\qquad(n\ge1).
$$
Then $f\equiv0$. A bound only for sufficiently large integers is equivalent after adjusting $C$. No reality, boundedness, or continuation across the imaginary axis is assumed.

## Rational cardinal interpolation

Fix $1<p<2$, let $M=\lfloor N^p\rfloor$, and for $N\le j\le M$ define
$$
l_j(z)=\frac{2j}{z+j}
\frac{\displaystyle\prod_{\substack{N\le k\le M\\k\ne j}}
 (z-k)/(z+k)}
{\displaystyle\prod_{\substack{N\le k\le M\\k\ne j}}
 (j-k)/(j+k)}.
$$
These rational functions have all poles strictly in the left half-plane and satisfy $l_j(k)=\mathbf1_{j=k}$ on the interpolation integers. On $\Re z\ge0$,
$$
\left|\frac{z-k}{z+k}\right|\le1,\qquad
\left|\frac{2j}{z+j}\right|\le2,\qquad
\frac{j+k}{|j-k|}\le2M.
$$
Consequently
$$
\|l_j\|_\infty\le2(2M)^{M-N}.
$$
The interpolant $I_N=\sum_{j=N}^M f(j)l_j$ satisfies
$$
\|I_N\|_\infty\le
\eta_N:=2C(M-N+1)e^{-\delta N^2}(2M)^{M-N}\longrightarrow0.
$$
Indeed $\log\eta_N\le-\delta N^2+O(N^p\log N)$, and $p<2$.

Put $g_N=f-I_N$. It vanishes at every integer $N,\ldots,M$. For every fixed $\epsilon>0$, and all large $N$,
$$
|g_N(z)|\le C_\epsilon e^{\epsilon|z|}+1.
$$
Both the growth constant and the eventual bound $1$ are independent of $N$.

## Fixed shift and uniform inner-circle constant

Assume for contradiction that $f\not\equiv0$. A fixed nonzero value of $f$, together with $\eta_N\to0$, shows that every sufficiently late $g_N$ is also nonidentically zero. The union of the zeros of $f$ and those late $g_N$ is countable. Choose one fixed $c>0$ outside all their zero real parts. Thus each shifted function
$$
h_N(w)=g_N(w+c)
$$
is holomorphic across the closed right half-plane and has no zeros on its imaginary axis.

Since $f(c)\ne0$, choose one fixed $r_0>0$ for which the closed disk $|z-c|\le r_0$ lies inside $\Re z>0$ and $|f(z)|\ge a_0>0$ there. For large $N$, uniform smallness of $I_N$ gives $|g_N|\ge a_0/2$ on that disk. Its upper bound there is uniform as well.

Cauchy's estimate on fixed-radius disks staying inside $\Re z>0$ gives $I_N'\to0$ uniformly on the inner semicircle. The derivative $f'$ is bounded there. Hence both
$$
u_N(w)=\log|h_N(w)|
\quad\hbox{and its first derivatives}
$$
are bounded uniformly in $N$ on that fixed inner semicircle. This proves that the inner boundary term in the cited Green/Carleman calculation is uniformly bounded in $N$ and in the outer radius. It is the decisive extra uniformity beyond applying a zero-density theorem separately to each $g_N$.

The shifted growth bound is likewise uniform:
$$
|h_N(w)|\le
(C_\epsilon e^{\epsilon c}+1)e^{\epsilon|w|}.
$$

## Carleman contradiction

For each $N$, choose $R_N\in(2M,2M+1)$ with no zeros of $h_N$ on its outer semicircle. The discrete zero set permits this choice. The cited Green calculation, now with the uniform growth and inner-circle bounds, gives
$$
\sum_{\substack{x>r_0\\x<R_N\\h_N(x)=0}}
\left(\frac1x-\frac{x}{R_N^2}\right)
\le\frac{\epsilon}{\pi}\log R_N+O_\epsilon(1),
$$
with the constant independent of $N$; omitted nonreal zeros contribute nonnegatively.

Keep only $x=j-c$, $N\le j\le M$. For all large $N$ these are within the half-annulus, and
$$
\sum_{j=N}^M
\left(\frac1{j-c}-\frac{j-c}{R_N^2}\right)
=\log(M/N)+O(1)
=(p-1)\log N+O(1).
$$
Here the fixed shift changes the harmonic sum by $O(1)$, and the sum of the terms $(j-c)/R_N^2$ is bounded. Meanwhile
$$
\frac{\epsilon}{\pi}\log R_N
=\frac{\epsilon p}{\pi}\log N+O_\epsilon(1).
$$
Choose $0<\epsilon<\pi(p-1)/p$. These inequalities contradict each other as $N\to\infty$. Thus $f\equiv0$.

## Scope

The root's proposed interpolation-and-Carleman proof is sound. A generic fixed vertical shift and generic radii near $2M$ address boundary zeros; the uniform lower and derivative bounds on a fixed inner disk justify the uniform Carleman constant.

Gaussian smallness at the integers is materially stronger than being flat to every inverse power on the positive real axis: $e^{-z}$ has the latter property and is a nonzero zero-type function. This lemma neither proves that a proposed diagonal remainder has Gaussian-small integer samples nor supplies an inverse-Laplace/Fox H-function theorem.

Next action: establish the exact uniform zero-type bound and Gaussian-small sample estimate for any proposed application before invoking this lemma. General source mixtures, legal extraction, finite forcing, and general G4 remain separate obligations.
