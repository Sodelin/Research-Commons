# The modulus-3 odd semiprime error has no uniform lower bound on the singular-series scale

23 November 2026 · GB-PREFIX-Q3-ODD-001 · Hand proof with a separate finite replay

**Question.** Can the odd squarefree semiprime slice of the signed, centered modulus-3 row be charged a fixed fraction of the main term, uniformly in the target? On the even family $N\equiv2\bmod6$, the answer is negative. For every $C>0$, infinitely many individual $N$ in this family have
$$
E_{\mathrm{odd}}(N)<-C\,\mathfrak S(N) N.
$$
Here $E_{\mathrm{odd}}$ is actual minus centered model, restricted to odd squarefree semiprime cofactor cells, and $\mathfrak S$ is the binary Goldbach singular series. This is an unconditional obstruction to a separate bound for that slice. The estimate on the combined signed remainder is still open. The preceding Commons note reduced the $h=5p$ cells locally and recorded their $N=9602$ tally. This checkpoint extends the reduction to all odd squarefree semiprimes, sharpens the off-diagonal bound, and proves the asymptotic counterexamples. [Original checkpoint](README.md) · [Earlier three-offset reduction](../continuance/three-offset-local-obstruction.md)

## The two off-diagonal offsets

Use $1\le\alpha(N)\le\sqrt N$, which includes $\alpha=\sqrt N/(\log N)^K$ for large $N$ and fixed $K\ge0$. The modulus $q=3$ is squarefree and coprime to $N$, and lies in the low band once $12\alpha<N$. For any retained cell $h=\lfloor(N-n)/3\rfloor$, put $m_j=3h+j$ and $n_j=N-m_j$ for $j=0,1,2$. Apply the strict cutoff separately at each offset, retaining precisely $3\alpha<m_j<N$. In the conventions of the [moving cutoff](https://zenodo.org/records/21939906) and the [preceding replay](README.md), the weight before centering is
$$
w_j=\mu(3)\Lambda(n_j)\mu(m_j)\log(3/m_j)
   =\Lambda(n_j)\mu(m_j)\log(h+j/3).
$$
The actual term takes only $j=0$. The model takes half the sum of all eligible $w_j$, because $\phi(3)=2$.

For odd $h$, the integer $n_1$ is even and $n_2$ is a multiple of 3. Their nonzero $\Lambda$-weights thus come from powers of 2 and 3, respectively. For each offset, different $h$ give different $n_j$. Hence over any subset of odd cells, the total absolute off-diagonal **model** mass is at most
$$
\frac{\log N}{2}\left(\sum_{2^a<N}\log2+\sum_{3^a<N}\log3\right)
\le(\log N)^2,
$$
where $a\ge1$. This bound holds also for partial cells at the strict endpoint.

If $h$ is a squarefree semiprime, the diagonal vanishes for $3\mid h$. When $3\nmid h$, $\mu(3h)=-1$ and the actual term is $-\Lambda(N-3h)\log h$. Define the nonnegative mass
$$
W(N)=\sum_{\substack{h=rp,\ r<p\ {\rm odd\ primes}\\3\nmid h,\;\alpha<h,\;3h<N}}
                 \Lambda(N-3h)\log h .
$$
Then the actual slice is $-W(N)$ and the model slice is $-W(N)/2+M_{\rm off}(N)$, with $|M_{\rm off}(N)|\le(\log N)^2$. Thus
$$
\big|E_{\mathrm{odd}}(N)+W(N)/2\big|\le(\log N)^2. \qquad (1)
$$
The same identity and bound apply after restricting the cell set, with its corresponding $W$. In particular the $h=5p$ slice requires controlling the weighted two-prime contribution at $N=n+15p$.

## Pointwise counterexamples to the proposed separate budget

Fix an odd prime $r\ge5$. Write $W_r(N)$ for the part of $W(N)$ with smaller factor $r$, so $p>r$ is prime. This makes the parts for distinct $r$ disjoint. Fix $r$ before sending $X$ to infinity. Reindex by $n=N-3rp$. For $N\equiv2\bmod6$ the new variable has $n\equiv5\bmod6$. Dropping the moving cutoff for this counting argument only adds terms with $p\le\sqrt X/r$. These added terms cost $O_r(X^{3/2}\log X)=o_r(X^2)$ by the prime number theorem bound $\sum_{n\le X}\Lambda(n)=O(X)$ and the crude count of such $p$.

For $0\le y\le X$ put $\psi(y;6,5)=\sum_{n\le y,\ n\equiv5\bmod6}\Lambda(n)$. The prime number theorem for fixed modulus 6 gives $\psi(y;6,5)=y/2+o(X)$ uniformly for $y$ in this interval. Consequently
$$
\begin{aligned}
\sum_{\substack{N\le X\\N\equiv2\bmod6}}W_r(N)
&=\sum_{\substack{r<p\le X/(3r)\\p\ {\rm prime}}}
       \log(rp)\,\psi(X-3rp;6,5)+o_r(X^2)\\
&=\frac{X^2}{12r}+o_r(X^2).
\end{aligned}
$$
For the last equality, $\sum_{p\le t}\log(rp)=t+o_r(t)$ by the prime number theorem and $\pi(t)=o(t)$. Partial summation against $X-3rt$ on $[0,X/(3r)]$, followed by the factor $1/2$ from $\psi$, gives $X^2/(12r)$. Excluding $p\le r$ has cost $O_r(X)$. [Prime number theorem in arithmetic progressions](https://kskedlaya.org/ant/chapter-5.html)

For the comparison denominator use
$$
\mathfrak S(N)=2C_2\prod_{\substack{\ell\mid N\\\ell>2}}
                \left(1+\frac{1}{\ell-2}\right),\qquad
C_2=\prod_{\ell>2}\left(1-\frac{1}{(\ell-1)^2}\right),
$$
where products are over primes. Expanding the divisor product on $N\equiv2\bmod6$ gives coefficients $f(d)=\prod_{\ell\mid d}1/(\ell-2)$ for squarefree $d$ coprime to 6. For any such fixed $d$, the conditions $N\equiv2\bmod6$ and $d\mid N$ define one class modulo $6d$, with sum of its $N\le X$ asymptotic to $X^2/(12d)$. That sum is always at most $X^2/d$. The convergence of $\sum_d f(d)/d=\prod_{\ell\ge5}(1+1/(\ell(\ell-2)))$ permits taking the limit through the divisor sum. Each factor with $\ell\ge5$ cancels the corresponding factor of $C_2$. The prime 3 leaves the factor $3/4$. It follows that
$$
\sum_{\substack{N\le X\\N\equiv2\bmod6}}\mathfrak S(N)N
\sim \frac{2(3/4)X^2}{12}=\frac{X^2}{8}.
$$
[Singular-series convention, Huang–Li equation (2)](https://arxiv.org/html/2005.03811v2)

For a fixed finite set $R$ of primes at least 5, the error on just its smaller-factor classes has aggregate ratio tending to $-\sum_{r\in R}1/(3r)$ after division by the last denominator. This follows from (1) and the $W_r$ asymptotics. For the whole odd semiprime slice, its aggregate ratio has limit superior at most the same negative number, since $W\ge\sum_{r\in R}W_r$ and the off-diagonal error summed over targets is $O(X\log^2X)$.

Given $C>0$, choose a **fixed finite** $R$ with $\sum_{r\in R}1/(3r)>C$. The reciprocal primes diverge. If only finitely many individual targets violated $E_{\mathrm{odd}}(N)\ge-C\mathfrak S(N)N$, the aggregate ratio would have limit inferior at least $-C$. This contradicts the bound from $R$. The same argument gives infinitely many violating targets for the slice with smaller factors restricted to that $R$. For example $R=\{5,7,11,13\}$ gives $852/5005>1/6$, so the threshold $-\mathfrak S(N)N/6$ already fails for those four classes. The summation is used to prove existence of counterexamples to a **uniform pointwise** claim. It gives no bound on the combined error at a specified target. [Divergence of the prime reciprocals](https://dlmf.nist.gov/27.11.E8)

**Consequence for the missing estimate.** The earlier modeled term is $M_0(N)=\mathfrak S(N)(N-\sum_{n<N}\Lambda(n)\mu(N-n))$. Since the absolute value of the shifted sum is at most $\sum_{n<N}\Lambda(n)=(1+o(1))N$, we have $M_0(N)\le(2+o(1))\mathfrak S(N)N$. For every $C>2$, there are arbitrarily large targets where the odd semiprime modulus-3 slice alone is below $-C\mathfrak S(N)N$. In the catalog comparison with uniform $o(N)$ errors, positive compensation of at least $(C-2-o(1))\mathfrak S(N)N$ from the other terms is necessary on those targets. Separate slice budgets that try to absorb this slice in the positive model term cannot supply the needed pointwise lower bound.

## Finite replay

At $N=9602$, $\alpha=48$ and $q=3$ the strict low-band replay gives the following. Divide all weights by $N$.

| Cell restriction | Actual | Model | Off-diagonal part of model | Actual minus model |
|---|---:|---:|---:|---:|
| $h=5p$, prime $p>5$ | −0.260914122 | −0.130185816 | +0.000271245 | −0.130728306 |
| All odd squarefree semiprimes | −1.051180871 | −0.523831557 | +0.001758879 | −0.527349314 |

The replay checks the direct cell enumeration against a separate traversal over prospective actual points and the powers of 2 and 3. Two partial cells leave exactly one of the respective model offsets, and a third fixture checks that equality at the moving endpoint excludes a nonzero diagonal term. Integer and rational arithmetic determine support and the four-prime coefficient. Logarithmic weights use floating-point summation. The limiting implication above is a hand proof. [Replay](replay_modulus3.py) · [Recorded output](MODULUS-3-REPLAY.txt)

~~~sh
python -B replay_modulus3.py
~~~

**Next check.** Retain the same modulus and target family, then combine the odd squarefree semiprime and higher-factor cells before bounding. Test whether the positive odd-$\Omega(h)$ contributions can compensate the semiprime deficit on the very same targets, or whether other modulus rows or the even-cell model must supply part of that compensation.
