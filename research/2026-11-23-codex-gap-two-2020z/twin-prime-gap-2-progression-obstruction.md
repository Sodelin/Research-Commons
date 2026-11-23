# A progression-count obstruction for the separated gap-2 block

Bounded-error unweighted interval estimates leave room for a signed separated-pair sum above the required scale. There are Boolean pair-count arrays with bounded error on every interval in each relevant refined progression and with a signed excess of order at least $RQ^2/(\log^4 X\log\log X)$. The required scale is $RQ^2/\log^5X$. A second test retains the common prime sequence and quantifies the loss in an operator-norm bound.

## What the shift average supplies

Use $R=X^{1/4}$, $Q=X/(4R)$, $h=Q/\log^6 X$, $w=(\log X)/100$, $W=\prod_{\ell\le w}\ell$, and the exactly centered $f$ from the [scale and correlation checkpoint](twin-prime-gap-2-scale-and-correlation.md). Write $L=\log X$, $J=\log w$, and $T=RQ^2/L^5$. For $h<d<Q$, put $I_d=\{q\in\mathbb Z:Q<q\le 2Q-d\}$ and

$$
 A_{r,d}(q)=\mathbf1_{\mathbb P}(rq-2)\mathbf1_{\mathbb P}(r(q+d)-2),
 \qquad a_d(q)=f(q)f(q+d).
$$

The actual separated quadratic sum is $2\sum_{R<r\le2R}\sum_{h<d<Q}\sum_{q\in I_d}a_d(q)A_{r,d}(q)$. The switched variables are $p=rq-2$ and $k=rd$. An interval on $q\equiv a\bmod W$ gives an interval on $p\equiv ra-2\bmod rW$. The divisor condition $r\mid k$ and both cofactor weights stay in the sum.

Mikawa’s mean-value theorem averages the error in the $\Lambda(p)\Lambda(p+k)$ count over all even shifts up to $X$, in reduced classes with modulus up to $X^{1/2}/(\log X)^{B(A)}$. It gives a total bound $O_A(X^2/(\log X)^A)$. In the cells $(r,k)=(r,rd)$ used here, even the sum of the trivial bounds for the counts and their main terms is $O(RQ^2L^2)=o_A(X^2/L^A)$. There are $O(RQ)$ cells and each count has $O(Q)$ available entries. The all-shifts budget can therefore absorb the entire sampled set. The argument below also tests a much stronger input in which each sampled cell has accurate interval counts. [Mikawa, theorem on p. 378](https://tsukuba.repo.nii.ac.jp/records/16157)

## Accurate counts with a large signed excess

Use the usual two-form local density on each class $q\bmod W$ as a prescribed comparison profile. Write $\rho=(W/\phi(W))^2/L^2\asymp J^2/L^2$, $m_r(q)=\mathbf1_{(rq-2,W)=1}$, and $g_r(q)=L/\log(rq-2)$. For squarefree $e$ with $(e,rW)=1$, put $\alpha(e)=\prod_{\ell\mid e}(\ell-2)^{-1}$, including $\alpha(1)=1$. The profile is

$$
 b_{r,d}(q)=\rho\,\theta_r\,m_r(q)m_r(q+d)g_r(q)g_r(q+d)
      \sum_{\substack{e\mid d,\ e\ {\rm squarefree}\\(e,rW)=1}}\alpha(e),
$$

where

$$
 \theta_r=\prod_{\substack{\ell>w\\\ell\mid r}}(1-1/\ell)^{-2}
       \prod_{\substack{\ell>w\\\ell\nmid r}}
                 \frac{\ell(\ell-2)}{(\ell-1)^2}.
$$

Indeed the two forms on $q=a+Wj$ are constant modulo primes of $rW$, and on admissible classes neither constant vanishes. At primes outside $rW$ their roots coincide exactly when the prime divides $d$. The profile includes the varying logarithms of both prime arguments. It vanishes on forbidden classes and satisfies $b_{r,d}(q)\asymp\rho$ uniformly on allowed classes. For this last bound the factors above $w$ attached to $rd$ have total logarithm $O(L/(w\log w))$ by counting their prime divisors.

The signed sum of the profile is $o(T)$. Here are the estimates needed for that assertion. Take $D=X^{1/50}$ and truncate the sum over $e$ at $D$. For $d\ne0$, Rankin's bound gives an omitted factor at most

$$
 D^{-1/2}\prod_{\substack{\ell\mid d\\ \ell>w}}
       (1+\sqrt{\ell}/(\ell-2))=X^{-1/100+o(1)}.
$$

The truncated kernel is uniformly bounded, including at $d=0$, by $\rho\cdot O(1)\prod_{w<\ell\le D}(1+1/(\ell-2))\ll 1$. By $\sum|f|^2\ll Q/L$, extending the truncated sum to all ordered pairs costs $O(RhQ/L)=O(RQ^2/L^7)$. Up to these errors, the signed profile sum is the sum over $r,e$ of $\rho\theta_r\alpha(e)$ times

$$
 \sum_{v\bmod e}\left|\sum_{q\equiv v\bmod e}f(q)m_r(q)g_r(q)\right|^2.
$$

For each $e\le D$, let $u_e$ and $v_e$ be the uniform probability masses on the reduced classes and all classes modulo $e$. The vector of inner sums over the classes has the form

$$
 A_r(u_e-v_e)+B_r v_e+\epsilon_{r,e},
 \qquad |A_r|\ll Q/L,\quad |B_r|\ll Q/L^2,\quad
 \|\epsilon_{r,e}\|_1\ll We\sqrt Q L^2.
$$

To see this, sum over the reduced classes modulo $W$ on which $m_r=1$ and use the prime number theorem in the combined class modulo $We$. Partial summation weights it by $g_r=1+O(1/L)$, whose variation is $O(1/L)$. The subtracted constant in $f$ has main mass uniform modulo $e$, from interval counts and the same prime number theorem for $c_a$. Replacing each occurrence of $g_r$ by $1$ in the two main masses changes them by $O(Q/L^2)$, so their difference is $B_r$ of that size. The two vectors being compared have total absolute mass $O(Q/L)$. Therefore their squared-norm errors summed over $e\le D$ are $O(WD^2Q^{3/2}L)$ per $r$, with a power saving after normalization.

Since $\|u_e-v_e\|_2^2=1/\phi(e)-1/e$, the weighted sum of these squared norms is $O(w^{-2})$ by taking the difference of the Euler products with factors $1+1/((\ell-2)(\ell-1))$ and $1+1/((\ell-2)\ell)$. The weighted sum for $\|v_e\|_2^2=1/e$ is bounded. Thus the signed profile contributes $O(RQ^2J^2/L^6)=o(T)$. This uses Dirichlet GRH only for the one-prime progression counts of $q$. [Lee, prime number theorem in progressions](https://arxiv.org/abs/2301.13457)

Now construct interval-count errors while keeping the exact weights $a_d$. Use $r$ coprime to $W$, of which there are $\asymp R/J$ in the row interval. For each such $r$ the classes with both $q$ and $rq-2$ coprime to $W$ occupy a fraction $\asymp J^{-2}$ of all classes and a fraction $\asymp J^{-1}$ of reduced classes. In $(9Q/8,5Q/4]$ choose primes $q$ in those classes for which $q+W$ is composite. There are $\gg Q/(LJ)$ choices, uniformly in $r$, by the prime number theorem in the classes modulo $W$. The excluded prime pairs $q,q+W$ number $O(QJ/L^2)=o(Q/(LJ))$. This follows from the two-form upper-bound sieve, whose product differs from the generic dimension-two product by at most $\prod_{2<\ell\mid W}(\ell-1)/(\ell-2)\ll J$. In $(7Q/4,15Q/8]$ there are $\gg Q/J^2$ integers $q'$ with residue in the allowed set for that $r$ and with both $q',q'+W$ composite. Removing prime values costs $O(Q/L)$. [Fundamental lemma, Corollary 19](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/)

Each choice determines the even difference $d=q'-q>h$ and an edge from $q$ to $q+W$ in the same refined progression on $I_d$. Both endpoints and their translates by $d$ remain in the block. At a fixed $r,d$ the edges are disjoint, with prime starts and composite ends. The signed weight changes by exactly

$$
 a_d(q+W)-a_d(q)=c_{q'\bmod W}\asymp J/L.
$$

Move $t$ of profile mass from the start to the end of each edge, for a sufficiently small fixed multiple $t$ of $\rho$. The resulting array stays in $[0,1]$. In each class modulo $W$, an interval cuts at most two disjoint edges of length $W$, so the interval count changes by at most $2t$. The signed sum, counting both orders, increases by

$$
 \gg \frac{R}{J}\frac{Q}{LJ}\frac{Q}{J^2}\frac{J^2}{L^2}\frac{J}{L}
   =\frac{RQ^2}{L^4 J}.
$$

If only prime $r$ are used for the perturbation, the same calculation with $R/L$ in place of $R/J$ gives an increase $\gg T$.

The array can have Boolean entries. Order each refined class by $q$, let $S_j$ be its cumulative perturbed mass, and take successive differences of $\lfloor S_j+u\rfloor$ for an offset $0\le u<1$. Every interval then has an additional discrepancy less than $1$, and the mean over $u$ of each entry equals its real mass. There is a choice of offsets for which the signed sum is at least its mean. This is an existence argument. Consequently the Boolean array has $O(1)$ error against the prescribed profile on every interval of every sampled $p\equiv ra-2\bmod rW$, yet its separated sum exceeds the scale $T$ by a factor of order at least $L/J$. The profile sum just bounded and the full local model $K_\infty$ in the earlier checkpoint each contribute $o(T)$. Even adding $\log p\log(p+k)$ to the interval diagnostic costs only $O(L^2)$ per class by partial summation.

The constructed entries specify pair counts separately at each $(r,d)$. A genuine prime sequence imposes additional relations across those cells. The obstruction is to an inference using interval counts as its data, including endpoints and refined progressions, with the actual cofactor weights.

## A test retaining the common prime sequence

A different approach uses the actual common prime vector and the signed rows as a linear operator. On the integer interval $X/4-2<n\le X-2$, let

$$
 v_r(n)=m_r(q)f(q)\ \text{if } n=rq-2,\quad v_r(n)=0\ \text{otherwise},
 \qquad (Bz)(r)=\langle z,v_r\rangle.
$$

Let $u$ be the prime indicator minus its empirical mean in each class modulo $W$ on that interval. Every $v_r$ has mean zero in each such class, by the exact centering of $f$ and the fact that $q\mapsto rq-2\bmod W$ depends only on $q\bmod W$. The actual full quadratic sum is $\|Bu\|_2^2$. The prime number theorem and the uniform bound $o(1)$ for the class means give $\|u\|_2^2\asymp X/L$.

Even on the subspace of vectors with these class means zero, a single row with $r$ prime has $\|v_r\|_2^2\gg Q/(LJ)$. Its prime cofactors in allowed classes alone supply that amount by Dirichlet GRH. Taking $v_r/\|v_r\|_2$ as an input gives this lower bound for the squared operator norm. Thus replacing the quadratic sum by the best operator norm times $\|u\|_2^2$ has a right-hand side at least of order $RQ^2/(L^2J)$, a factor $L^3/J$ above $T$. This test retains the signs and the common prime sequence and isolates the loss from using only its norm and the local centering.

## The estimate still needed

For actual primes, the signed error against the displayed profile must satisfy

$$
 2\sum_{R<r\le2R}\sum_{h<d<Q}\sum_{q\in I_d}
       f(q)f(q+d)\big(A_{r,d}(q)-b_{r,d}(q)\big)\ \le\ o(T).
$$

At this scale the profile bound makes this equivalent to the requested upper bound with $K_\infty$. The two tests show where additional information is needed about the correlation between the pair errors and the cofactor weights.

For the Goldbach block in which both factors are of order $\sqrt N$, the same switch sends the endpoints $N-rq,N-r(q+d)$ to a pair at shift $rd$ with the first endpoint congruent to $N\bmod r$. Even an extension of Mikawa's modulus range to this block would let the entire sampled set, of trivial total weight $O(N^{3/2}\log^2 N)$, fit within the all-shifts budget. Moving both cofactors by $W$ preserves the difference and the refined progression on the interior. Applying the interval-count obstruction there still requires a lower bound for the change in the specific Goldbach weight. The operator test likewise requires the squared norm of its signed row after local projection. [Research Commons progress, separated prime pairs](https://github.com/Sodelin/Research-Commons/blob/main/communications/2026-11-23-codex-number-theory-progress.md#goldbach-local-prediction-for-separated-prime-pairs-at-1926-utc)

The constructions and estimates above are hand arguments. The imported arithmetic inputs are the cited sieve, Mikawa’s theorem for comparison, and the Dirichlet-GRH prime number theorem in progressions. The comparison profile is a local density. The Boolean array is a mathematical example, and this checkpoint adds no finite search or Lean verification.
