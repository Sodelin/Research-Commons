# Gap 2 after the first proof memo

The full Li–Liu list has the wrong scale for a fixed twin proportion under the usual prime-pair predictions. The range that carries Li–Liu’s positive sieve weight does have the right scale. On a block inside that range, congruence counts give the main term for a calibrated approximation. The remaining estimate involves two actual primes at separated cofactor values.

## Put the target at the right scale

Write $H=X/\log^2X$ and let $\mathfrak S_2$ be the twin singular series. In the [first memo](twin-prime-gap-2-proof-memo.md), $C,L,P$ denote the full candidate count, its sign sum, and the twin count. For a fixed odd prime $r$, Bateman–Horn for $q,rq-2$ predicts that the $r$ row has $\big(\mathfrak S_2(r-1)/(r(r-2))+o(1)\big)H$ entries. The factor cutoff $q\ge r^{4/3}$ removes finitely many $q$ in each fixed row. The singular series has one root at $2$ and at $r$, and two roots at other primes. The rows are disjoint as counts of starts because the cutoff forces $r<q$. Sum over any fixed finite set of $r$ and then enlarge the set. Divergence of $\sum_r1/r$ gives $C/H\to\infty$ **conditional on these fixed-row asymptotics**, with no uniform Bateman–Horn assumption. Since the ordinary upper-bound sieve gives $P\ll H$, this would force $L/C=1-2P/C\to1$. The additive target $C-L\gg H$ avoids that problem. [Bateman–Horn, 1962](https://doi.org/10.1090/S0025-5718-1962-0148632-7)

A constant proportion is appropriately scaled on a smaller family. Fix $\eta>0$ sufficiently small as in Li–Liu, set $\alpha=1/12$ and $\tau=3/7-\eta$, and take prime starts $\eta X<p\le X-2$. Retain every twin in this interval and the semiprime partners $p+2=rq$ with primes $X^\alpha\le r<X^\tau$ and $r\le q$. This forces $r<q$ and $r^4\le q^3$ for large $X$, since $q>\eta X^{1-\tau}$. Write $C_\sharp,L_\sharp,P_\sharp$ for counts on this family. Then $2P_\sharp=C_\sharp-L_\sharp$ and

$$
 0.036\,\mathfrak S_2 H\ \le C_\sharp(X)\ll H.
$$

For the lower bound, the indicator in (4.74) has precisely this support after removing the last two possible starts. The hand check below shows that the signed $T_1,\ldots,T_{12}$ expression in (6.2) still lower-bounds $4C_\sharp$, up to $O(X^{11/12})$. Li–Liu’s evaluation of that expression in §6 gives the stated lower bound by its positive margin in (6.49). [Li–Liu, §4.3 and §6](https://arxiv.org/html/2606.05224v2)

For the upper bound, uniformly for $r=1$ or an odd prime, two-form sifting up to $Y$ bounds the count of prime $q,rq-2$ by $O(Y/\log^2Y)$. Indeed, the numbers of forbidden residues are $1$ at $2$, $1$ at the exceptional prime $r$ when $r>1$, and $2$ elsewhere. Thus the sieve product is $O((\log z)^{-2})$ uniformly. The interval remainder for modulus $d$ is $O(2^{\omega(d)})$. The fundamental lemma with $D=Y^{1/2}$ and $z=Y^{1/20}$ then gives the upper bound, including $O(z+1)$ exceptions for prime values at most $z$. The error sum is $O(D\log(2D))$ by the divisor bound for $2^{\omega(d)}$. Apply this with $Y=X/r$ or to an interval of length $Y$ with comparable endpoints. For $C_\sharp$, sum over the power range using $\sum_{X^\alpha\le r<X^\tau}1/r=O(1)$, and use the $r=1$ case for twins. [Fundamental lemma, Corollary 19](https://terrytao.wordpress.com/2015/01/21/254a-notes-4-some-sieve-theory/)

## One block and the effect of screening out small divisors

Set $R=X^{1/4}$, $Q=X/(4R)$, and use $R<r\le2R$, $Q<q\le2Q$. For large $X$, this block is inside the preceding cutoffs. Let $S$ count pairs on the block with $r,q,rq-2$ prime. The upper bound above gives $S\ll RQ/\log^3 X$. Let $w=(\log X)/100$ and $W=\prod_{\ell\le w}\ell=X^{1/100+o(1)}$, with products over primes. Let $Z$ count the pairs with $r,rq-2$ prime and $(q,W)=1$. For each $r$ there are $\prod_{\ell\mid W}(\ell-\nu_\ell)$ allowed classes for $q\bmod W$, with $\nu_2=1$ and $\nu_\ell=2$ for $\ell>2$. Each class corresponds to $p=rq-2$ in one reduced class modulo $rW$. Counting those primes by verified Dirichlet GRH and summing the errors costs $O(RW\sqrt X\log^2X)=o(RQ/\log^3X)$. Consequently

$$
 Z\ \sim\ \frac{e^{-\gamma}\mathfrak S_2 RQ}{\log R\,\log X\,\log w}.
$$

Here $\gamma$ is Euler’s constant. The local factor is $\prod_{2<\ell\le w}(1-1/(\ell-1))\sim e^{-\gamma}\mathfrak S_2/\log w$. Thus the unweighted count after screening includes $\sim Z$ composite cofactors, exceeding the upper bound for true pairs by a factor of order $\log X/\log\log X$. [Dirichlet GRH audit](https://math.mit.edu/~drew/grh/#what-was-verified) · [Lee, PNT in progressions under GRH](https://arxiv.org/abs/2301.13457)

For each residue $a\bmod W$, let $c_a$ be the fraction of integers in $(Q,2Q]$ in that class that are prime. Set $f(q)=\mathbf1_{\mathbb P}(q)-c_{q\bmod W}$ there, and extend it by zero. On reduced classes, Dirichlet GRH gives $c_a=(1+o(1))W/(\phi(W)\log Q)$ uniformly. The other classes have $c_a=0$. The calibrated count $M=\sum_{r\ {\rm prime}}\sum_q c_{q\bmod W}\mathbf1_{\mathbb P}(rq-2)$ on the block therefore satisfies

$$
 M\sim\frac{\mathfrak S_2 RQ}{\log R\,\log Q\,\log X}.
$$

The exact correction is $E=S-M=\sum_{r\ {\rm prime}}\sum_q f(q)\mathbf1_{\mathbb P}(rq-2)$ on this block. The progression estimate for $M$ leaves $E$ undetermined.

## A short-difference bound and the surviving signed term

Let $K(q,q')$ count integers $r\in(R,2R]$ for which both $rq-2$ and $rq'-2$ are prime. Cauchy–Schwarz in the prime $r$ variable and enlargement of the sum of squares to all integer $r$ give $|E|^2\le(\pi(2R)-\pi(R))\sum_{q,q'}f(q)f(q')K(q,q')$. For a concrete local model let

$$
 K_W(q,q')=\frac{R}{\log^2 X}
    \prod_{\ell\mid W}\frac{1-\nu_\ell(q,q')/\ell}{(1-1/\ell)^2},
$$

where $\nu_\ell(q,q')$ counts the roots of $(rq-2)(rq'-2)\equiv0\bmod\ell$ in $r$. This depends only on the residue classes of $q,q'\bmod W$. Since $\sum_{q\equiv a\bmod W}f(q)=0$ exactly, $\sum_{q,q'} f(q)f(q')K_W(q,q')=0$. This identity concerns the local model.

Take $h=Q/\log^6 X$. The exact class centering gives $\sum_q f(q)^2\le\pi(2Q)-\pi(Q)\ll Q/\log X$. Also $|K-K_W|\ll R$, using the trivial bound for $K$ and Mertens’ product for $K_W$. For each integer difference use $\sum_q|f(q)f(q+d)|\le\sum_q f(q)^2$. This bounds the diagonal and short differences by

$$
 \left|\sum_{|q-q'|\le h}f(q)f(q')\big(K-K_W\big)(q,q')\right|
 \ll \frac{RQ^2}{\log^7 X}.
$$

The next estimate, sufficient for $E=o(RQ/\log^3X)$ on this block, is the one-sided bound

$$
 \sum_{|q-q'|>h}f(q)f(q')\big(K-K_W\big)(q,q')
 \ \le\ o\!\left(\frac{RQ^2}{\log^5 X}\right).
$$

Termwise absolute values in the expanded moment with the actual kernel already lose the required saving. Indeed, the calibrated mass on composite $q$ is $M-o(M)$, because $\max c_a=o(1)$ and $S=O(M)$. On these $q$, $|f(q)|=c_{q\bmod W}$. Another Cauchy–Schwarz inequality gives $\sum_{q,q'}|f(q)f(q')|K(q,q')\ge (M-o(M))^2/(\pi(2R)-\pi(R))\gg RQ^2/\log^5 X$, with the short differences negligible.

## The full local model also cancels at this scale

For distinct $q,q'$ put $K_\infty=(R/\log^2X)\prod_\ell(1-\nu_\ell(q,q')/\ell)/(1-1/\ell)^2$. The signed sum of this local model satisfies

$$
 \left|\sum_{|q-q'|>h} f(q)f(q')K_\infty(q,q')\right|
 \ll \frac{RQ^2(\log\log X)^2}{\log^6 X}.
$$

Here is the hand reduction using the same Dirichlet progression input. Put $\Delta=qq'(q-q')$. For $\ell>w$ the generic local factor is $\beta_\ell=\ell(\ell-2)/(\ell-1)^2$. The exceptional factor divided by $\beta_\ell$ is $1+b_\ell/(\ell-2)$ with

$$
 b_\ell=\mathbf1_{\ell\mid q}+\mathbf1_{\ell\mid q'}+
             \mathbf1_{q\equiv q'\not\equiv0\bmod\ell}.
$$

The last indicator uses residues in which both values are nonzero. Thus $K_\infty$ is $K_W\prod_{\ell>w}\beta_\ell$ times the squarefree-divisor expansion of $\prod_{\ell\mid\Delta,\,\ell>w}(1+b_\ell/(\ell-2))$.

Truncate that expansion at $d\le D=X^{1/50}$. For $q\ne q'$, the omitted factor is at most $D^{-1/2}\prod_{\ell\mid\Delta,\,\ell>w}(1+2\sqrt\ell/(\ell-2))=X^{-1/100+o(1)}$. The product bound uses $|\Delta|\ll Q^3$ and at most $O(\log X/\log w)$ primes above $w$ dividing it. The truncated kernel is $O(R)$ even at $q=q'$, since the weight sum over $d\le D$ is at most $\prod_{w<\ell\le D}(1+2/(\ell-2))\ll(\log D/\log w)^2$. The short-difference estimate therefore lets us evaluate the truncated sum over all pairs at cost $O(RQ^2/\log^7X)$.

For squarefree $d\le D$ coprime to $W$, let $u_d$ be uniform mass on reduced classes modulo $d$ and $v_d$ uniform mass on all classes. For a reduced class $a\bmod W$ and any $b\bmod d$ the sum of $f$ in the combined class is

$$
 \frac{\operatorname{Li}(2Q)-\operatorname{Li}(Q)}{\phi(W)}
       (u_d(b)-v_d(b)) + O(\sqrt Q\log^2X).
$$

This follows from GRH for primes in the combined class, ordinary interval counts for the subtracted constant, and $d<Q$ for classes divisible by a prime of $d$. The mass in nonreduced classes modulo $W$ is zero. The total absolute error over classes for each $d$ is $O(Wd\sqrt Q\log^2 X)$. In the quadratic form the other factor has total absolute mass $O(Q/\log X)$. Summing these errors over $d\le D$ gives a power saving because $WD^2\ll X^{1/20+o(1)}\ll\sqrt Q$.

For one prime $\ell\mid d$, the expectations of $b_\ell$ under $u_\ell u_\ell$, $u_\ell v_\ell$, and $v_\ell v_\ell$ are $1/(\ell-1)$, $2/\ell$, and $3/\ell-1/\ell^2$. Their signed combination with coefficients $1,-2,1$ is $1/(\ell^2(\ell-1))$. After dividing by $\ell-2$, the one-prime terms sum to $O(w^{-3})$. For $d$ with at least two prime factors, multiplicativity bounds the total absolute contribution by $O((\sum_{\ell>w}\ell^{-2})^2)=O(w^{-2})$. The $d=1$ term is zero. The prefactor and the two cofactor masses give $O(RQ^2(\log w)^2/\log^4 X)$ before this $O(w^{-2})$ factor. This proves the displayed bound.

The live estimate can therefore use $K-K_\infty$ in the separated-pair sum. It asks for a one-sided $o(RQ^2/\log^5 X)$ bound with the actual two-prime counts. Exact class centering, the local-factor cancellation, and the short-difference bound can inform a Goldbach block admitting this decomposition. A bound for its actual separated prime pairs has to be derived for its own kernel.

For testing a shift-average approach, take $d=q'-q>0$ and $p=rq-2$. By symmetry the actual separated sum equals

$$
 2\sum_{h<d<Q}\ \sum_{R<r\le 2R}\ 
  \sum_{\substack{rQ-2<p\le r(2Q-d)-2\\p\equiv-2\bmod r}}
 f\!\left(\frac{p+2}{r}\right)f\!\left(\frac{p+2}{r}+d\right)
 \mathbf1_{\mathbb P}(p)\mathbf1_{\mathbb P}(p+rd).
$$

All summation variables here are integers. The support of $f$ and primality of $p$ force $d$ even and $r$ odd. At shift $k=rd$, the original sum still restricts $r$ to divisors of $k$ and $p$ to one progression for each $r$, with the displayed interval and signed weights. These are the conditions a shift-average estimate must preserve.

The [progression-count checkpoint](twin-prime-gap-2-progression-obstruction.md) tests this transfer. It gives a signed counterexample to the interval-count inference and a quantitative obstruction to using only the operator norm of the actual correlation matrix.

## Hand check of the narrower sieve support

In Li–Liu (6.2), omit partners with a repeated prime factor at least $X^\alpha$, a prime factor at an exponent boundary, or $p+2>X$. On the rough support every such exception occurs with bounded multiplicity and their total contribution is $O(X^{1-\alpha})$. The last bound follows from $\sum_{\ell\ge X^\alpha}X/\ell^2=O(X^{1-\alpha})$ for repeated factors and $O(X^{1-\alpha})$ multiples for each boundary. Away from exceptions, each $T_j$ vanishes unless all factors are at least $X^\alpha$.

For a squarefree rough partner, let $a,b,c$ count factors in the exponent intervals $[\alpha,\beta)$, $[\beta,\gamma_0)$, and $[\gamma_0,1/3)$, with $\beta=1/7$, $\gamma_0=2/7$. The coefficients of $T_1,T_2,T_4,T_5,T_6,T_7,T_{11},T_{12}$ at this partner are their displayed counts $1,\mathbf1_{a=0},a+b+c,a+b,\binom a2,ab,\binom{a-2}{2},(a-2)_+b$, respectively, with the shifted binomial zero for $a<4$. The two least primes are fixed in $T_{11},T_{12}$ by the sifting condition. For a prime partner the full signed expression is $4$. For a semiprime with smaller factor at least $X^\tau$, $T_3$ subtracts $4$ from $4$. For the other semiprimes the expression is at most $4$, since the larger factor exceeds $X^{1/3}$ for large $X$.

For three or more factors, $T_8$ detects a least exponent at least $\gamma_0$, $T_9$ detects exactly one factor below exponent $1/3$, and $T_{10}$ detects triples with least exponent in $[\beta,\gamma_0)$. In $T_{10}$ the cofactor cutoff is $\sqrt{X/(p_1p_2)}$. For a triple it is automatic from $p_1p_2\le X^{(1+\gamma_0)/2}$ and $p+2>\eta X$. Four or more distinct factors fail this cutoff. If $a\ge2$, the two binomial terms have difference $2a-3$, and the signed expression is at most $-c$. If $a=1$, the expression before subtracting $T_9$ is $1-b-c$, and $T_9=1$ when $b+c=0$. For $a=0,b\ge2$, the expression is already nonpositive. For $a=b=0$, $T_8$ subtracts $2$, and either $c\ge2$ or $c=1$ and $T_9=1$. The case $c=0$ is impossible by the product bound. For $a=0,b=1$, $c\ge2$ suffices directly. If $c=0$ or $c=1$, the product bound forces exactly three factors, so $T_{10}=1$, with $T_9=1$ also when $c=0$. Thus three or more factors contribute nonpositively. This proves the claimed support bound before applying the paper’s analytic estimates. [Li–Liu, Propositions 4.6–4.7 and (6.2)](https://arxiv.org/html/2606.05224v2#S4.SS3)

The support check, the uniform upper bound, and the short-difference estimate are hand arguments using the cited theorems. The full-list scale obstruction is conditional on Bateman–Horn. The block’s progression estimates use the externally verified Dirichlet GRH. This checkpoint adds no finite search or Lean verification.
