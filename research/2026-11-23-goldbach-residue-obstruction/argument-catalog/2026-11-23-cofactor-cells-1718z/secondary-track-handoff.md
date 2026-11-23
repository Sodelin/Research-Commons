# Twin primes and GRH continuation

23 November 2026 · Separate research subagent findings, integrated by the pointwise Goldbach thread

## TP-PERIODIC-CARRIER-001 · a quantitative obstruction for the Li–Liu carrier

Let $\mathcal C(X)$ be the set of prime starts $p\le X$ for which $p+2=rq$, with $q$ prime, $r=1$ or prime and $r\le q^{3/4}$. Write $C=|\mathcal C(X)|$. Li–Liu give $C\gg X/\log^2 X$. On this set every two-factor partner is squarefree, so Liouville agrees with Möbius and $2P=C-L$, where $P$ counts twin starts and $L$ sums the partner signs on $\mathcal C(X)$. A fixed proportional gap $L\le(1-\epsilon)C$ would suffice for infinitely many twin primes. [Li–Liu, Theorem 1.2](https://arxiv.org/html/2606.05224v2#S1.SS2)

**Hand result.** For every fixed $A>0$ and all sufficiently large $X$, uniformly for integers $M\le(\log X)^A$,
$$
C-O_A(\log\log X)\ \le\
 \inf_{w:\, M\text{-periodic}}\ \sum_{p\le X}
 \big|\mathbf{1}_{\mathcal C(X)}(p)-w(p)\big|
 \ \le\ C .
$$
The sum is over primes and the weight may be complex and depend on $X$. Thus periodic weights at this scale cannot approximate the carrier indicator with error $o(C)$, or even with a fixed proportional saving over $C$. This rules out a transfer by that $L^1$ approximation route.

For the proof, fix a reduced class $a\bmod M$, and let $n_a,c_a$ be its total and carrier prime counts through $X$. For a uniform prime in this class let $D$ count primes $\ell\le\log X$, $\ell\nmid 2M$, dividing $p+2$. By CRT and Siegel–Walfisz at moduli at most $M(\log X)^2$, the probability of one event is $1/(\ell-1)+O_A((\log X)^{-8})$, and the probability of distinct pairs is the corresponding product plus the same error. The power eight follows by taking a sufficiently strong Siegel–Walfisz remainder before dividing by the size of the original class. With $\sigma=\sum_{\ell\le\log X,\,\ell\nmid 2M}1/(\ell-1)$, the number of pairs is $O((\log X)^2)$, so
$$
\mathbb E[(D-\sigma)^2]\le\sigma+o(1).
$$
Mertens' theorem gives $\sigma\gg\log\log\log X$ uniformly: among $\ell>\log\log X$, the primes dividing $M$ remove at most $O_A(1/\log\log\log X)$ reciprocal weight since $\sum_{\ell\mid M}\log\ell\le\log M$. A carrier member has $D\le2$. Hence $c_a/n_a\ll_A1/\log\log\log X$ by Chebyshev, in particular $n_a\ge2c_a$ for all sufficiently large $X$.

For any value $w_a$ on that class, the error is at least
$$
c_a|1-w_a|+(n_a-c_a)|w_a|
\ge c_a+(n_a-2c_a)|w_a|\ge c_a .
$$
The nonreduced classes contain only prime divisors of $M$, at most $O_A(\log\log X)$ of the prime starts. Summing and testing $w=0$ gives the claim. One can also assign an abstract sign $+1$ to each carrier member and choose $\lfloor n_a/2\rfloor$ negatives from its complement, so every reduced class has signed sum of absolute value at most one at this cutoff. This model uses actual prime starts and free signs. It makes no assertion about multiplicative signs. [Siegel–Walfisz theorem](https://kskedlaya.org/ant/chapter-11.html) · [Reciprocal-prime estimate](https://dlmf.nist.gov/27.11.E8)

**Literature scope.** Lichtman's theorem for an average absolute shifted sum covers Möbius and Liouville. For $H=X^\theta$ with fixed $0<\theta<1$, its mean bound of order at most $X/(\log X)^{4/3-\delta}$ is above the $X/\log^2 X$ candidate scale, and an individual fixed shift can remain exceptional. The single-shift theorems in Carella v3 assume Hypothesis 2.1. [Lichtman, Theorem 1.1 and Remark 1.7](https://arxiv.org/pdf/2009.08969v2) · [Carella v3](https://arxiv.org/pdf/2206.12956v3)

**Next test.** Audit the centered signed discrepancy for the residue $-2\bmod d$ with power-sized $d$ in the fixed-residue variant of Murty–Vatwani. The shifted-Möbius distribution premise is still required. No finite computation or Lean check was used for the hand result above. [Murty–Vatwani and the fixed-residue variant](https://mrammurty-ai.github.io/TwinPrimes-Parity.pdf#page=5)


## GRH-ARTIN-WINDOW-001 · square-root criterion for one two-dimensional Artin factor

The starting point is the independently verified RH and Dirichlet-GRH statements and the [pinned imprimitive Euler-factor audit](README.md). The result here concerns the separate $S_3$ benchmark from the [existing compact-window reduction](../../../2026-11-23-rh-proof-reading/rh_nonabelian_v2/README.md). Let $K$ split $x^3-2$, let $\rho_{\rm std}$ be the standard two-dimensional representation, and put $D=-L'/L$ for its Artin factor. Retain the prior compact prime-power sum $B_r(X)$ and
$$
M_r(s)=\frac{(r^s-1)(r^s-r)}{s(s-1)}
$$
with fixed $r>1$ and removable values at 0 and 1 filled in.

**Hand result.** Artin RH for this one factor is equivalent to $B_r(X)=O_r(\sqrt X)$. For every open-strip zero $\zeta=\beta+i\gamma$ of multiplicity $m$, there are also the quantitative bounds
$$
\limsup_{X\to\infty}B_r(X)/X^\beta\ge m|M_r(\zeta)|,\qquad
\liminf_{X\to\infty}B_r(X)/X^\beta\le -m|M_r(\zeta)|.
$$
The fixed-window square-root estimate itself remains open. [Independent verification scope for the starting Dirichlet results](https://math.mit.edu/~drew/grh/#what-was-verified)

**Classical dependency.** Take $F=\mathbb Q(\sqrt{-3})$. A nontrivial character of the cyclic cubic $K/F$ induces $\rho_{\rm std}$, so Artin induction and reciprocity identify the factor with a nonprincipal Hecke $L$-function of $F$. Cox identifies $K/F$ as the ring class field of conductor 6. It is also the full ray class field modulo $(6)$ because the rational residue units modulo 6 are $\{\pm1\}$, already images of Eisenstein units. The unit groups at $(2)$ and $(3)$ have orders 3 and 6, and quotienting their product by the six Eisenstein units gives ray group of order 3. At the maximal proper divisors $(3)$ and $(2)\mathfrak p_3$, the residue-unit group has order 6 and is the image of the Eisenstein units. Therefore the inducing character has conductor $(6)$ and the Hecke parameter $|d_F|N(6)=108$. [Cox, Proposition 9.5 and Theorem 9.8](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf)

The logarithmic derivative bounds in Lagarias–Odlyzko are the analytic input. Lemmas 5.4 and 5.6 give contours with $D(s)=O(\log^2 T)$ on horizontal sides from $-1/2$ to $2$, by choosing heights at distance $\gg1/\log T$ from the zero ordinates. Lemma 6.2 bounds $D(-1/2+it)$ by $O(\log(2+|t|))$. The multiplier is $O_r((1+|t|)^{-2})$ in this strip. Shifting the Mellin integral gives the absolutely convergent formula
$$
B_r(X)=-\sum_\zeta M_r(\zeta)X^\zeta-M_r(0)+O_r(X^{-1/2}).
$$
The simple zero at 0 gives the constant term, since the completed factor is nonzero there by functional symmetry and positivity at 1. Classical Dedekind-zeta boundary nonvanishing with $\zeta_K=\zeta_F L^2$, and functional symmetry, exclude other boundary terms. Under Artin RH the zero sum is $O_r(\sqrt X)$ by the local zero count and multiplier decay. [Lagarias–Odlyzko, Lemmas 5.4, 5.6 and 6.2](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf#page=21)

For the two quantitative oscillation inequalities, the eta-product Mellin integral gives $L(s)>0$ for positive real $s$, so $\gamma\ne0$. The multiplier has no zeros in the open strip. Suppose one of $\pm B_r$ has eventual ceiling $C X^\beta$ for $0<C<m|M_r(\zeta)|$. Take the Mellin transform $G$ of the nonnegative tail given by subtracting that signed sum from the ceiling above a fixed $X_0$. Its continuation is $C X_0^{\beta-s}/(s-\beta)\mp D(s)M_r(s)$ plus an entire term. It has real residue $C$ at $\beta$ and a residue of magnitude $m|M_r(\zeta)|$ at $\zeta$. Landau's real-boundary theorem for a nonnegative tail gives convergence for $\Re s>\beta$, as $G$ has no real singularity there. Then $|G(\sigma+i\gamma)|\le G(\sigma)$ for $\sigma>\beta$. Multiplying by $\sigma-\beta$ and taking $\sigma\downarrow\beta$ contradicts the choice of $C$. In particular a zero with $\beta>1/2$ rules out a square-root ceiling for either sign. Functional symmetry excludes a zero with $\beta<1/2$ if none lies to the right.

There is also a correction for the prime-only trace window $P_r(X)$. At prime squares the traces are $2,2,-1$ on the three $S_3$ classes of Chebotarev densities $1/6,1/2,1/3$, with mean 1. Partial summation and setting $u=v^2$ in the weight integral give
$$
B_r(X)-P_r(X)=\tfrac12 M_r(1/2)\sqrt X+o(\sqrt X).
$$
Higher powers cost $O_r(X^{1/3}\log^2 X)$. Thus the same square-root criterion applies to the prime-only window, with this shift at the critical scale. This is a sourced hand derivation. It has no separate numerical zero experiment or Lean replay.

**Next test.** Isolate the Mellin residue inequality for nonnegative tails as an abstract theorem, with both signed ceilings as acceptance tests. The analytic prime-sum estimate for the benchmark remains a separate obligation.
