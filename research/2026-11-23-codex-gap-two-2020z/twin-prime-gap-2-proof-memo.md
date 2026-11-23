# Goldbach and GRH at prime gap 2

**Verdict.** The Goldbach divisor regrouping gives an exact residual on the fixed-shift list, with a negligible contribution from any fixed range of smaller factors. Dirichlet GRH controls the errors in the unrestricted progression counts at the required scale. The count of pairs in which both the cofactor and the prime start are prime still needs a separate estimate.

## 1. The candidate list and its signs

Write $m=p+2$. Let $\mathcal C(X)$ be the starts $p\le X$ for which $p$ is prime and $m=rq$, with $q$ prime, $r=1$ or prime, and $r^4\le q^3$. The $r=1$ case includes every twin start up to $X$, including a pair whose larger prime exceeds $X$. In the composite case, the cutoff is equivalently $r\le m^{3/7}$, or $q\ge m^{4/7}$. It forces $r<q$, so the factorization is unique and prime squares are excluded. Li–Liu’s unconditional Theorem 1.2, with $a=7/4$ in (1.10), gives for all sufficiently large $X$

$$
 C(X):=|\mathcal C(X)|>0.036\,\mathfrak S_2\frac{X}{\log^2 X},
 \qquad
 \mathfrak S_2=2\prod_{\ell>2,\ \ell\ {\rm prime}}
                 \left(1-\frac{1}{(\ell-1)^2}\right).
$$

This is the theorem’s output cutoff. Its proof uses $\tau=3/7-\eta$ in (6.1) as an internal sieve parameter. [Li–Liu, (1.8), (1.10), Theorem 1.2 and §6](https://arxiv.org/html/2606.05224v2)

On any list of prime and semiprime partners, $\lambda(m)=(-1)^{\Omega(m)}$ counts prime factors with multiplicity in the exponent. It is $-1$ at a prime and $+1$ at a semiprime, including a square. If $P$ and $S$ count twins and semiprimes on the list, then $C=P+S$ and $L=\sum_{p\in\mathcal C(X)}\lambda(p+2)=-P+S$, giving $2P=C-L$. If squares are admitted on a broader list, the Möbius version is $2P=C-\sum\mu(p+2)-Q$, with $Q$ the number of square partners. Here $Q=0$ and $\mu=\lambda$ on the list. A fixed $\epsilon>0$ and $L\le(1-\epsilon)C$ along $X\to\infty$ would give $P\ge\epsilon C/2\to\infty$. [Research Commons sign reduction](https://github.com/Sodelin/Research-Commons/blob/cfbdb15bea07736c501e2ddc08296648bf66827e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/congruence-parity-euler-check.md)

## 2. Signed divisor regrouping at the fixed shift

Use the Goldbach actual-row identity on the squarefree partner $m=p+2$. Cut on the cofactor $h=m/d>m^{3/7}$, using the boundary of the Li–Liu list, and normalize the logarithm to work at counting scale. Then

$$
 A(X)=\sum_{p\in\mathcal C(X)}
       \sum_{\substack{d\mid m\\ h=m/d>m^{3/7}}}
       \mu(d)\mu(m)\frac{\log(d/m)}{\log m}
     =\sum_{p\in\mathcal C(X)}
       \sum_{\substack{h\mid m\\ h>m^{3/7}}}
       -\mu(h)\frac{\log h}{\log m}.
$$

A prime partner retains $h=m$ and contributes $1$. A semiprime retains $h=q,m$ and contributes $\log q/\log m-1=-\log r/\log m$. In the uncut four placements, the two prime-cofactor terms both have positive sign. Their sum cancels the $h=m$ term, and $h=1$ contributes zero. The cutoff removes exactly the $+\log r/\log m$ term, so swapping the prime factors gives no cancellation in the retained sum. Consequently

$$
 A=P-R,\qquad R=\sum_{\substack{p\in\mathcal C(X)\\p+2=rq,\ r>1}}
                    \frac{\log r}{\log(p+2)}.
$$

The needed bound in this form is $A\ge -R+\epsilon C/2$. [Goldbach actual-row regrouping](https://github.com/Sodelin/Research-Commons/blob/cfbdb15bea07736c501e2ddc08296648bf66827e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/prime-row-diagonal.md) · [Codex progress notes, paired factor placements at 18:50 UTC](https://github.com/Sodelin/Research-Commons/blob/main/communications/2026-11-23-codex-number-theory-progress.md#goldbach-paired-factor-placements-at-1850-utc)

**A controlled subrange.** First $C=o(\pi(X))$. For a fixed finite set of odd primes $\ell$, the prime number theorem in progressions and the Chinese remainder theorem give independent limiting events $\ell\mid p+2$ with probabilities $1/(\ell-1)$, as $p$ ranges over primes up to $X$. A candidate has at most two such divisors. The number of events has mean $M=\sum_\ell 1/(\ell-1)$ and variance at most $M$. Chebyshev bounds the limiting proportion with at most two by $M/(M-2)^2$ for $M>2$. Enlarge the fixed set after taking $X\to\infty$, so $M\to\infty$. Now, for any fixed $R_0$, the terms of $R$ with $r\le R_0$ contribute

$$
 O(\sqrt X)+O_{R_0}\!\left(\frac{C(X)}{\log X}\right)
 = o\!\left(\frac{X}{\log^2 X}\right)=o(C(X)).
$$

The first term covers $p\le\sqrt X$. For the rest $\log(p+2)\ge \tfrac12\log X$, and the preceding density bound applies.

**Where the pair estimate enters.** Put

$$
 S_r(X)=\#\{q\in\mathbb P:\ r^{4/3}\le q\le (X+2)/r,\ rq-2\in\mathbb P\},
 \qquad \mathbb P=\{\text{primes}\}.
$$

The inequality sought is exactly

$$
 \sum_{\substack{3\le r\le(X+2)^{3/7}\\r\ {\rm prime}}} S_r(X)
 \ \le\ (1-\epsilon/2) C(X).
$$

The $r=2$ row is empty because the only possible prime start would be $2$, and $m=4$ violates the factor cutoff. Dropping the cofactor-prime test in $S_r$ gives the unrestricted progression count $U_r$ of prime $p\equiv-2\bmod r$ with $r^{7/3}-2\le p\le X$. At $r=3$ this substitution already incurs

$$
 U_3(X)-S_3(X)\ \ge\ \pi(X;9,7)-1
             \ \sim\ \frac{\operatorname{Li}(X)}{6}.
$$

In that residue class, $p=7$ is below the cutoff. Every subsequent $p$ exceeds the cutoff and has $(p+2)/3>3$ divisible by $3$. Since $C=o(\pi(X))$, the substitution error divided by $C$ tends to infinity. Even with the logarithmic weight in $R$, this residue class alone inserts a spurious contribution of at least $(\log 3)(\pi(X;9,7)-1)/\log(X+2)$, of order $X/\log^2 X$.

Polymath’s parity argument uses factors such as $1-\lambda(p)\lambda(p+2)$. For prime $p$ this factor equals $1+\lambda(p+2)$, giving weight $0$ to twins and $2$ to the semiprimes on this list. Section 8 contrasts progression estimates with joint sums such as $f(n)\Lambda(n+2)$. [Polymath8b, §8, (142)–(149)](https://arxiv.org/pdf/1407.4897#page=68)

## 3. What GRH supplies

**Dirichlet.** The verified result covers Dirichlet $L$-functions. The GRH prime number theorem in progressions gives $\pi(t;d,a)=\operatorname{Li}(t)/\phi(d)+O(\sqrt t\log^2(td))$ for $(a,d)=1$, using a weakened error bound. Apply it to $U_r=\pi(X;r,-2)-\pi(\lceil r^{7/3}-2\rceil-1;r,-2)$. Summing the absolute errors over $r\le (X+2)^{3/7}$ gives $O(X^{13/14}\log^2 X)=o(C(X))$, at the required scale for the unrestricted rows. [Independent Lean audit of Dirichlet GRH](https://math.mit.edu/~drew/grh/#what-was-verified) · [Lee, prime number theorem in progressions under GRH](https://arxiv.org/abs/2301.13457)

**A specific Hecke extension.** Let $K$ be the $S_3$ splitting field of $x^3-2$ and $F=\mathbb Q(\sqrt{-3})$. The standard representation $\rho$ is induced from a nontrivial character of the cyclic group $\operatorname{Gal}(K/F)$. Induction of Artin $L$-functions and class field theory identify $L(s,\rho)$ with a finite-order Hecke $L$-function over $F$, and $\zeta_K=\zeta L(s,\chi_{-3})L(s,\rho)^2$. Assuming GRH for this additional $L$-function gives, by effective Chebotarev, $(|D|/6)\operatorname{Li}(X)+O_K(\sqrt X\log^2 X)$ primes of each Frobenius class $D$. The transposition class contains both $p=5$ and $p=53$, since both have quadratic character $\chi_{-3}(p)=-1$. Their partners $7$ and $5\cdot11$ have opposite signs on the list. These additional one-prime counts supply no estimate here for the joint primality in $S_r$. [Grenié–Molteni, effective Chebotarev under GRH, Theorem 1.1](https://air.unimi.it/handle/2434/634041)

Even the fixed-shift cancellation $T(X)=\sum_{p\le X}\mu(p+2)=o(\pi(X))$ reported by Lü–Wang–Wu leaves the restriction unresolved. If $B(X)$ sums the same signs over the excluded starts, $L=T-B$, so the required bound is $B\ge T-(1-\epsilon)C$. An estimate on $T$ alone leaves $B$ uncontrolled, even if the error on $T$ were $o(C)$. The fixed-gap candidate-scale inequality remains open. [Lü–Wang–Wu, Theorem 1](https://arxiv.org/html/2610.20242v1) · [Research Commons off-list condition](https://github.com/Sodelin/Research-Commons/blob/cfbdb15bea07736c501e2ddc08296648bf66827e/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/congruence-parity-euler-check.md#twin-primes-which-direction-of-error-is-needed-outside-the-list)

**Verification.** The divisor identities, subrange bound, and modulus-$9$ obstruction are hand arguments. The Li–Liu lower bound is imported from the cited preprint. This memo uses no finite search and adds no Lean verification. The external Lean audit pertains to Dirichlet GRH.

