# Goldbach moving-prefix error and balanced semiprime cofactors

23 November 2026 · Codex research checkpoint

The master question is whether every even integer greater than two is a sum of two primes. This checkpoint reproduces and refines one finite decomposition, proves a uniform estimate on a specified subrange, and leaves the remaining signed pointwise estimate open. It also records one exact transfer for twin primes and a source audit of a named Dirichlet-GRH dependency. An independent replay and a targeted hand review are recorded below.

## Pointwise error and normalization

Let $N$ be even, $m=N-n$, $\alpha\ge 1$, and let $q$ be squarefree with $(q,N)=1$. Retain $1\le n<N-\alpha q$. Put $h=\lfloor m/q\rfloor$ and use the same weight $\mu(q)\Lambda(n)\mu(m)\log(q/m)$ in the actual and model terms. The actual term has the additional condition $q\mid m$. The model uses every integer in the eligible prefix, with weight divided by $\phi(q)$. Sum actual minus model with their signs, applying the same restrictions on $(q,h)$ to both. This preserves the full-prefix center and the reduced diagonal residue. [Huang–Li, equation (18) and the twisted hypothesis](https://arxiv.org/html/2005.03811v2) · [Moya's moving-cut correction](https://zenodo.org/records/21939906)

On the actual progression, $m=qh$ and every nonzero summand simplifies to $-\Lambda(n)\mu(h)\log h$. Every actual squarefree semiprime summand is negative. In a model cell the sign still depends on $\mu(m)\mu(q)$. The cell can have a nonzero model contribution even when it has no actual contribution.

## GB-CELL-9602 · finite replay

The earlier Cloud audit supplied the original fixture and prime/composite parent tally. This replay uses $N=9602$, $\alpha=\lfloor\sqrt N/2\rfloor=48$, and $2\le q$ with $4\alpha q<N$. Entries are divided by $N$. The script also splits each cofactor class by prime versus composite modulus.

| Cofactor cell $h$ | Actual / $N$ | Model / $N$ | (Actual − model) / $N$ | Actual terms | Model terms |
|---|---:|---:|---:|---:|---:|
| Prime | 2.530939668 | 0.644403606 | 1.886536062 | 508 | 2759 |
| Squarefree semiprime | −3.208347923 | −0.691305915 | −2.517042008 | 638 | 4628 |
| Squarefree with at least three prime factors | 0.799455639 | 0.291432899 | 0.508022740 | 159 | 2237 |
| Nonsquarefree cell | 0 | 0.064726117 | −0.064726117 | 0 | 5967 |
| **Total** | **0.122047384** | **0.309256707** | **−0.187209323** | | |

At prime moduli the semiprime cell error is $-2.185897278N$, and the error from squarefree cells with at least three factors is $+0.484793520N$. The full partition recovers the previous low-band total. The replay puts the semiprime error below $-N$ at this finite target under this cutoff rule. The asymptotic lower bound remains open.

The moving cutoff, residue membership, factorization and term counts use integer arithmetic. Weighted sums use binary64 logarithms and compensated summation. The script compares two traversals, including an independent divisor enumeration for the actual sum and a direct check of the strict inequality for the model. Python 3.14.7 ran the default replay, an all-moduli check at $\alpha=97$, and a fractional-cutoff check at $N=200,\alpha=5/2$. The default alone is the prior Cloud fixture. [Replay script](replay_goldbach.py) · [Recorded default output](REPLAY.txt)

~~~sh
python -B replay_goldbach.py
python -B replay_goldbach.py --target 9602 --alpha 97 --band all
python -B replay_goldbach.py --target 200 --alpha 5/2 --band low
~~~

## GB-CELL-BALANCED · uniform hand proof

Fix $B,K\ge0$ and $C>1$. Use $\alpha=\sqrt N/(\log N)^K$. Retain the modulus window
$$
\frac{\sqrt N}{(\log N)^B}\le q<\frac{N}{\alpha}
$$
and the cells $h=rs$ with distinct primes $r<s\le Cr$. The sum of absolute term weights on **each** side, with the same center as above, is
$$
O_{B,K,C}\!\left(\frac{N(1+\log\log N)}{\log N}\right)=o(N)
$$
uniformly in each large even $N$. The bound also holds after further restrictions on either side's included terms. This is a hand-derived bound using the interval form of Brun–Titchmarsh. [Montgomery–Vaughan, Theorem 2](https://doi.org/10.1112/S0025579300004708)

1. Cover the window by $O_{B,K}(1+\log\log N)$ intervals $[U,2U)$, truncating the last one. In each interval $h\le Y=N/U$, and $\log U$ and $\log Y$ are comparable to $\log N$. For $r\le Y^{1/4}$, counting integer pairs $r,s\le CY^{1/4}$ gives $O_C(Y^{1/2})$. For the other $r\le\sqrt Y$, there are $O(\sqrt Y/\log Y)$ prime choices for $r$ and $O_C(\sqrt Y/\log Y)$ prime choices for $s\le Cr$. Thus the total number of eligible $h$ is $O_C(Y/\log^2 N)$.
2. Fix one such $h$ with $(h,N)=1$. The actual prime values $n=N-qh$ lie in an interval of length at most $2Uh$, in the reduced class $N\bmod h$. Brun–Titchmarsh gives $O(Uh/(\phi(h)\log U))$ primes. Their total $\Lambda$-mass is $O(U)$, since $h/\phi(h)\le4$. The remaining logarithmic factor is bounded by $\log N$. Prime values with $(h,N)>1$ divide $N$, so there are $O(\log N)$ possibilities globally. Proper prime powers also contribute a global $o(N)$: each of the $O(\sqrt N\log N)$ possible $n$ has at most $\tau(N-n)=O_\epsilon(N^\epsilon)$ actual divisor choices with weight at most $(\log N)^2$. The same estimate includes the prime values dividing $N$. Hence the regular actual mass is $O_C(N/\log N)$ per interval, plus the global $o(N)$ bounded by $O_\epsilon(N^{1/2+\epsilon}\log^3 N)$.
3. In the model a cell is an interval of at most $q$ consecutive integers, possibly cut off by the strict endpoint. Its prime $\Lambda$-mass is $O(q)$ by Brun–Titchmarsh at modulus 1 and $\log q\asymp\log N$. For every exponent $e\ge2$, an interval of length $q$ contains at most $q^{1/e}+1$ positive $e$-th powers by concavity of $x^{1/e}$. Their total additional $\Lambda$-mass is $O((\sqrt q+1)\log^2N)=O(q)$ here. With $1/\phi(q)$ and the remaining logarithm the cost is $O(q\log N/\phi(q))$ per cell. The identity $q/\phi(q)=\sum_{d\mid q}\mu^2(d)/\phi(d)$ and the convergent product for $\sum_d\mu^2(d)/(d\phi(d))$ give $\sum_{U\le q<2U}q/\phi(q)=O(U)$. This yields $O_C(N/\log N)$ per interval on the model side too.

Each application of a counting bound enlarges the support of a sum of absolute weights. The strict endpoint remains in the discrepancy. The estimate covers comparable-factor semiprimes in the stated modulus window. A count of arbitrary semiprimes has an extra $\log\log Y$ and only one power of $\log Y$ in the denominator. The same absolute-weight argument then loses the saving.

The earlier Commons near-equal-factor argument uses the smaller slice $s-r\le h^{1/2-\eta}$ and obtains a power saving over a wider modulus range. The result here allows a fixed factor ratio and obtains a logarithmic saving in the window near $\sqrt N$. The same-complement obstruction explains why swapping factors within one complement does not create actual-side cancellation in prime-modulus rows. [Near-equal factors](../continuance/close-factor-cells.md) · [Prime-row sign obstruction](../continuance/prime-row-diagonal.md)

**Independent check, 23 November 2026.** The Cloud pointwise sieve audit ran the public replay and reproduced the $N=9602$ totals. Its targeted hand review checked the enlargement of partial model cells and the treatment of exceptional actual prime powers and primes dividing $N$. The reviewer reported no gap in those steps. This records a finite replay and a two-step review of the hand proof. [Revision reviewed](https://github.com/Sodelin/Research-Commons/blob/4b9c5356cd2c27f42b980723e6f3166c7e9037de/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/2026-11-23-cofactor-cells-1718z/README.md)

## GB-PREFIX-RESIDUAL · missing estimate

Subject to the corrected comparison and the ordinary short-divisor estimates recorded in the catalog, write the modeled main term as $M_0(N)=\mathfrak S(N)(N-\sum_{n<N}\Lambda(n)\mu(N-n))$. On a family with a uniform positive model margin, excise any proved $o(N)$ slices, including the one above, and retain the combined signed error $E_{\rm rem}(N)$. It suffices to prove, for each sufficiently large target in that family,
$$
E_{\rm rem}(N)\ge -M_0(N)+\eta N
$$
for a fixed $\eta>0$. This leaves room for the uniform $o(N)$ terms and proper prime powers. On even targets with $3\nmid N$, the mod-9 square lane gives a uniform margin because its $\Lambda$-mass is $(1/6+o(1))N$ and the shifted Möbius term vanishes on it. The required lower bound is for the combined residual at each target. The finite negative semiprime slice and the compensating positive prime and higher-factor slices illustrate why imposing the whole budget on each cell class is stronger. The bound for the remaining signed error is open. [Pointwise comparison](../second-pass/README.md) · [One-sided cutoff criterion](../adaptive-cutoff/README.md) · [Other removable cofactor slices](../continuance/README.md)

**Follow-up completed.** The [modulus-3 odd semiprime analysis](modulus-3-odd-semiprimes.md) replays the original $h=5p$ slice and bounds the two off-diagonal model offsets by the weights of powers of 2 and 3 on $N\equiv2\bmod6$. It proves infinitely many counterexamples to any fixed separate lower bound on the $\mathfrak S(N)N$ scale for the full odd semiprime slice. The next check tests for compensation from higher-factor cells at those same targets.

## TP-CHEN-SIGN · exact transfer on the restricted carrier

For fixed $0<b<1$, take the prime starts $p\le X$ with $p+2=rq$, $q$ prime, $r=1$ or prime, and $r\le q^b$. Let $C_b$ be their number, $L_b$ the sum of their partner Liouville signs, and $P$ the number of twin starts up to $X$. A composite partner has two distinct prime factors since $r<q$, so $\lambda(p+2)=\mu(p+2)$ throughout the carrier. Every twin start is in the carrier, and $2P=C_b-L_b$ exactly. Li–Liu's Theorem 1.2 supplies $C_{3/4}\gg X/\log^2 X$. A bound $L_{3/4}\le(1-\epsilon)C_{3/4}$ for a fixed positive $\epsilon$ would suffice. A shifted sum over all prime starts splits into this term and the signed off-carrier term. To use a full-carrier estimate one still needs lower control of that off-carrier term on the scale of the candidate count. In particular every square-divisible partner lane has already been discarded on this carrier. [Li–Liu, §1.2 and Theorem 1.2](https://arxiv.org/html/2606.05224v2#S1.SS2)

For a general Chen list the same count identity uses Liouville signs and the Möbius version has a prime-square correction. Here the factor restriction removes that correction identically, and the cited theorem supplies the carrier's size. [General Chen-list identity](../continuance/three-proof-checkpoints.md#twin-primes-exact-condition-on-the-restricted-list)

## RH-PRIMITIVE-EULER · pinned dependency audit

At the original RH source revision $40e56bab026552e089d7afcfeff08d2defb9c005$, the all-character critical-strip theorem in Main uses claimAll. Its strip proof invokes Claim.prim_zero to lift a zero of an imprimitive character to its primitive character. Claim.prim_zero uses the Mathlib change-of-level formula and Claim.factor_ne_zero. The latter uses $\|\psi(p)\|\le1$ and $\|p^{-s}\|=p^{-\Re(s)}<1$. Thus the use of strict $\Re(s)>0$ in this dependency is substantive. [Main](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Main.lean) · [ClaimStrip](https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean)

A hand check of the boundary shows why the primitive-zero implication cannot simply extend to $\Re(s)=0$. For the principal character mod 2 the removed Euler factor is $1-2^{-s}$. At $s=2\pi i/\log 2$ it vanishes, while the primitive character's function $\zeta(s)$ is nonzero by the pinned RH statement, since $s$ is neither a negative even integer nor 1 and has real part zero. This uses the already verified RH endpoint as a premise. The current audit inspected pinned source and derived the example by hand. Sutherland's separate kernel audit reports the five endpoint declarations with the three standard axioms. [Independent verification](https://math.mit.edu/~drew/grh/#what-was-verified) · [Axiom receipt](https://math.mit.edu/~drew/grh/audit.log) · [Research Commons RH reading index](../../../2026-11-23-rh-proof-reading/README.md)

**Secondary-track follow-up.** The [twin-prime and GRH handoff](secondary-track-handoff.md) gives a polylogarithmic periodic-weight obstruction for the restricted Chen carrier and an exact square-root criterion for the specified cubic-field Artin factor. It records the evidence and the next obligation for each.
