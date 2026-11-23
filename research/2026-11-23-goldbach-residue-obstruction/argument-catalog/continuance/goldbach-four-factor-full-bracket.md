# A full four-factor bracket charge at powers of two

Fix \(N=2^k\), \(L=\log N\), \(H=\sqrt N\), \(P=H^{21/20}=N^{21/40}\), and the original square-root block \(H/2<q,h\le H\). Keep \(m=qh\) squarefree coprime to \(N\) and \(n=N-m\) squarefree with \(\mu(n)=+1,\ \omega(n)\ge4,\ P^-(n)>Z_1\), using the original strict \(d>P\). This is a bound on the **full signed divisor bracket**, before choosing any individual admitted divisor. It applies to arbitrary additional swap-invariant original center masks. The doubled charge below is the one in the pointwise comparison after endpoint-parity transfer. [Pinned pointwise budget and exterior odd-semiprime sieve](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0) · [Strict center and completed endpoint parity](https://github.com/Sodelin/Research-Commons/commit/5ea16bc7f76f066d04b5077764ec67c57cf715ab)

On \(\mu(m)=-1\) and the further support \(P^-(n)\ge N^{1/6}\), the quadruple-or-higher row has doubled absolute paired weight less than \(0.039N\) at all sufficiently large powers of two. On both \(\mu(m)\) parities, the narrower moving condition \(P^-(n)\ge N^{1/4-L^{-3/4}}\) gives doubled absolute paired weight \(O(N/L^{1/2})\). These are bounds on the original arithmetic row and do not use an expanded Selberg square.

## Bracket when the endpoint has four factors

Since \(n<N\), six primes at least \(N^{1/6}\) are impossible under the extra support. The parity and lower factor count give \(n=p_1p_2p_3p_4\) with distinct primes \(p_1<p_2<p_3<p_4\). Write \(X=n/P\) and
\[
 B(n)=-\sum_{\substack{\ell\mid n\\\ell<X}}\mu(\ell)\log\ell .
\]
This is exactly the long-divisor bracket after using \(\mu(n)=+1\) and \(d=n/\ell\). The divisor \(1\) contributes zero. No triple is admitted: its product is at least \(N^{1/2}>X\), even before trimming. View the admitted prime divisors as vertices and the admitted products of two primes as edges. Every edge includes two admitted singleton vertices. No two edges can be disjoint, because their product would be \(n\) and both less than \(X<\sqrt n\). Thus the edges lie in a star or triangle. In a star the excess of the edge-log sum over the corresponding singleton-log sum is at most \(2\log p\) at its center \(p<X\), and in a triangle the excess is at most the sum of the three vertex logs. Either is at most \(\log n\). Extra singleton weights can only help the negative side. The positive part is bounded by the full singleton sum. Therefore
\[
 |B(n)|\le\log n
 \tag{1}
\]
on the exact strict support. In unordered \(q<h\) pairs the original signed weight is \(\mu(h)(\log h+\mu(m)\log q)B(n)\), so the odd-\(m\) side retains \(\log(h/q)\).

## Count with the two least primes fixed

Fix the actual two least primes, and use the odd composite modulus \(M=p_1p_2\le\sqrt n<H\) with \(qh=N\bmod M\). The remaining variable \(t=(N-qh)/M\) is \(p_3p_4\), in particular \(N^{1/6}\)-rough. Use an auxiliary one-dimensional Selberg square in \(t\), at level
\[
 D_M=N^{997/3000}/\sqrt M
\]
with odd sieve primes excluding the two factors of \(M\). This has \(D_M<N^{1/6}\). Its reciprocal diagonal norm is \((2\Pi+o(1))/\log D_M\), where \(\Pi=\prod_{p>2}(1+1/[p(p-1)])\), by the same diagonal Euler product as the pinned odd-semiprime auxiliary sieve. Both omitted factors tend to infinity, with uniform \(1+o(1)\) effect. On the original support the square is one, and it is nonnegative on the enlarged counting support. [Pinned Selberg quadratic norm and composite-modulus count](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0)

For each pair \(a,b\) of auxiliary sieve indices, count the unit hyperbola at the full composite odd modulus \(M[a,b]\). The oddness of both \(q,h\) gives rectangle area divided by four after the odd-progression substitution, and the error is \( (M[a,b])^{1/2+o(1)}(1+H/(M[a,b]))\). In the grid count for the odd part use the nonnegative weight \((\log(h/q))_+\), whose integral divided by \(N\) on the square is \(J=3/8-(\log 2)/2\). The main factor before \(B(n)\) is at most
\[
 \frac{N(J+o(1))}{4M}\frac{2\Pi+o(1)}{\log D_M}.
\]
The last upper bound uses \(\varphi(M)/M\le1\) after evaluating the **signed** opened sieve sum through its positive diagonal.

Using \(|\lambda_a|\le1\) and \(\sum_{a,b\le D}[a,b]^{-1/2}\ll D\), the error at a fixed \(M\) is
\[
 N^{o(1)}(M^{1/2}D_M^3 + H M^{-1/2}D_M).
\]
These two powers equal \(N^{.997}/M\) and \(N^{5/6-.001}/M\). Summation over \(p_1<p_2\) has at most divisor multiplicities at \(M\), and the reciprocal sums and the log weights cost only \(N^{o(1)}\); hence the total error is power-saving.

Let \(x=(\log p_1)/L,\ y=(\log p_2)/L\), and \(A=997/3000\). Since \(p_3,p_4\ge p_2\), the exact support implies \(x+3y\le1\). Dropping other conditions after (1), and doubling, gives
\[
 2\big|\text{signed odd-\(m\) charge}\big|
 \ \le\ (J\Pi I+o(1))N,\qquad
 I=\!\!\int_{\substack{1/6\le x\le y\\x+3y\le1}}
      \frac{dx\,dy}{xy(A-(x+y)/2)}.
 \tag{2}
\]
The same bound holds for doubled absolute paired weight itself. Mertens gives this upper integral using the product harmonic measure of the fixed two primes on their fixed positive exponent rectangle. The boundary planes have measure zero, and the diagonal can be omitted or enlarged.

For an exact rational constant check, cover \([1/6,1/4]\times[1/6,5/18]\) by squares of step \(s=1/432\). Keep squares with lower vertices \(x_i,y_j\) satisfying \(x_i\le y_j+s\), \(x_i+3y_j\le1\). Their integrals are at most \(s^2/[x_i y_j(A-(x_i+y_j+2s)/2)]\). Round each of the 946 terms upwards to the nearest multiple of \(10^{-6}\). The rounded sum is \(985407/10^6\). For verification, the exact arithmetic is:
    from fractions import Fraction as F
    s, A, total = F(1,432), F(997,3000), 0
    for i in range(36):
        x = F(1,6) + i*s
        for j in range(48):
            y = F(1,6) + j*s
            if x <= y+s and x+3*y <= 1:
                cap = 10**6*s*s/(x*y*(A-(x+y+2*s)/2))
                total += -(-cap.numerator // cap.denominator)
    assert total == 985407
    assert F(969,25000)*F(total,10**6) < F(39,1000)

Here \(J\Pi<969/25000\) uses the pinned rational \(J<57/2000\), \(\Pi<34/25\). This proves the strict \(0.039N\) cap including the \(o(N)\) term for sufficiently large \(N\). The grid verifies a constant in the hand inequality (2), separate from any finite-target Goldbach computation.

## Both block parities in a thin balanced range

Fix any \(\eta=o(L^{-1/2})\) with \(\eta\ge0\), and impose \(P^-(n)\ge N^{1/4-\eta}\). The preceding four-factor bracket and modulus apply. The two least primes satisfy
\[
 N^{1/4-\eta}\le p_1,p_2\le N^{1/4+\eta/3}
\]
by \(x+3y\le1\). Uniformly in this moving range their harmonic prime mass is \(O(\eta+1/L)\) by Chebyshev and partial summation. Both parity weights \(|\log h+\mu(m)\log q|\) are at most \(L\). Use this bound and (1) with the same auxiliary rectangle count (without the \(J\) weight). Since \(\log D_M\gg L\), the doubled absolute charge is
\[
 O\!\left(N L(\eta+1/L)^2+N^{.997+o(1)}\right)=o(N).
\]
In particular \(\eta=L^{-3/4}\) gives the claimed \(O(N/L^{1/2})\). This controls that exact full-bracket subrange in either \(\mu(m)\) row. On the broader \(N^{1/6}\)-rough support the \(0.039N\) charge uses the odd-\(m\) logarithmic ratio. Even-\(m\) beyond the thin range, lower least-prime ranges, and the higher factor counts they permit remain in the signed budget. These are hand proofs with an exact rational check of one constant and no new Lean verification.

## A full-bracket zero filter at all even factor counts

On the original \(\omega(n)\ge4\) support, the endpoints \(n\le P^{3/2}=N^{63/80}\) have absolute weight \(N^{63/80+o(1)}\) by the fixed-product divisor bound. In the rest put \(X=n/P\). Call a prime factor inactive if it is at least \(X\), respecting equality at the strict divisor cutoff. If there are two such factors \(p,r\), their remaining squarefree product is
\[
 a=n/(pr)\ \le P^2/n<X.
\]
Here \(\omega(a)\ge2\). Every divisor of \(a\) is admitted and none involving \(p\) or \(r\) is admitted, so the full bracket equals \(-\sum_{\ell\mid a}\mu(\ell)\log\ell=0\). Three inactive factors are impossible because \(X^3>n\). If one factor \(p>P\) occurs, similarly \(n/p<X\) and the full bracket vanishes, since \(\omega(n/p)\ge3\). Thus any nonzero bracket has at most one inactive prime, and that prime, if present, lies in \([X,P]\). This holds in both \(qh\) parities and also at all higher even endpoint factor counts.

In the one-inactive-prime case write \(a=n/p\). The complete divisor-log sum of \(a\) vanishes. On \(\mu(n)=+1\) one has \(\mu(a)=-1\), hence the original remaining bracket has the exact alternative form
\[
 B(n)=\sum_{\substack{\ell\mid a\\\ell\ge X}}\mu(\ell)\log\ell
      =-\sum_{\substack{b\mid a\\b\le P/p}}\mu(b)\log\frac{n}{pb}.
\]
Equality at \(pb=P\) is included. This puts the logarithmic summands on \(pb\le P\) but retains the prime test \(p\), the original endpoint parity and the one-inactive-prime selection. No signed determinant bound for this partly regrouped row is inferred from the index cutoff alone.
