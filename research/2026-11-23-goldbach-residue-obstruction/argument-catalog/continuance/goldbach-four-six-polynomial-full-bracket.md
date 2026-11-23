# A four- and six-prime charge on the original Goldbach center

For each sufficiently large power of two the odd Möbius-parity part of the original even-endpoint center with at least four prime factors and least factor at least \(N^{19/120}\) has doubled absolute charge below \(0.045N\). The estimate keeps each endpoint's full admitted divisor bracket. It augments the fixed-target budget on a disjoint slice from the semiprimes. The original Vaughan and Selberg expansion stays fixed, and the count uses an auxiliary upper sieve. [Pinned exact center and cutoff](https://github.com/Sodelin/Research-Commons/commit/5ea16bc7f76f066d04b5077764ec67c57cf715ab) · [Pinned powers-of-two margin and remaining rows](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0)

## Exact support and full-bracket size

Write \(N=2^k,\ H=\sqrt N,\ L=\log N,\ P=N^{21/40}\), and \(\sigma=19/120\). Keep the actual central square \((H/2,H]^2\), \(m=qh\) squarefree and \((m,N)=1\), and \(n=N-m\) squarefree. Keep its full strict divisor condition \(d>P\). The support in the assertion also requires \(\mu(m)=-1,\ \mu(n)=+1,\ \omega(n)\ge4,\ P^-(n)\ge N^\sigma\). The estimate allows any further original masks common to both \(q,h\) orientations and all admitted \(d\) at that endpoint. The original roughness \(P^-(n)>Z_1\) is automatic here for sufficiently large \(N\).

Pair the two orientations with \(q<h\). The signed full-bracket weight is \(\mu(h)\log(h/q)B(n)\), where
\[
 X=n/P,\qquad B(n)=\sum_{\ell\mid n,\,\ell<X}-\mu(\ell)\log\ell .
\]
This uses squarefreeness and \(\mu(n)=+1\). The external factor of two from the original endpoint-parity transfer remains in the charge. Eight primes above \(N^\sigma\) would have product greater than \(N\), so the two possible counts are \(4\) and \(6\). The strict cutoff \(X<N^{19/40}=N^{3\sigma}\) rules out triples and higher divisors for both counts.

For four primes, retain the graph whose vertices are the primes below \(X\) and whose edges are the admitted pairs \(p_i p_j<X\). No two edges are disjoint, since otherwise \(n<X^2<n\), using \(P>\sqrt n\). A finite simple graph with no two disjoint edges has its edges in a star or a triangle. If it has a star of at least two edges, its center is the least prime of \(n\): whenever \(p_i p_j<X\), replacing an endpoint by a smaller distinct prime also gives an edge. On a star with \(r\) leaves, the bracket is the sum of the logarithms of isolated vertices minus \((r-1)\) times the log of the center. For \(r\ge2\) that center has \(\log p_1\le(\log n)/4\), so the negative term has magnitude at most \((\log n)/2\). A single edge contributes zero from its two vertices. For a triangle the bracket is minus the sum of its three logs plus any isolated-vertex log. With no edges the bracket is just the sum of vertex logs. Thus in all four-prime cases \(|B(n)|\le\log n\le L\).

For six primes every pair divisor is admitted because its complementary four factors have product at least \(N^{4\sigma}>P\). The same holds for singletons. The graph is complete on the six vertices. Since each prime appears in five pair divisors, the full bracket is exactly \(-4\log n\). This gives \(|B(n)|\le4L\) here. These are estimates for each full bracket on the original strict support.

## Count once using the smallest primes as the modulus

In the four-prime case fix the two least primes as a product \(M=p_1p_2\). In the six-prime case fix the three least as \(M=p_1p_2p_3\). Each endpoint supplies a unique sorted tuple. In both cases \(M\le\sqrt n\le H\), and \(M\) is odd. The pairs \(q,h\) obey the unit hyperbola \(qh=N\bmod M\), and the remaining factor \(b=(N-qh)/M\) is free of primes below \(N^\sigma\).

Take an auxiliary upper Selberg square for this roughness, with level
\[
 D_M=\min\{N^{997/3000}/\sqrt M,\ N^{\sigma-1/1000}\}.
\]
The square is one on the original rough \(b\). Its indices use odd primes other than those dividing \(M\). For each such prime \(r\) the forbidden density from \(qh=N\bmod r\) is \(g(r)=(r-1)/r^2\). Thus the optimal reciprocal main value is \((2\Pi+o(1))/\log D_M\), where \(\Pi=\prod_{r>2}(1+1/[r(r-1)])\). The one-dimensional Euler product and logarithmic convolution in the pinned direct semiprime proof apply uniformly since \(\log D_M\gg L\). No prime divisor of \(M\) is at most \(D_M\) here, and the omission of 2 stays explicit. [Pinned direct sieve and its main coefficient](https://github.com/Sodelin/Research-Commons/commit/36624845444790787f442157309e7f9ba6644ad0)

Open the square with \(c=[a_1,a_2]\), and count directly at the odd composite modulus \(Mc\). Keeping \(q,h\) odd gives one fourth of the area main term. The continuous weight \((\log(h/q))_+\) on the square has normalized integral \(J=3/8-(\log 2)/2\). It can be bounded above on a finite mesh of log-power complexity with integrated weight \(J+o(1)\). Unit-hyperbola rectangular completion gives \(N^{o(1)}((Mc)^{1/2}+H/(Mc)^{1/2})\) error per sieve pair. The coefficient magnitudes are at most one, and
\(\sum_{a_1,a_2\le D_M} [a_1,a_2]^{1/2}\ll D_M^3\), while the reciprocal half-power sum is \(O(D_M)\) by writing \(a_1=gu,a_2=gv\) with \((u,v)=1\). Thus the summed error at \(M\), including log weights, is at most
\[
 N^{o(1)}\big(M^{1/2}D_M^3+HM^{-1/2}D_M\big)
 \le N^{o(1)}\big(N^{1-3/1000}+N^{5/6-1/1000}\big)/M .
\]
Summing over the two- or three-prime modulus choices costs only a fixed power of \(\log\log N\) in reciprocal mass. All errors are \(o(N)\). The sieve enlarges only the nonnegative upper count after evaluating the full bracket and pairing. [Pinned composite-modulus completion](https://github.com/Sodelin/Research-Commons/commit/909738e51f1ea4abe94c119276375481f85abc56)

## The cap on the same target

Use \(\varphi(M)/M^2\le 1/M\). When \(M=\prod p_i\), set \(x_i=(\log p_i)/L\) and \(c(w)=\min(997/3000-w/2,\sigma-1/1000)\). The count, the bracket log bound, and the doubled prefactor give coefficient \(J\Pi\int (\prod dx_i/x_i)/c(\sum x_i)\) for the four-prime case and four times that for the six-prime case. The prime harmonic limit follows from Mertens by a fixed mesh in these compact exponent ranges. Restrict the domains to the necessary constraints
\[
 \begin{aligned}
 \mathcal D_4&:\ \sigma\le x\le y,\quad x+3y\le1,\\
 \mathcal D_6&:\ \sigma\le x\le y\le z,\quad x+y+4z\le1 .
 \end{aligned}
\]
In both domains \(\sum x_i\le1/2\), so \(c(\sum x_i)\ge247/3000\).

For \(\mathcal D_6\), put \(x=\sigma+a,\ y=x+b,\ z=y+c_1\). The nonnegative variables satisfy \(6a+5b+4c_1\le1/20\), which gives volume \(1/(8000\cdot720)\). Using \(J<57/2000\), \(\Pi<34/25\) and \(x,y,z\ge\sigma\), the doubled coefficient is at most \(918/11145875\).

For \(\mathcal D_4\) the following rational upper grid verifies the other coefficient. It keeps every rectangle that can meet the domain, and uses the upper integrand from the lower coordinates and the upper sum of coordinates.

    from fractions import Fraction as F
    sig, A = F(19,120), F(997,3000)
    K, scale = 64, 10**12
    dx = (F(1,4)-sig)/K
    dy = ((1-sig)/3-sig)/K
    total = 0
    for i in range(K):
        low_x = sig+i*dx
        for j in range(K):
            low_y = sig+j*dy
            if low_x > low_y+dy or low_x+3*low_y > 1:
                continue
            c_lo = min(sig-F(1,1000),
                       A-(low_x+dx+low_y+dy)/2)
            t = scale*dx*dy/(low_x*low_y*c_lo)
            total += (t.numerator+t.denominator-1)//t.denominator
    jp = F(57,2000)*F(34,25)
    four = jp*F(total,scale)
    six = 4*jp*F(1,8000*720)/(sig**3*(A-F(1,4)))
    assert total == 1154346605362
    assert four+six < F(9,200)

The combined upper coefficient is below \(0.044825\), with strict slack below \(0.045\). This proves the asserted pointwise charge, and it is disjoint from the semiprime charge. Spending both charges from the certified \(0.330N\) model margin leaves \(0.187N\) for the other signed rows. These include the less rough part of the four-or-more-prime center and the \(\mu(qh)=+1\) center. The hand proof and exact rational constants are separate from these unresolved lower bounds and from Lean verification.
