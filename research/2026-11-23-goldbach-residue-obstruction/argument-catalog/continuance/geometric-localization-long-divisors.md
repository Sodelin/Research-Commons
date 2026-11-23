# Geometric localization of the rough long-divisor sum

These are pointwise hand estimates. Keep \(L=\log N,\ H=\sqrt N\), the original block \(q,h\in(H/2,H]\), strict cofactor cutoff, squarefree \(m=qh\), \((m,N)=1\), the original middle-count mask, and \(d>D,\ n=d\ell=N-m>0\) with \(n\) \(Y\)-rough. Here \(\log Y\asymp L^{\delta/2}\), as in the original project. The exact weight is \(-\mu(h)\mu(d)\log h\log\ell\).

## Local counting bound

Fix \(s=\min(d,\ell)\le H\), with at most two orientations, and omit \(s=1\), which contributes zero on the original support. Fix any axis-parallel \(q,h\) box inside the block of real area \(A\). The number of placements in the box with \(qh=N\bmod s\) and \((N-qh)/s\) \(Y\)-rough is
\[
\ll \frac{A\varphi(s)}{s^2\log Y} + s^{1/2+o(1)}(1+H/s)N^{o(1)}.
\]
Indeed \(s\) is \(Y\)-rough and coprime to \(N\). For each \(p\le Y\), the local bad event is \(qh=N\bmod p\). Its density in the CRT model is \((p-1)/p^2\) if \(p\nmid N\), or \((2p-1)/p^2\) otherwise. The survival product is \(O(1/\log Y)\), uniformly in \(N\). Truncate upper Bonferroni at a sufficiently large even \(O(\log L)\). The local tail is smaller than every fixed negative power of \(L\) by enlarging that constant. Each retained modulus \(e\) has \(e^2=N^{o(1)}\) residue boxes. In each such box the congruence modulo \(s\) reduces to a unit modular hyperbola. Splitting complete periods and a partial period gives the stated error by the rectangular Kloosterman estimate; the mixed complete/partial terms use the unit-count error \(O(\tau(s))\). The moduli and all induced boxes cost \(N^{o(1)}\) in the error. This argument is uniform in the location and lengths of the original rectangle. Summing over \(s\le H\) and over any polylogarithmic number of boxes per \(s\) costs \(N^{3/4+o(1)}\), also after restoring logarithmic weights. [Fixed rectangle, Shparlinski equation (10)](https://arxiv.org/pdf/1103.2879) · [Estermann](https://doi.org/10.1112/S0025579300002187).

For \(B\ge Y/2\), the number of rough \(s\) in \(B<s\le2B\) is \(O(B/\log Y)\), by the upper sieve up to \(\min(Y,B^c)\) for a fixed sufficiently small \(c>0\). Thus \(\sum_{B<s\le2B,\ s\ {\rm rough}}\varphi(s)/s^2\ll1/\log Y\). The contribution from all shells to this harmonic sum is \(O(L/\log Y)\). [Upper sieve, p. 50](https://pub.math.leidenuniv.nl/~evertsejh/Fundamental%20Lemma.pdf).

## Simultaneous block-factor ribbon and endpoint corner

Fix \(a,b\ge0\) and impose \(n\le NL^{-a}\) and \(|q-h|\le HL^{-b}\). Put \(u=\max(a,b)\). On this sector, the total absolute weight is
\[
O(N L^{3-\delta-a-u})+N^{3/4+o(1)}.
\]
On \(\mu(m)=-1\), the absolute value of the signed contribution is
\[
O(N L^{2-\delta-a-2u})+N^{3/4+o(1)}.
\]
To see the area factor, \(N-qh\ge H(H-q)\) and likewise for \(h\). Both coordinates therefore lie within \(U=HL^{-a}\) of \(H\), intersecting the original block. If the ribbon width \(\Delta=HL^{-b}\) is smaller than \(U\), partition the \(q\)-interval into pieces of length at most \(\Delta\). The corresponding \(h\)-ranges lie in intervals of length at most \(3\Delta\). Otherwise use the single square. The total area is \(O(U\min(U,\Delta))=O(NL^{-a-u})\), with \(O(1+U/\Delta)\) boxes. The full harmonic sum and the \(L^2\) weight cap give the first bound. On odd \(m\), \(q,h\) reflection replaces \(\log h\) by \(\tfrac12\log(h/q)\), of magnitude \(O(L^{-u})\), yielding the second. Thus at \(\delta=.01\), the odd sector with just the corner condition has \(o(N)\) for \(a>1.99/3\). With just the ribbon condition it has \(o(N)\) for \(b>.995\).

## Near-equal endpoint divisors

Fix \(0<\lambda\le1\) with \(\lambda\ge L^{-C}\) for some fixed \(C\), and retain \(1\le\max(d,\ell)/\min(d,\ell)\le1+\lambda\). The total absolute weight over all parities is
\[
O(N\lambda L^{2-\delta})+N^{3/4+o(1)}.
\]
On \(\mu(n)=-1\), allow both \(m\)-parities. The absolute value of the signed contribution is
\[
O(N\lambda^2 L^{1-\delta})+N^{3/4+o(1)}.
\]
Indeed for fixed \(s=\min(d,\ell)\) we have \(s^2\le n\le(1+\lambda)s^2\). Both \(q,h\) are within \(2s^2/H\) of \(H\). Split the \(q\) range into intervals of length at most \(v=\lambda s^2/H\). On each, the required \(h\) lies between \((N-(1+\lambda)s^2)/q\) and \((N-s^2)/q\), and its full range has length \(O(v)\) by the width and the bounded slope on \(q\ge H/2\). The \(O(1/\lambda)\) boxes have area \(O(\lambda s^4/N)\). Summing the local counting bound over rough \(s\) gives \(O(N\lambda/(\log Y)^2)+N^{3/4+o(1)}\) placements: indeed \(\sum_{s\le H,\ s\ {\rm rough}}s^3\ll H^4/\log Y\) by dyadic summation. Restore \(L^2\) for the absolute bound.

For the second bound restrict to \(s>D\) so both orientations are legal. Then squarefree odd \(n\) gives \(\mu(d)=-\mu(\ell)\), and reflection \(d,\ell\) replaces \(\log\ell\) by \(\tfrac12\log(\ell/d)\) in the signed weight, of magnitude \(O(\lambda)\). The omitted sector \(s\le D\) has \(n\le2D^2=N^{o(1)}\) and absolute cost \(N^{o(1)}\) by the divisor bound, since at each \(n\) there are at most \(\tau(n)\tau(N-n)\) placements. At \(\delta=.01\) and \(\lambda=L^{-b}\), the signed odd-\(n\) estimate is \(o(N)\) for \(b>.495\) even if \(\mu(m)=+1\). If both \(m,n\) have odd Möbius parity, both reflections apply and the bound improves by one more factor of \(L\).

These estimates leave broad regions of separation between both pairs of factors. The proof takes upper bounds on exact-support pieces rather than averaging over \(N\).

The proof uses only fixed rectangles. An arbitrary moving interval version of the hyperbola bound would fail: for prime modulus, assigning each admissible first coordinate a singleton containing its inverse gives almost a full period of points despite a constant area main term.


## Combined localization

Impose all three conditions \(|q-h|\le\eta H,\ n\le\xi N\), and \(\max(d,\ell)\le(1+\lambda)\min(d,\ell)\), with the widths bounded below by fixed inverse powers of \(L\) and at most one. For fixed \(s=\min(d,\ell)\), put \(U=s^2/H\) and \(\Delta=\eta H\). The identity \(q^2-(N-s^2)=q(q-h)+(qh-(N-s^2))\) restricts \(q\) to a range of length \(O(\min(U,\Delta+\lambda U))\). The allowed interval in \(h\) has length \(O(\min(\Delta,\lambda U))\). Partition the \(q\)-range at that latter scale. The endpoints of the allowed \(h\)-intervals vary by at most a constant times the mesh over each piece. The total box area is \(O(\lambda U\min(U,\Delta))\). Summing the local bound to \(s\le H\sqrt{\xi}\) yields
\[
O\!\left(\frac{N\lambda\min(\xi^2,\eta\xi)}{(\log Y)^2}\right)+N^{3/4+o(1)}
\]
placements. Multiply the main term by \(L^2\) for the absolute estimate, \(L\min(\eta,\xi)\) for signed odd \(m\), \(L\lambda\) for signed odd \(n\), or \(\lambda\min(\eta,\xi)\) if both are odd. The errors absorb these logarithmic weights.
