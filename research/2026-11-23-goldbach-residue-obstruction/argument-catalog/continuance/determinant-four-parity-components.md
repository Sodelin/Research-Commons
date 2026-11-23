# The four parity components of the determinant estimate

This hand corollary retains the original fixed target, square-root block, exact middle mask, \(Y\)-rough endpoint and cutoff \(d>D\). Put \(H=\sqrt N\), \(L=\log N\), and \(P=H^a\) for any fixed \(1\le a<23/22\). Write \(m=qh,\ n=d\ell=N-m\), and \(w=-\mu(h)\mu(d)\log h\log\ell\). Restrict to squarefree \(m,n\) and \((m,N)=1\). The standard rough exceptional-set trims justify the last two restrictions at arbitrary logarithmic savings on the original support. All estimates below are \(O_A(N/L^A)\) for any fixed \(A\). They hold uniformly with additional independent interval restrictions on the four variables, including \(N\)-dependent endpoints. [Pinned parity transfer and cutoff optimization](https://github.com/Sodelin/Research-Commons/blob/2de6bf8b2fd7dd70e07bcd6c5865dec7b5eb5140/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-parity-transfer.md).

Let \(S_{\epsilon,\eta}\) denote the signed sum of \(w\) in a fixed such box on \(\mu(m)=\epsilon,\ \mu(n)=\eta\), where \(\epsilon,\eta\in\{+1,-1\}\). Then:
- On \(d\le P\), both row sums \(S_{\epsilon,+}+S_{\epsilon,-}\) are negligible.
- On \(\ell\le P\), both row differences \(S_{\epsilon,+}-S_{\epsilon,-}\) are negligible.
- On \(d,\ell\le P\), every cell \(S_{\epsilon,\eta}\) is negligible. On the remaining \(d>P\) range the two columns agree in each individual \(m\)-parity, since \(\ell\le N/d<P\). Those common values remain uncontrolled by the determinant transfer.

To prove this, consider the four sums \(U_{ij}=\sum \mu(m)^i\mu(n)^j w\) for \(i,j\in\{0,1\}\). For \(i=1\), squarefreeness gives \(\mu(m)\mu(h)=\mu(q)\). Swap \(q,h\) so the Möbius coefficient returns to the variable designated as \(h\). The square-root block, coprimality and product mask are preserved, and any additional independent \(q,h\) intervals are interchanged. The logarithm on the old \(h\) becomes a smooth log weight on the new \(q\). Multiplying the smooth test by it costs at most powers of \(L\) in normalized derivatives because \(q\in(H/2,H]\). Removing the old \(\log h\) from the arithmetic coefficient also preserves the masked Möbius prefix bound in the zero mode. A new sharp \(q\)-edge can be smoothed inside its actual interval at width \(H/L^J\), discarding \(O(N/L^J+H)\) candidate pairs per edge. The divisor-moment argument in the pinned proof absorbs that error.

For \(j=1\) the previously audited transfer interchanges \(d,\ell\) after \(\mu(n)\mu(d)=\mu(\ell)\), so the determinant cutoff is now on \(\ell\). The old \(d>D\) becomes an edge on the smooth variable and uses the pinned smooth-edge argument. If both swaps are present, the transformed logarithms lie on the smooth block variable and the signed endpoint variable, respectively; their costs are again only logarithmic. Both exceptional-set and zero-mode estimates apply after the swaps. Consequently \(U_{00}\) and \(U_{10}\) are negligible when \(d\le P\), and \(U_{01}\) and \(U_{11}\) are negligible when \(\ell\le P\).

Finally,
\[
 S_{\epsilon,+}+S_{\epsilon,-}=\tfrac12(U_{00}+\epsilon U_{10}),\qquad
 S_{\epsilon,+}-S_{\epsilon,-}=\tfrac12(U_{01}+\epsilon U_{11}).
\]
These are two independent row identities on their declared supports. They do not bound either row sum in the original large-\(d\) remainder. [Original signed determinant proof and masks](https://github.com/Sodelin/Research-Commons/blob/ec0d19f39f6024e75d4e4403b43bfe82e5c4b882/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/determinant-asymmetric-range.md).
