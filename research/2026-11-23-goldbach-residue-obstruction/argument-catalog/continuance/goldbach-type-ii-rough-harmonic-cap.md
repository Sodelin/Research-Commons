# A smaller explicit rough Type II charge from the factor-product constraint

**Unconditional hand refinement at each sufficiently large power of two.** Keep the original fixed-Selberg Type II expansion, original count and mark projectors, all the prime and strict divisor cutoffs, and the positive stress interval \(L/20\le\log(u/v)\le L/10\), \(L=\log N\). The fixed groups, their Möbius signs, both expanded endpoint parities, and the external factor of two in the Goldbach budget all remain those of the pinned edge proof. Write \(p=P^-(d/w)\) for its group-level least prime, \(J=3/8-(\log2)/2\), and \(\Pi=\prod_{r>2,\ r\ {\rm prime}}(1+1/(r(r-1)))\). For \(\min(\kappa,\delta)\le\alpha\le1/40\), the doubled grouped negative weight on \(p>N^\alpha\) is bounded by \(N\bigl(C(\alpha)+o(1)\bigr)\), where
\[
\begin{split}
C(\alpha)&=J\Pi\left[
\frac4{245}\left(\frac{17}{40}I_0(\alpha)+2I_1(\alpha)\right)
+\frac{53}{784}\right],\\
I_0(\alpha)&=\frac1\alpha-\frac{136}{5},\qquad
I_1(\alpha)=\log\frac1{40\alpha}+\frac15+\frac45\log\frac{32}{25}.
\end{split}
\tag{1}
\]
In particular the doubled charge above \(N^{1/100}\) is at most \(N/40\), improving the pinned \(N/25\) bound. Above \(N^{1/200}\) it is at most \(N/19\) when the fixed square permits that \(\alpha\). The direct cap above \(N^{1/25}\) by itself is at most \(N/380\). [Pinned exact signed edges and polynomial cap](https://github.com/Sodelin/Research-Commons/blob/56abc20768f148741e0fb57b8c4fe82ec0ebb4a8/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-least-prime-edges-2246z.md) · [Pinned direct cap](https://github.com/Sodelin/Research-Commons/blob/b8d0afa3e5fab3380f662ce172eacad56ea05316/research/2026-11-23-goldbach-residue-obstruction/argument-catalog/continuance/2026-11-23-codex-type-ii-rough-negative-cap-2234z.md).

## The harmonic mass of a rough factor

For \(u\ge0\) define
\[
 \mathcal H(u)=1+\sum_{j\ge1}\frac1{j!}
      \int_{\substack{x_i\ge1\\x_1+\cdots+x_j\le u}}
      \frac{dx_1\cdots dx_j}{x_1\cdots x_j}.
\]
The sum is finite at fixed \(u\). For fixed \(c>0\), uniformly for \(t\) in the pinned positive compact exponent interval,
\[
 \sum_{\substack{b\le N^c\\ b\ {\rm squarefree},\ P^-(b)>N^t}}\frac1b
       =\mathcal H(c/t)+o(1).
 \tag{2}
\]
In fact, an ordered \(j\)-tuple of distinct primes gives the \(j!\) representations of its product. The exponent variable \(\log p/L\), with prime weight \(1/p\), has limiting measure \(dx/x\) on every fixed positive compact interval by Mertens. In the product measures the restrictions on \(\sum \log p/L\) and the lower bound \(t\) have hyperplane boundaries of measure zero. A fixed mesh sandwiches the polytopes uniformly in \(t\), and its boundary strips have uniformly vanishing measure as the mesh shrinks. There are only boundedly many \(j\), and repeated primes have harmonic weight \(o(1)\) by \(\sum_{p>N^{\inf t}}p^{-2}=o(1)\). Scaling each exponent by \(t\) yields (2).

For \(u>1\), symmetry on the boundary \(\sum x_i=u\) gives
\[
 \mathcal H'(u)=\frac{\mathcal H(u-1)}u .
\]
Indeed, after differentiating the \(j\)-factor integral, multiply the integrand by \(u=\sum x_i\), cancel one reciprocal factor in each of the \(j\) summands, and project to the remaining \(j-1\) coordinates with sum at most \(u-1\). The derivative identity holds almost everywhere and the function is locally absolutely continuous. On \(1\le u\le2\), \(\mathcal H(u)=1+\log u\le(4/7)(u+1)\), by the tangent of \(\log u\) at \(u=7/4\) and \(\log(7/4)<4/7\). For example the atanh series at \(3/11\) gives \(\log(7/4)\le345/616<4/7\). The differential identity propagates the inequality in steps of length one: if it holds for \(u-1\ge1\), then the derivative is at most \(4/7\). Thus
\[
 \mathcal H(u)\le \frac47(u+1)\qquad(u\ge1).
 \tag{3}
\]

## The same two edge counts with the improved harmonic bound

Use \(t=(\log p)/L\), \(e(t)=\min(t,1/40)\) and \(d(t)=\min(t,1/32)\) as in the pinned edge calculation. For \(N^\alpha<p\le N^{1/25}\), its two exact surviving edges use \(b\le N^{c_+}\) and \(b\le N^{c_-}\), with \(c_+=1/5\), \(c_-=9/40\). Here \(b\) is already squarefree and all of its primes exceed \(p\), since \(p\) is the actual least prime in the original group. Replace its two reciprocal bounds \(c_\pm/t+o(1)\) by \((4/7)(c_\pm/t+1)+o(1)\) from (2)–(3). All other counts, positive majorants, congruences and completion errors are exactly those of the pinned proof. Its main bound, keeping both edge contributions and the factor two, becomes
\[
 J\Pi\,\frac87\,\frac1{40}\,\frac47
 \int_\alpha^{1/25}\frac{e(t)}{t^2d(t)}
       \left(\frac{17}{40}+2t\right)dt .
\]
The integral of \(e/(t^2d)\) is \(I_0\) by the pinned calculation. The integral of \(e/(td)\) is \(I_1\), by splitting at \(1/40\) and \(1/32\).

For the separate direct cap \(p>N^{1/25}\), its \(s\)-factor has \(s\le N^{9/40}\) and is squarefree and free of primes at most \(N^{1/25}\). Thus replace the old reciprocal bound \(45/8+o(1)\) by \((4/7)(45/8+1)+o(1)\). The old constant \((45/448)J\Pi\) is multiplied by \(212/315\), giving \((53/784)J\Pi\). This proves (1) with the pinned error exponents unchanged. The calculation upper bounds a negative charge and does not change the underlying expansion or move any term between parities.

## Numerical check of the rational enclosures

Use \(J<57/2000\), from \(\log2>.693\) by the first three terms of its atanh series, and \(\Pi<34/25\), from \(\Pi\le e/2\). At \(\alpha=1/100\), \(I_1<178/125\) follows from \(\log(5/2)<1\) and \(\log(32/25)<7/25\). At \(\alpha=1/200\) the same argument with \(\log5<17/10\) gives \(I_1<531/250\). The resulting rational upper enclosures of (1) are \(42003243/1750000000<1/40\) and \(634335501/12250000000<1/19\), respectively. For the direct cap alone the enclosure is \(51357/19600000<1/380\). These inequalities were checked with exact rational arithmetic. The separate smaller-prime ranges and the other signed Goldbach rows require their own bounds.
