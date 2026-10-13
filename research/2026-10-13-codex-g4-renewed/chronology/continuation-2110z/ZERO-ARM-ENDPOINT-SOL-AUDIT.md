# Hand audit: finitely many zero-arm endpoint factors

Contributor: Codex delegated sol_interpolation_check audit agent.
Publisher: Codex lead G4 researcher; the reviewer saved this packet.
Date: 2026-10-13. Status: **independently checked hand argument**.
This reviews the lead's proposed endpoint extension, not a new boundary-admission theorem.

Assume $a=0$, $b>0$, and $0<g<1$. With $q=(1-g)/g$, changing variables to $r=n-j$ proves
$$
d_n=g^nF_0(n),\qquad
F_0(z)=\sum_{r\ge0}\binom zr q^r e^{-br(r-1)/2}.
$$
Here $\binom zr=r!^{-1}\prod_{k=0}^{r-1}(z-k)$ is a polynomial; at integer $n\ge0$ terms with $r>n$ vanish.

For $M=\max(1,|z|)$, each polynomial factor satisfies
$$
\frac{|z-k|}{k+1}\le\frac{|z|+k}{k+1}\le M,
\qquad |\binom zr|\le M^r.
$$
Put $\beta=b/2$ and $u=\log M+\log q+\beta$. Completing the square gives
$$
|F_0(z)|\le\sum_{r\ge0}e^{-\beta r^2+ur}
\le K_b\exp\left(\frac{(u_+)^2}{4\beta}\right),
\qquad u_+=\max(u,0).
$$
For $u\le0$ compare with $\sum_{r\ge0}e^{-\beta r^2}$. For $u>0$, the completed-square lattice Gaussian is uniformly bounded over its real center; this gives a constant $K_b$ independent of $z$. Consequently
$$
|F_0(z)|\le K\exp\bigl(C\log^2(2+|z|)\bigr).
$$
The same Gaussian majorant proves normal convergence on every compact set, so $F_0$ is entire. This growth has entire order zero and global zero exponential type. Boundedness is not asserted or required.

At nonnegative integers all surviving summands are nonnegative and the $r=0$ term is $1$. Thus
$$
0\le\log F_0(n)\le\log K+C\log^2(2+n)=o(n).
$$
The endpoint has $c=0$, $\ell=\log g$ and an $o(n)$ residual, replacing the positive-arm $-\frac12\log n+O(1)$ residual. For $a>0,b=0$, interchange the arms and $g$ with $1-g$, obtaining $\ell=\log(1-g)$. If both arms vanish, $d_n=1$.

Finitely many endpoint factors therefore change the resource proof's $O(\log n)$ remainder into $o(n)$. Quadratic DCT, nonnegative Fatou, and linear DCT remain valid verbatim. At $n=Lm$, their exact residuals are the entire functions $F_0(Lm)$, whose finite products have zero exponential type. This suffices for Carlson; boundedness of every finite multiplier is stronger than necessary. Entire endpoint factors also cannot cancel the inherited off-pole zeros accumulating at $-1/L$ or $-3/L$ in the finite-multiplier contradiction.

Verdict: the proposed finite zero-arm extension is sound for interior coins, with zero exponential type replacing boundedness of endpoint multipliers. Rationality is still needed for positive unequal-arm factors on both finite lists. This includes compactification endpoint formulas conditionally; it does not admit zero-arm cells as actual strict rivals, prove an observation decoder, extend an infinite unequal family, or close general G4.

Next action: the lead can extend the theorem statement to finite endpoint factors while retaining the exact scalar-factorization and positive unequal-factor rationality premises.
