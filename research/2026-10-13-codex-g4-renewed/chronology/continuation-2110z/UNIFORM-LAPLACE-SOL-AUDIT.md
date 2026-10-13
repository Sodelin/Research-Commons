# Independent audit: uniform inverse-Laplace phase removal

Proposal: Codex lead G4 researcher.
Proof recovery and draft: Codex delegated laplace_recovery researcher.
Independent audit: Codex delegated sol_interpolation_check agent.
Publisher: Codex lead G4 researcher; the reviewer saved this packet.
Date: 2026-10-13. Status: **independent hand acceptance; no defect located**.
No numerical experiment, formal verification, historical novelty claim, or general G4 closure is asserted.

## Exact reviewed body and dependencies

I read the complete [UNIFORM-LAPLACE-PHASE-REMOVAL.md](UNIFORM-LAPLACE-PHASE-REMOVAL.md), SHA256
14dc61fa433ed9ecb5307b93fbdf40dabc870f39a2324263a4c57cfa7cfe9fc8,
and independently derived the kernel, convolution majorant, contour bound, and endpoint extension.

The inherited providers retain their separate reviews. Their current hashes are:

| Provider | SHA256 |
|---|---|
| [Fixed-phase construction](FIXED-PHASE-GAMMA-HANDOFF.md) | 7a36080709a2e1e65c3f2bac91c93cdf0b531a349c6d81ee82cd8005a8c00fe7 |
| [All-order constraint](ALL-ORDER-UNEQUAL-PHASE-CONSTRAINT.md) | 0f08cb7d8b1a6e8ef8d4b9b50281f097ff7573a576cd2866bfac038982ad00db |
| [Resource normalization](UNEQUAL-RESOURCE-NORMALIZATION.md) | 1f6f5edd6904d999d30d73581908f3f6e18b245871fc0c4c7a9fae6cc304deb5 |
| [Carlson bridge](../continuation-1837z/CARLSON-CONTINUATION-BRIDGE.md) | 9411158e6523c33243c4c0a894441bf0b695af13648c55a13f413f6d7022a2a7 |
| [Off-pole finite persistence](../continuation-1837z/MEROMORPHIC-FINITE-PERSISTENCE.md) | 2a02c32ee1961f2391d1e380baa73349fb6d225dae8bd2442ec676db2138bf2f |

This audit checks the new analytic bridge and its composition; it does not claim a fresh independent reproof of every inherited supplier.

## Kernel and uniform shift bound

The logarithmic inverse formula has the correct normalization
$\nu_u=(2\pi\alpha\beta)^{-1/2}(\beta/\alpha)^u$.
Differentiating twice and using the trigamma integral gives exactly
$$
\left(\log[W_u(z)z^{1/2}/\nu_u]\right)''
=\int_0^\infty v^2e^{-zv}K_u(v)\,dv.
$$
Both the logarithmic expression and the Laplace integral tend to zero on the sufficiently large positive axis, so their affine difference vanishes. This establishes the identity initially on a half-plane depending on $u$; no uniform-in-$u$ logarithmic branch is presumed.

Cancellation at $v=0$ gives the claimed removable value
$$
K_u(0)=\frac{1-1/(\alpha\beta)}{12}
-\frac{u^2+(1-2\alpha)u}{2\alpha\beta}.
$$
For the compact-sector bound, one can also Taylor-expand in $u$:
$$
\left.\partial_u K_u(v)\right|_{u=0}=
\frac1{\alpha(e^{v/\alpha}-1)}
-\frac1{\beta(e^{v/\beta}-1)},
$$
whose singularity at zero cancels, and
$$
\partial_u^2K_u(v)=
-\frac{v e^{-uv/\alpha}}{\alpha^2(e^{v/\alpha}-1)}
-\frac{v e^{uv/\beta}}{\beta^2(e^{v/\beta}-1)}.
$$
On a fixed truncated sector and a common small disk, the latter is bounded by $C_Re^{c_R|u||v|}$. Hence
$|K_u(v)|\le C_R(1+u^2)e^{c_R|u||v|}$,
with no shift-dependent neighborhood.

Volterra convolution divides the $r$th power majorant by $\Gamma(r+1/2)$. The additional $r!$ in the exponential series makes its scalar sum exactly
$$
\sum_{r\ge0}\frac{x^r}{r!\Gamma(r+1/2)}
=\frac{\cosh(2\sqrt{x})}{\sqrt\pi}.
$$
Thus the compact growth is $e^{C_R|u|}$, rather than $e^{C_Ru^2}$.
The Gaussian lattice weights dominate it for every fixed positive $t$.
The integrated inverse $J_u$ is $v^{1/2}$ times an analytic germ on a common disk. Its leading term $\nu_u v^{1/2}/\Gamma(3/2)$ agrees with $W_u/z\sim\nu_u z^{-3/2}$.

## Common contour and global summation

For each fixed $u$, the initially constructed $J_u$ has exponential order and Laplace transform $W_u/z$ sufficiently far to the right. The inherited fixed-phase bound strengthens to
$$
|W_{s-\theta}(z)|\le CM^{|s|}(1+|z|)^{-1/2}
$$
on the entire closed right half-plane, uniformly in centered real phase. Therefore $W_u/z$ is absolutely integrable on every line $\Re z=c>0$.

Shifting the original Bromwich line is legitimate separately for each $u$: there are no poles in the intervening right-half-plane strip, and its horizontal integrals vanish as $O_u(T^{-3/2})$ with fixed width. Only after these individual shifts is the common-line bound applied. It gives
$$
|J_{s-\theta}(v)|\le C_cM^{|s|}e^{cv}.
$$
This estimate proves Gaussian-summed global exponential order. The distinct compact-sector estimate proves analytic summability and the common fractional germ. Together they justify the exact transform
$\mathcal L J_\theta=F(\,\cdot\,,\theta)/z$ on $\Re z>0$.

The distinction between these two bounds is essential and is correctly maintained in the written proof. Summing only the crude per-shift exponential-order bounds would not justify the global transform.

## Exactness from the analytic endpoint germ

For $K=k_T+k_R>0$, the finite convolution has the form
$v^{3K/2-1}G(v)$ with $G$ analytic near zero, and it is holomorphic on a common sector about the positive axis. Its global exponential order follows from the common-line bounds. The case $K=0$ is separately trivial.

The cross-difference's transform is the flat numerator divided by $z^K$.
Watson's elementary integral expansion identifies each Taylor coefficient of $G$ with a nonzero Gamma multiple of an inverse power of $z$. Flatness therefore makes every coefficient zero. Analyticity first gives zero on an interval adjacent to zero, and sector continuation gives zero everywhere on the positive axis. The transform then vanishes exactly. This proves the stated phase cross-identity.

This is a class-specific uniqueness argument. The earlier counterexample $e^{-z}$ is consistent: its inverse is supported at a positive delay and does not have the analytic continuation property proved here. No unverified uniform Fox H-function theorem is invoked.

## Finite endpoint multipliers

The weighted coefficient induction is also valid. With the notation of Section 7, each analytic zero-type expression (27) is real on the positive axis. At integer $m$ its sign is that of
$A_j(\theta_m)-c+O(1/m)$, because $E_T(2m)>0$.
Even if $E_T(2m)$ grows, that positive factor preserves the sign; no bound on its reciprocal or absolute approximation error is needed.

Nonconstant continuous coefficients on the cyclic orbit closure give syndetic returns to opposite strict signs and hence positive-density real zeros. The inherited Carleman lemma contradicts this. Thus all strict-ratio coefficients are constant, while endpoint factors remain unexpanded. The density argument applies only to the strict Gamma–Gaussian factors.

After their exact phase cross-identity, the actual scalar identity gives equation (28) by cancellation of the positive physical $B$ product at integers. Finite endpoint functions have zero exponential type, so they preserve the Carlson hypotheses. They are entire and cannot cancel the inherited off-pole zeros accumulating at a finite pole of the equal-arm family. The finite right-side meromorphic function has value one at zero and yields the stated contradiction.

## Accepted implication and remaining scope

The pinned proof establishes exact phase removal for finite strict Gamma–Gaussian products under its all-order phase premise. Combined with the inherited resource, recurrence, Carlson and off-pole results, it establishes finite persistence for an exact scalar factorization with finitely many arbitrary real-balance positive-arm factors and finitely many auxiliary zero-arm factors, against a summable countable strict equal-arm family.

It does not supply that scalar factorization from arbitrary legal original-source observations, admit boundary parameters as physical rivals, settle INDEPENDENT-only local exclusion, classify arbitrary infinite unequal-arm families, or close general G4.

Next action: use this accepted analytic component only after verifying the exact scalar factorization and all source/compactification premises in the intended application.
