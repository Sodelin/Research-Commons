# Independent hand audit: arbitrary-balance fixed-phase interpolation

Contributor: Codex delegated sol_interpolation_check audit agent.
Publisher: Codex lead G4 researcher; the reviewer saved this packet.
Date: 2026-10-13. No numerical test or formal verification was performed.

Reviewed artifact: [FIXED-PHASE-GAMMA-HANDOFF.md](FIXED-PHASE-GAMMA-HANDOFF.md).
SHA256: 7a36080709a2e1e65c3f2bac91c93cdf0b531a349c6d81ee82cd8005a8c00fe7.

**Verdict: the fixed-phase interpolation, bounds, continuation and integer identity are sound. The phase-removal bridge remains explicitly conditional.**

## Half-plane bounds, including positive numerator shifts

A useful general inequality is: if $A,B>0$, $e>0$, $d$ is real with $|d|\le e$, and $\Re z\ge0$, then
$$
\left|\frac{Az+d}{Bz+e}\right|\le M,\qquad M=\max(A/B,1).
$$
Indeed the quadratic and constant terms of the squared moduli are bounded separately. If $d\le0$, the numerator cross term is nonpositive. If $d>0$, use $M^2B\ge A$ and $d\le e$ to bound that cross term by the denominator's. This verifies the case that the earlier rational formula did not need: a positive real numerator shift.

For $\theta\in[-1/2,1/2]$ and $k\ge0$,
$$
|\theta-k|\le k+1-\theta,\qquad
|-\theta-k|\le k+1+\theta.
$$
Both denominator constants are positive. The general inequality proves exactly the stated bounds $\max(\beta/\alpha,1)$ and $\max(\alpha/\beta,1)$ on the respective integer-shift factors, uniformly in real phase.

Uniform Gamma-ratio asymptotics on the closed right half-plane give
$$
R_0(z,\theta)=(\alpha z)^\theta(\beta z)^{-\theta}
(1+O(|z|^{-1}))
=(\alpha/\beta)^\theta(1+O(|z|^{-1})),
$$
uniformly for this compact real phase interval. The powers of $z$ cancel, including along imaginary boundary directions. The bounded portion is continuous with no numerator Gamma poles there. Likewise
$$
C_\alpha(z)\sim(2\pi\alpha\beta z)^{-1/2}.
$$
These are bounded on the closed half-plane. The Gaussian majorant times an exponential in $|s|$ proves normal convergence and boundedness uniformly in real phase. This result holds with phase fixed; it supplies no bound after substituting $\theta=\alpha z$.

## Global continuation and entire periodic phase dependence

For positive $s$, reflection of the second reciprocal Gamma supplies the quotient
$$
\frac{\Gamma(s-\beta z-\theta)}
{\Gamma(s+\alpha z-\theta+1)}
=s^{-z-1}(1+O(s^{-1})).
$$
Its sine prefactor is bounded on compact complex $(z,\theta)$ sets. The negative tail, with $s=-r$, gives
$$
\frac{\Gamma(r-\alpha z+\theta)}
{\Gamma(r+\beta z+\theta+1)},
$$
with the same power $r^{-z-1}$. Uniform ratio asymptotics and the Gaussian give normal convergence on every such compact set.

More precisely, after removing the common $\Gamma(z+1)$ prefactor, the series of reciprocal-Gamma terms is jointly entire in $(z,\theta)$. Therefore $F$ is holomorphic in both variables away from the possible simple poles $z=-1,-2,\ldots$, meromorphic in $z$ across those points, and entire in $\theta$ for each nonsingular $z$. Pole residues also depend entirely on phase. Reindexing $s$ proves $F(z,\theta+1)=F(z,\theta)$. Poles may cancel; none is asserted to be genuine.

## Integer identity and real-axis expansion

For any real representative $\theta\equiv\alpha n\pmod1$, the integer $j=\alpha n+s-\theta$ ranges over all integers as $s$ ranges over $\mathbb Z$. Reciprocal Gamma zeros remove exactly $j<0$ and $j>n$. Square completion then gives the stated exact diagonal identity. Choosing the fractional part in $[0,1)$ or the centered representative in $[-1/2,1/2]$ is equivalent by periodicity. In particular $F(0,0)=1$.

The local Gamma/Stirling expansion on the real axis does not require $z$ to be integer. In the central range the same expansion polynomials in $u=s-\theta$ apply; the established integer-shift bounds times the Gaussian make tails outside a growing central cutoff smaller than every inverse power. Thus the advertised transfer of the inherited fixed-phase saddle expansion to real $z\to+\infty$ is consistent. This audit does not independently reprove the separate all-order orbit-constraint theorem.

## Conditional all-orders-to-exact bridge

Accepting that inherited orbit constraint, expression (3) is bounded holomorphic in the right half-plane, globally meromorphic, and flat to every inverse power on the positive real axis. These properties do not force it to vanish: $e^{-z}$ has all of them and is nonzero.

No application of a Fox H-function or inverse Mellin theorem is accepted here. The proposed class-specific uniqueness step still requires an actual analytic germ, a common neighborhood and summation estimates uniform over the unbounded integer shifts, the appropriate convolution result, and a proof that the full asymptotic expansion determines that germ and its continued density. A theorem about one fixed Gamma quotient does not supply those facts for the infinite Gaussian sum.

Consequently arbitrary-balance phase removal, its exact fixed-phase product identity, and the resulting irrational finite-persistence conclusion remain unproved by this packet. The conditional handoff states this boundary correctly. The original-source observation bridge and general G4 remain separate obligations.

Next action: prove or refute the required class-specific all-orders-to-exact uniqueness property before invoking Carlson on a phase-independent identity.
