# The two-shell compensated mean is an endpoint statistic

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction for a potential averaging approach to the retained conductor-23 sum. No signed prime estimate or Lean verification.

Use the same locked cutoffs and signed measure nu as in the [two-shell detector](2026-11-25-conductor23-two-thin-product-shells.md). Let q(x)=integral R_d(log(t/x)) d nu(t), the single shell with its own reference subtraction, and s(x)=q(x)-q(bx)/b. This is the exact compensated two-shell difference, including the [prime-cutoff correction](2026-11-25-conductor23-shell-centering-boundary.md). Assume the cutoffs stay locked over all scales used below; no change of cutoffs is part of this argument.

For X>=bY the broad linear functional that matches the main-term scaling satisfies the exact identity
```
integral_Y^X s(x) dx/x^2
  = integral_Y^(bY) q(x) dx/x^2
    - integral_X^(bX) q(x) dx/x^2.
```
In the term q(bx)/b put y=bx: the measure dx/x^2 becomes b dy/y^2, cancelling the prefactor. The two integrals have the same integrand on [bY,X] and cancel there. If X<bY, the corresponding identity is the difference of nonoverlapping original and shifted full intervals.

This eliminates every interior product individually, not only after summing prime signs. Indeed put E=exp(d). On a complete positive x-axis sweep, the integral of R_d(log(t/x)) dx/x^2 is t^(-1) times the integral of R_d(log v) dv for 1<=v<=E^2. For the finite comparison, both complete shell traversals occur whenever bE^2Y<=t<=X, and the two contributions cancel exactly. This per-product assertion also applies to the continuous reference: on the bounded x-range the signed measure is locally finite on the supported products, so the integrals can be interchanged.

A broad near-flat weighted mean obeys a related identity. Put u=log x, f(u)=e^(-u)q(e^u), B=log b, and integrate against a compactly supported Lipschitz test w(u) within the allowed window. Then
```
integral e^(-u) s(e^u) w(u) du
  = integral f(u) [w(u)-w(u-B)] du.
```
With w(u)=W((u-U0)/L) the multiplier has magnitude at most (B/L) Lip(W), with support in the union of the two shifted supports. This attenuation is automatic for any signed input, not evidence of prime cancellation; in the sharp constant-weight case it degenerates to the endpoint formula above.

Thus a small value of this particular full-window mean cannot by itself diagnose a small signed interior. A proof using averages needs to retain a nonlinear quantity, a different weight with genuine sensitivity, or explicit control of endpoint and interior separately. Neither identity estimates the late one-sided window at square-root scale. These observations concern this matched-weight functional, not a prohibition on other averaging schemes.
