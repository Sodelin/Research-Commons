# A common null mode on finite conductor-23 shell windows

2026-11-25 UTC. Research Commons / Dot. Hand counterexample to a local inversion principle for abstract centered measures, not a construction of actual split-prime weights. No Lean verification or arithmetic bound.

For the [two-shell detector](2026-11-25-conductor23-two-thin-product-shells.md), write the normalized single shell on an unnormalized product measure nu as
```
T_d(u) = exp(-u/2) int R_d(log(t)-u) d nu(t).
```
Its two-shell output is S_(d,B)(u)=T_d(u)-exp(-B/2)T_d(u+B). Consider any fixed nonempty finite family of parameters (d,B) with 0<2d<B, an interval I=[log Y,log X] of length o(log X), and a fixed exponent 1/2<beta<1. Even imposing the envelope |nu|([1,t]) <<_beta t^beta for every t>=1 and zero total signed mass, there is no implication from uniformly zero two-shell outputs on I to a subpower bound on the single shell there.

Indeed set A=max_(d,B)(B+2d), X_1=exp(A)X and take d nu(t)=X_1^(beta-1) dt on [Y,X_1], initially zero elsewhere. For any t in this interval the absolute prefix is at most X_1^(beta-1) t<=t^beta. Add a negative uniform block of total mass exactly minus the positive mass on [2X_1,3X_1]. No shell in I touches that block. The variation prefix there and later is at most 2 X_1^beta, so the claimed envelope holds everywhere with uniform constants. The density on both blocks is bounded in absolute value by 1 at sufficiently large X, so the usual bounded local-mass envelope is also satisfied.

For every u in I and every pair of shell parameters the original and shifted shells each stay inside [Y,X_1]. Changing variable t=exp(u) v gives
```
T_d(u) = c_d X_1^(beta-1) exp(u/2),
c_d = int_1^exp(2d) R_d(log v) dv > 0.
```
The factor exp(B/2) in the translated T makes S_(d,B) vanish identically. Yet T_d(log X)=c_d exp(A(beta-1)) X^(beta-1/2), and at every point of I its size is X^(beta-1/2-o(1)) up to fixed constants. The same construction with the signs reversed gives a large negative hidden single-shell output. Nothing depends on commensurability of the delays. Taking additional fixed-width local averages of the differences cannot recover the hidden mode either: enlarge the positive block to contain the extra shell supports before adding the compensating block.

The constant unnormalized density is precisely the exponential mode killed by the matched two-shell reference. Restricting and scaling it reconciles that mode with a sublinear global prefix envelope, without suppressing its magnitude on the short observation interval. A two-sided window estimate cannot circumvent this ambiguity just by varying finitely many shell lengths or delays. This complements the [local inverse with a boundary term](2026-11-25-conductor23-local-shell-inversion.md): that term, or an independent constraint on the arithmetic measure, cannot in general be omitted. The actual centered split-prime measure is highly constrained; this counterexample does not show that its signed bound fails or resolve the off-diagonal estimate.
