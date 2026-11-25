# Exact energy comparison for the locked conductor-23 two-shell test

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof, using the actual signed measure and continuous split-prime reference of the [two-shell detector](2026-11-25-conductor23-two-thin-product-shells.md) and [exact centering](2026-11-25-conductor23-shell-centering-boundary.md). No new signed prime bound or Lean verification. The norm equivalence here is on a full sweep of a finite restriction, not a converse for the one-sided late-window criterion.

## A square-root-normalized shell does not erase a frequency band

Lock the cutoffs and take a finite restriction of the signed measure nu, including its reference component. For a prescribed finite window, choose the restriction to include both shell supports throughout the window, so it changes no values in the window. Put y = log t and let m(dy) = exp(-y/2) d nu(exp y), notation for weighting the logarithmic pushforward. Set
```
q(x) = integral R_d(log(t/x)) d nu(t),
S(u) = exp(-u/2) [q(exp u) - b^(-1) q(b exp u)],
B = log b,  r = exp(-B/2),  0 < 2d < B.
```
The weight H(v) = exp(v/2) R_d(v) has an exact convolution factorization:
```
H = E_+ * E_-,    E_+(v) = 1_[0,d](v) exp(v/2),
                   E_-(v) = 1_[0,d](v) exp(-v/2).
```
Before multiplying by exp(v/2), the convolution of 1_[0,d] and exp(-v) 1_[0,d] gives 1-exp(-v) for 0<=v<=d and exp(d-v)-exp(-d) for d<=v<=2d, by integrating over the overlap. Multiplying the integrands by exp(v/2) factors across convolution.

With R denoting reflection about zero, S = (delta_0-r delta_(-B))*R(H)*m. For Fourier convention exp(-i xi u), the square of the absolute kernel multiplier is exactly
```
|1-r exp(i xi B)|^2
  |exp((1/2+i xi)d)-1|^2 |exp((-1/2+i xi)d)-1|^2
  / (xi^2+1/4)^2.
```
Each of the three numerator moduli is bounded above and bounded away from zero, by the triangle and reverse triangle inequalities, with constants depending only on d,B. They are bounded away from zero even at xi=0. In particular, by Plancherel,
```
||S||_(L2(R))^2  is comparable, with constants depending only on d,B, to
   (1/(2 pi)) integral_R |m_hat(xi)|^2 / (xi^2+1/4)^2 d xi .
```
The right side is finite for every finite signed input, since its transform is bounded. The identity and comparison apply as well to each measurable frequency subset, cutting the integral of |S_hat|^2 to the same subset. In the exact prime-companion rectangle, m_hat is the product of the centered prime and signed companion sums with exponent -1/2-i xi, because the square-root weight also factors. This conclusion does not apply to a pair mask imposed after squaring.

Thus the cancellation of the bulk of the matched exponential mean in the [endpoint identity](2026-11-25-conductor23-shell-mean-boundary.md) must not be read as a notch in the square-root-normalized response. At bounded real frequencies the kernel gives no asymptotic power saving in absolute energy. At high frequency the amplitude decays quadratically; this comparison is for the original triangular shells, not the optional further smoothing.

## A local consequence which does not assume a full sweep

Writing D for differentiation in u, direct differentiation of the two truncated exponentials (as distributions), followed by reflection, gives
```
(D^2-1/4) S =
  (delta_0-r delta_(-B)) *
  (delta_0-(exp(d/2)+exp(-d/2)) delta_(-d)+delta_(-2d)) * m.
```
Indeed (D-a) E_a = delta_0-exp(ad) delta_d for a=+/-1/2. Reflection reverses each derivative's sign; the two minus signs cancel. The three masses result from multiplying the two reflected factors. For every smooth test phi compactly supported in an open subinterval J of the locked window, this yields exactly the signed six-shift test on m after moving D^2-1/4 to phi. Its absolute value is bounded by ||S||_(L2(J)) ||phi''-phi/4||_(L2(J)), with no endpoint contribution. This is only a necessary bound from local absolute energy, not a bound obtained from the one-sided test. These identities leave open the actual square-root-scale signed estimate on arbitrarily late windows.
