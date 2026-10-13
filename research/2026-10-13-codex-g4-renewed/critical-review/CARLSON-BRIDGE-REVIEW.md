# Independent analytic review: even-arity Carlson continuation

Contributor: Codex critical-review subagent, 13 October 2026. **Scoped hand acceptance**, independent within the current team, of [CARLSON-CONTINUATION-BRIDGE.md](../chronology/continuation-1837z/CARLSON-CONTINUATION-BRIDGE.md), SHA256 `9411158e6523c33243c4c0a894441bf0b695af13648c55a13f413f6d7022a2a7`.

The single-cell bound, locally convergent product, zero exponential type and Carlson uniqueness conclusions are correct under the stated summable clock and squared-log-odds budgets. This review does not yet accept any separate meromorphic pole/zero argument or infer general G4 closure from analytic continuation alone. No numerical or Lean verification was performed.

## Integer interpolation and contour branch

The Fourier coefficients of the shifted periodic heat kernel are `exp(-t k^2-hk)`. The even Fourier coefficients of `cos(theta/2)^(2m)` are the centered `Bin(2m,1/2)` probabilities. Their symmetry supplies the stated `cosh(hS)` expectation. This gives precisely the inherited even-arity residual sequence, without changing the observation model.

On the contour-shift rectangle, `cos((w-ih)/2)` has positive real part in the interior and only the two stated upper-corner zeros. Its principal logarithm therefore has argument between `-pi/2` and `pi/2`. The small corner integrals vanish for each fixed `Re z>=0`: the complex power is bounded there by a fixed `z`-dependent constant times a nonnegative radial power, and arc length tends to zero. The signs of the arguments on the two vertical edges give exactly the factors `exp(∓pi y)` used in the proof.

## Uniform growth estimate

I independently checked each estimate and constant.

- The direct modulus bound is `exp(h^2/(4t))`, since the remaining real heat kernel integrates to one. When `|Im z|>=pi/(32t)`, its exponent is at most `(8/pi)h^2|Im z|<3h^2|z|`.
- On the lower contour, the modulus bound `r^(2x)<=exp(xh^2/4)` and central argument bound `|arg|<=h|theta|/2` follow from the displayed elementary hyperbolic and tangent inequalities.
- Pairing `theta` and `-theta` gives a `cosh` argument factor with no multiplicative constant two per cell. The periodized central Gaussian integral is bounded by the unwrapped Gaussian moment `exp(t h^2 y^2)` because the chosen representative has the smallest absolute value among its translates.
- The outer wrapped-Gaussian mass is at most `2 exp(-pi^2/(16t))`; multiplying by `exp(pi|y|)` in the small-imaginary regime gives the stated `2 exp(-pi^2/(32t))` bound.
- Summing the vertical Gaussian images gives the stated `t^(-1/2)` estimate. The exponent after using `h<=1` and `|y|<=pi/(32t)` is `-(7pi^2-8)/(32t)`. The final absorption into `2 exp(-pi^2/(32t))` is valid because `(t/2)log(1/t)<=1/(2e)<(6pi^2-8)/32`.
- Finally `4 exp(-pi^2/(32t))<=8t` on `0<t<=1`, and `t y^2<=(pi/32)|y|`. These establish the claimed `exp(3h^2|z|+8t)` bound with room to spare.

The pairing and exponentially small boundary estimates are essential: multiplying raw `exp(h^2/(4t))` bounds over infinitely many cells would not be justified by the source budgets.

## Product convergence and uniqueness

For a compact set in the closed right half-plane, the shifted central power differs from one by `O_C(theta^2+h^2)`. Its Gaussian integral is `O_C(t+h^2)`. Away from the center its modulus is uniformly bounded on that compact set, including near the endpoint corners because `Re z>=0`; Gaussian and vertical contributions are exponentially small. Thus the local estimate `sup_C|U-1|<=A_C(t+h^2)` is valid.

Summability gives normal convergence of the infinite product. Each finite removed factor is globally bounded on the right half-plane by its finite raw heat-kernel bound. On the tail, the sum of squared log odds is arbitrarily small, while the sum of clocks remains finite. The displayed uniform growth estimate then proves zero exponential type. Zeros of individual factors do not invalidate normal product convergence; the product equals one at zero and is not identically zero.

I directly retrieved and read the opening Carlson statement in Jonathan Pila's [2003 primary note](https://people.maths.ox.ac.uk/pila/carlson.pdf). It requires holomorphy on the closed right half-plane, exponential type, imaginary-axis type strictly below `pi`, and vanishing on the nonnegative integers. Applying it to the difference shifted by one meets those requirements: that difference is holomorphic in an open neighborhood of the closed half-plane, retains zero exponential type, and vanishes at every nonnegative integer. Identity continuation then gives equality on the original open right half-plane. No integer-interpolation uniqueness principle stronger than Carlson is assumed.

## Source and master boundary

The inherited resource identity supplies finite total clock and finite `sum log cosh(h_i/2)`. Since this forces `h_i` to zero and the latter function is bounded below by a positive multiple of `h_i^2` near zero, only finitely many exceptional cells need removal to obtain the exact analytic hypotheses.

Accordingly the source's exact all-integer residual product identity does continue to the right half-plane. Establishing that such an identity precludes infinitely many persistent cells requires the separate meromorphic argument. Finite persistence must then be combined with the reviewed local theorem, and an original whole-core observation bridge remains a further scope obligation. This analytic review by itself claims none of those downstream conclusions.
