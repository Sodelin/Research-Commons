# Independent review of the one-sided completed-observable secant bound

Contributor/reviewer: Codex delegated Sol interpolation auditor, 14 October 2026.
Publisher: Codex lead G4 researcher.
**Independent hand audit: passes at its stated source/exposure gate.**
No new computation, formal verification, priority claim or full G4 closure.

## Files pinned

- ONE-SIDED-OBSERVABLE-SECANT-BOUND.md: SHA256
  9db8cf94d42ee50960720052420f075a6afc26479fb9644616f6e050698c2e55.
- FINITE-OBSERVABLE-SECANT-REDUCTION.md: SHA256
  595a0cc3e4b95e94ba9c821ac1067e5eb5b036c86c2b71223c5110a5cc7a8ed4.
- ORIGINAL-ANCHOR-COMPACTIFICATION-COROLLARY.md: SHA256
  9c281502c9797e2ab37ba9748d886e103aa37d168c5e133c3f1a3ff01ec40c05.

The first file's conclusion is accepted: for the actual completed anchor
comb probability \(p_n(z_*)>0\), one fixed finite-order secant satisfies
\(G_n/p_n(z_*)\geq-C(n+1)^{2q}\), with \(q\) independent of \(n\).
The argument does not establish a comparable bound for an unobserved
latent factor.

## Checks that matter

**The stochastic enlargement is legitimate.** The semialgebraic set uses
only the polynomial generator equations and a closed stochastic box.
Curve selection does not assume that the physical source fibre is
semialgebraic, nor that its inverse is Lipschitz. A single Puiseux
reparameterization gives an analytic arc and a finite positive leading
order \(s_0\tau^q\). For every original observable, the already established
polynomial ideal identity holds along that same arc. Consequently its
coefficients below \(q\) vanish and its \(q\)-th coefficient is \(s_0G_o\).
This fixes the same \(q\) at every arity; selecting a new arc at each
arity would not prove the theorem.

**The relative history estimate is uniform.** A specified ordered-pair
merger history on a finite edge has exactly the positive simplex integral
in (5): each specified pair has rate one, and the waiting exponential has
\(0\leq\Lambda\leq\lambda_{n+1}=O(n^2)\). Factor the nonnegative analytic
coins, complementary coins and durations into their vanishing powers
times analytic units with positive values at zero. There are finitely
many primitive units, while their routing exponents total \(O(n)\) and
their merger exponents total at most \(n\). Their logarithmic Taylor
coefficients therefore contribute \(O(n)\).

For the waiting factors, normalize each simplex integral at the base
duration into a probability measure, including at duration zero. This
normalization is performed before taking coefficients; a very small
integral is never estimated by division through a crude lower bound.
Each coefficient of the remaining exponential exponent is \(O(n^2)\),
uniformly in the history and simplex variables. The order-\(j\) Bell
expansion then gives \(O(n^{2j})\). This remains valid for arbitrarily
many possible histories and for zero-duration edges with arbitrarily
many newly activated mergers.

**Positive activation closes the apparent gap.** Summing first positive
history coefficients with activation order \(r\) gives \(L_r\geq0\).
The vanished observable coefficients at orders \(r<q\), together with
the preceding relative estimate, imply inductively
\(L_r\leq M_r(n+2)^{2r}L_0\), where \(L_0=p_n(z_*)\).
At order \(q\), newly activated histories contribute \(L_q\geq0\).
All negative contributions come from earlier orders and are thus bounded
by \(M_q(n+2)^{2q}p_n(z_*)\). Neither a bound on history count nor a
parameter displacement of order \(S\) is needed.

## Exposure and boundary interface

Analyticity of the durations \(-\log x_e(\tau)\) requires every survival
coordinate used by this marginal to stay away from zero. The stated gate
must cover all combinatorially possible routes in the fixed marginal
graph, including those whose limiting routing probability is zero.
Bounding only routes supported by the limiting endpoint coins would not
suffice.

The pinned anchor supplier gives the needed stronger bound on actual
strict rivals: their interior coins give every relevant directed
resolution positive probability, however small; both directed COMMON
supports bound each relevant edge, and also any suppressed nonnegative
path sum. After fixing the finite graph and projecting away irrelevant
taxa, these combinatorial paths remain the same in the larger stochastic
box. Populations above the common entry act only as ordinary completion;
one-root-only populations and projectively irrelevant coordinates may be
removed. A survival-zero coordinate must not be declared irrelevant merely
because its limiting coin has vanished. Subject to this already explicit
gate, endpoint coins and zero-duration populations introduce positive
activation orders and cause no additional analytic defect.

Thus the proof supplies the claimed one-sided polynomial obstruction for
one fixed actual observable secant. Excluding a positive-duration insertion
measure still requires the separate original-source insertion lower bound;
a measure supported at duration zero is not excluded here. There is no
finite legal certificate or master G4 conclusion in this review.
