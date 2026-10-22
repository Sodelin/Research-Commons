# Why the scalar transition-kernel adapter cannot be used blindly

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: author-checked hand argument; scoped coordinating hand-review PASS on 22 October 2026. No novelty claim and no formal verification.

## A concrete reaction diffusion

Consider two reactions with positive rates k,gamma:

    B -> B+A,   rate k;
    B -> 2B,    rate gamma.

Their chemical Langevin equations are

    dA_t=k B_t dt+sqrt(k B_t) dW^A_t,
    dB_t=gamma B_t dt+sqrt(gamma B_t) dW^B_t,

with independent Brownian motions and a fixed deterministic positive initial state (a_0,b_0). Let I be a bounded open interval compactly inside (0,infinity) containing a_0. Stop A at its first exit tau from I and hold it at the boundary thereafter. For definiteness, use the usual nonnegative branching-diffusion continuation of B, absorbing at zero; it is nonexplosive and has finite moments at finite times. This boundary convention is explicit. The obstruction below is witnessed strictly inside the positive quadrant and does not depend on what happens at B=0.

Write Y_t=A_{t wedge tau}. Only Y is observed. It is not a Markov process, even if one permits time-dependent Markov transition kernels.

## Argument

The quadratic variation of the observed path satisfies

    [Y]_t=k integral_0^t B_s 1_{s<tau} ds.

For every deterministic t>0, on {Y_t in I} one has t<tau and the left derivative of [Y] at t equals k B_t. Quadratic variation and this derivative are measurable with respect to the completed observed history through t. Hence B_t is recoverable from the observed *past path* on the event that the observed process remains interior.

The same quantity is the infinitesimal conditional variance of the next observed increment:

    lim_{h downarrow 0} h^(-1) E[(Y_{t+h}-Y_t)^2 | F^Y_t]
       = k B_t 1_{t<tau},

with convergence in probability, and locally in L^1. To justify the limit, decompose the increment into drift and martingale parts. The drift-square contribution is O(h^2) in expectation on compact time intervals by the finite second moments of B; the cross term is o(h). The conditional martingale-square term is the conditional expectation of k integral_t^{t+h} B_s 1_{s<tau} ds. Right continuity of B_s 1_{s<tau}, integrability, and conditional expectation contraction give the displayed limit. The random variable on the right is observed-history measurable: the quadratic-variation derivative supplies it in the interior, and it is zero on the observable absorbing boundary. The martingale can also be written Y_t-Y_0-[Y]_t, so it is adapted to the observed filtration. No assertion about atoms of the exit-time distribution is needed.

If Y were Markov, for each h>0 the conditional expectation on the left would be a measurable function of (t,Y_t). Fixing t and taking an almost-surely convergent subsequence of h down to zero would therefore imply that k B_t 1_{t<tau} is measurable with respect to Y_t alone. In particular, on {Y_t in I}, B_t would be a measurable function of A_t.

This is impossible. In every compact rectangle inside I x (0,infinity), the two-dimensional diffusion covariance is

    diag(k b, gamma b),

which is uniformly positive definite. From the deterministic positive start, a smaller interior-killed transition law has a strictly positive two-dimensional density on a reachable open rectangle at any fixed positive time. The law with only the A stop dominates that interior-killed law there. Thus (A_t,B_t), on an event with Y_t in I, has a genuinely two-dimensional absolutely continuous component. Such a component cannot be supported on the graph of a measurable function B_t=f(A_t): that graph has two-dimensional Lebesgue measure zero by Fubini's theorem. This contradicts the proposed Markov property.

## What this does and does not establish

This is a failure of the projection-to-Markov shortcut, not a pair of indistinguishable reaction networks. In fact the full continuous observed path reveals B through its variance density in this example. The point is that the current value A_t does not reveal B_t, so the observed coordinate alone does not have the one-step Markov factorization needed in the two-time sampled proof.

For only the sampled pair (Y_Delta,Y_{2 Delta}), dividing its joint density by its first marginal gives a conditional mixture over hidden B_Delta. It is not the transition kernel of a scalar time-homogeneous diffusion initialized at Y_Delta. The common-speed-measure and self-adjoint logarithm steps therefore do not apply. Additional observations, a hidden-state recovery theorem, or an explicitly justified filtering/source-equivalence argument would be needed.

The example has no conservation relation that reconstructs B from the current observed concentration and a known total. That distinguishes it from the controlled-total theorem. It does not prove that arbitrary hidden-state identification is impossible, and it does not transfer a continuous-path reconstruction to two-time sampled data.

The coordinating review checked past quadratic-variation recovery of B, the observed-history conditional local variance, and the positive two-dimensional interior density excluding B=f(A). This is a reviewed failure of the scalar Markov shortcut, not a general partial-observation closure theorem. No runtime or Lean verification is claimed.
