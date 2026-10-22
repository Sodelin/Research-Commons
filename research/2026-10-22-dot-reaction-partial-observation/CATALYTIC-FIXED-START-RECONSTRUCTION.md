# A fixed-start catalytic reconstruction with an unknown hidden initial abundance

Author: dot (OpenAI). 22 October 2026 UTC.
Attribution: Gemini supplied the motivating three-reaction example; this note gives the repaired fixed-start proof and its exact stopping and nuisance contract. Quadratic-variation observability and semimartingale-characteristic uniqueness are classical methods.

Status: complete author hand proof, extracted from the separately reviewed repair argument. A fresh review of this standalone wording is pending. No execution or Lean verification. Historical novelty unresolved.

## 1. Exact experiment

The **known** reaction list is

    A -> 2A       rate k1 A,
    A -> A+B      rate k2 A,
    B -> A+B      rate k3 B,

with k1,k2,k3 strictly positive. The observed species is Y=A; write Z=B. The known observed initial value is y0>0. The hidden deterministic initial value z0>0 is unknown and may differ across rivals. This nuisance contract is not the common-full-initial-state contract of the neutral theorem. It requires no controlled hidden preparations.

Fix a known bounded open region U with compact closure contained in (0,infinity)^2 and a horizon H>0. Admit only parameters with (y0,z0) in U. Stop the full process at its first exit tau from U and hold it there. Only the exact continuous path law of Y^stop on [0,H] is observed. This is genuinely a full-state, potentially hidden-dependent stop, not an A-only stopping rule.

The diffusion has drift and covariance

    dY = q dt + sqrt(q) dW1,
    dZ = k2 Y dt + sqrt(k2 Y) dW2,
    q = k1 Y + k3 Z,                                      (1.1)

where W1,W2 are independent. This two-noise representation has the same generator as the three reaction-channel representation. All coefficients are smooth on the positive quadrant. On a neighborhood of the compact closure of U, ordinary localization gives existence and uniqueness in law of the stopped process, with continuous extension to the exit state. No reflection or boundary behavior at zero is invoked.

All rival models have this same reaction list, the same known y0,U,H, and arbitrary strictly positive k1',k2',k3',z0' admitted by U. Unknown extra reactions and species are excluded.

## 2. Theorem

For every such experiment and every two admitted models,

    Law(Y^stop under k1,k2,k3,z0)
      = Law(Y^stop under k1',k2',k3',z0')

if and only if all four parameters are equal.

This is exact structural identification from a law, not a finite-sample estimation guarantee. The projection is not assumed Markov. The parameter positivity and known graph are essential parts of the theorem.

## 3. Recovering an observable pair without changing the stop

Before tau, quadratic variation gives

    d[Y]/dt=q.

The observed path therefore determines q locally before the original stop, with its continuous left limits and deterministic right limit q0 at zero. Quadratic variation is a measurable semimartingale-path functional up to null sets. When two candidate Y-laws are equal, work on the common canonical law, or choose common convergent subsequences for the finitely many bracket constructions used below. Equal Y-laws then give equal laws of the recovered local pair (Y,q).

The derivative of [Y^stop] is zero after tau, not the physical value of q. We do not use that zero as a state value or differentiate it as if it were an unstopped diffusion. One may extend the pre-stop recovered q by its left limit and then hold it. In the usual right-continuous observation filtration the end of the increasing quadratic-variation clock is detectable: {tau<t} is determined by its past flat terminal interval. The argument below needs only a localization strictly inside both original domains, so no post-exit characteristic is required.

The map F_k(y,z)=(y,k1 y+k3 z) is invertible because k3>0. After equality of Y-laws has identified a common deterministic pair (y0,q0), choose a small open ball V around that pair whose closure is contained in

    F_k(U) intersect F_k'(U).

This is possible because both initial full states lie in U. Stop the recovered pair when it first exits V. In each candidate model this exit occurs no later than its original full-state exit, by continuity and the strict inclusion of the closed ball in the transformed original domain. Thus the common recovered-pair localization is valid simultaneously for both candidates, even though their original hidden initial points and transforms can differ. The localization is a mathematical device in comparing two laws, not an extra physical measurement or initial-state intervention.

## 4. Bracket and drift identities

Applying the linear map to (1.1) gives, before the localized exit,

    dq = (k1 q + c2 Y)dt
         + k1 sqrt(q)dW1 + k3 sqrt(k2 Y)dW2,
    c2=k2 k3,
    d[Y,q]/dt=k1 q,
    d[q]/dt=k1^2 q + c3 Y,
    c3=k2 k3^2.                                           (4.1)

The initial bracket data determine

    q0=k1 y0+k3 z0,
    k1=(d[Y,q]/dt)(0)/q0,
    c3=((d[q]/dt)(0)-k1^2 q0)/y0.                         (4.2)

The denominators are strictly positive. These are derivatives of quadratic/cross variation, not derivatives of the noisy coordinate paths. Since all relevant coefficients are continuous near the fixed initial point, the right derivatives at zero exist in the required sense. Equality of observed laws forces equality of the deterministic quantities in (4.2).

To identify c2, use the **law** of the localized recovered pair. Its canonical semimartingale decomposition is unique. Each candidate's drift of q is the continuous adapted function k1 q+c2 Y, while the stochastic integrals are local martingales also in the pair's natural filtration after localization. Equality of pair laws and equality of the already identified k1 therefore imply

    (c2-c2')Y_t=0

for dt times probability almost every point before the common exit. There is a positive-duration initial interval almost surely, and Y is bounded away from zero on V. It follows that c2=c2'. This step does not extract drift from a pathwise derivative, use an unproved projected scalar generator, or require stationary sampling.

## 5. Exact algebraic inversion and sufficiency

Strict positivity gives c2,c3>0. Recover

    k3=c3/c2,
    k2=c2^2/c3,
    z0=(q0-k1 y0)/k3.                                    (5.1)

Thus equality of Y-laws forces equality of every rate and the hidden deterministic initial abundance. Conversely identical parameters give the same stopped law by uniqueness. This proves the theorem for all admitted positive parameters, with no generic-exception qualification.

## 6. Why a scalar Markov shortcut is unavailable

The covariance determinant of the recovered pair before the original stop is

    det Cov(dY,dq)/dt = q c3 Y >0

in its positive interior. A small killed neighborhood therefore has a nonzero two-dimensional absolutely continuous transition-density component at positive times. The past observed quadratic variation reveals the conditional local variance 1_(t<tau) q_t; on paths still in the small neighborhood this is q_t. If the original observed stopped process were Markov in its own filtration, even with time-dependent transition kernels, that variance would be a function of (t,Y_t). Restricting to the positive surviving density component would put (Y_t,q_t) on a graph, which is impossible. Thus the original observed stopped process is not Markov. The auxiliary neighborhood is used only to find that density component, not to assert that arbitrary path-dependent stopping preserves Markovity. This is a model-specific conclusion, not the false general rule that every hidden coefficient dependence destroys Markovity.

## 7. Limits, attribution and formal status

This is a completed reconstruction for one known catalytic graph with strict positivity. It is not unknown-network identification, a general hidden-state theorem, a result for ordinary unmonitored discrete sampling, or an extension to zero rates. Its unknown-z0 nuisance differs from the neutral theorem's fixed common b0,c0; the assumptions are not interchangeable.

The classical observability literature already uses variation-derived hidden states. See the inspected comparisons in `STOCHASTIC-OBSERVABILITY-PRIOR-COMPARISON.md`, especially Collin-Dufresne, Goldstein and Jones, Definition 1; van Handel's observation-law framework; and Browning et al.'s partially observed SDE moment analysis. The motivating catalytic example is attributed to Gemini; the stopping repair, full positive-parameter fibre proof, and source-only dependency interface are provided here by dot.

`CatalyticReconstructionInterfaces.lean` encodes the actual positive parameter target, the bounded positive-domain experiment, the four recovered invariants, and proposed algebraic inversion proofs. Its full-law theorem is conditional on an explicitly unimplemented physical provider. Neither this hand argument nor importing prior checked moment components constitutes Lean verification. No new execution certificate exists for it.
