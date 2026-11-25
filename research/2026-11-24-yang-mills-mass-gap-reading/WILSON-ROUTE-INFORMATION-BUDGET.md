# Information budget for selecting nearby bare Wilson routes

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction for the deterministic bare route pool of [the conditional Haar comparison](WILSON-NEARBY-ROUTE-TOTAL-VARIATION.md). No simulation, Lean verification, or mass-gap conclusion.

Condition on the exterior links of the previous result. Fix a base route whose transport is exterior measurable, and M alternatives. Let the conditional total variation error for the comparisons be delta, with the earlier bound uniform in the exterior. Let the router use an arbitrary observation of the interior, but with at most K possible messages for each fixed exterior value, plus optionally independent coins. The observation can have arbitrary dependence on all the selected links. Given the exterior, the message, and its independent coins, the router selects one alternative.

For any radius t, write h(t) for the Haar probability of discrepancy at most t. Then
```
Pr(selected discrepancy <= t | exterior)
  <= 1 - (1-h(t))^min(K,M) + delta
  <= min(K,M) h(t) + delta.
```
To prove this, first fix the coins. For the fixed exterior and coins the set of possible selected indices has cardinality at most min(K,M); crucially this set is fixed before the selected links are revealed. Success implies that this set contains at least one comparison in the Haar ball. This is a union of coordinate hit events in the full tuple, so one application of the total variation error suffices. Under the reference product law its probability is exactly 1-(1-h(t))^s for a set of size s. Averaging over coins preserves the bound. The hypothesis concerns the number of distinguishable messages, not the number of computations performed by an observer. In particular, an exterior-only choice has K=1. For b binary bits and t tending to zero, nonvanishing success as delta tends to zero requires 2^b times t^3 not to tend to zero, since h(t) is asymptotic to t^3/(3 pi sqrt(2)).

The budget is sharp within this model: choose any fixed pool of s<=min(K,M) indices, observe all s discrepancies, and report the index of the minimum. A message alphabet of size s suffices; up to delta, success is exactly 1-(1-h(t))^s. This assertion does not bound the cost of finding the message: the encoder in this example can see every discrepancy.

## More candidates in the same physical tube

If the line direction is one of four coordinate directions and the other three transverse offsets are available, use every offset in {2,4,...,2w}^3 with the same base and a deterministic transverse connector at each endpoint. For w=o(L) there is no wrap in the transverse cube centered relative to the base; all detour lengths are O(w/L) in physical units. Any two transverse vectors differ by at least two lattice units in one coordinate, so the longitudinal links share no plaquette, just as in the previous proof. The transverse connectors contain no selected longitudinal links. Consequently M=w^3 is allowed in the same conditional bound, and the minimum bare discrepancy scales as w^(-1) rather than the w^(-1/3) obtained by only using one transverse direction. If m is comparable to L and beta_W=O(log L), the total variation error still vanishes.

This gives a quantitative distinction between a router that uses only exterior information and one whose interior statistic actually distinguishes many candidates. It does not show how much information the published nonlinear routing data carry, whether a routing cutoff preserves the conditional reference law, or how either fact would imply a continuum physical mass.
