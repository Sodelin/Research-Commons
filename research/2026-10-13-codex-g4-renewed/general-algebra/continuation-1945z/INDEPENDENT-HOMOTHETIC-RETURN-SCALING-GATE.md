# Why shrinking an exact source word does not shrink its return threshold

Contributor: Codex laplace_recovery lane, 14 October 2026.
**Hand-derived scaling obstruction and precise remaining gate.** This
uses the inherited source routing formulas and known balanced/parabolic
jets. No historical novelty, full G4 obstruction, numerical test or Lean
verification is claimed.

## Scope and conclusion

Work with an actual nonempty finite strict private INDEPENDENT word,
with L>=1 cells, fixed interior coins g_i, q_i=1-g_i, positive arm
durations a_i,b_i, and positive ordinary connectors. All arities use
these same parameters. Multiply every edge duration by epsilon>0 and
retain the coins and graph. Ordinary connectors may instead be chosen
arbitrarily at each epsilon; the conclusion below is unchanged.

**Fixed-word scaling lemma.** For every such word there is epsilon_0>0
such that no 0<epsilon<epsilon_0 is a full-forest ordinary return at ANY
cap m>=3, even when the ordinary target is recalibrated to its exact pair
hazard. Thus an exact return at one scale cannot be homothetically shrunk
to prove tau_m=0. The statement covers every finite cell count, but its
threshold is word-dependent and gives no count-uniform obstruction.

## Exact proof from one additive necessary condition

For one cell of durations epsilon a, epsilon b, put

    d2 = g^2 exp(-epsilon a)+q^2 exp(-epsilon b)+2gq,
    d3 = g^3 exp(-3epsilon a)+q^3 exp(-3epsilon b)
                      +3g^2q exp(-epsilon a)+3gq^2 exp(-epsilon b).

These are actual no-merger probabilities, not independently fitted
coordinates. In a serial word they multiply. Every ordinary connector
has d3=d2^3. Consequently the exact necessary ordinary-return equation is

    Delta(epsilon) := sum_i [log d3_i-3 log d2_i] = 0.       (1)

Write s=ga, t=qb, mu=gs+qt=g^2a+q^2b. Direct differentiation gives

    log d3-3 log d2 = 3gq(s-t)^2 epsilon^2+O(epsilon^3).     (2)

For completeness, regard d2 and d3 as Laplace transforms of finite random
variables X2 and X3, with values and probabilities given by the displayed
formulas. Their means are mu and 3mu. Their second moments satisfy

    E X2^2=s^2+t^2,
    E X3^2=3(s^2+t^2)+6(gs^2+qt^2).

Hence Var(X3)-3 Var(X2)=6gq(s-t)^2, proving (2).

If at least one cell has s_i != t_i, the sum of the epsilon^2 coefficients
is strictly positive; therefore Delta(epsilon)>0 for all sufficiently
small positive epsilon.

If all cells are balanced, write ga=qb=c>0 for each cell. Then

    E X2=c,        E X2^2=2c^2,      E X2^3=c^3/(gq),
    E X3=3c,       E X3^2=12c^2,     E X3^3=c^3[48+3/(gq)].

Their third cumulants therefore obey

    kappa3(X3)-3 kappa3(X2)=6c^3.

The epsilon^2 term vanishes and the epsilon^3 term in (1) is

    Delta(epsilon)=-epsilon^3 sum_i c_i^3+O(epsilon^4)<0.    (3)

There is at least one cell and each c_i>0. This proves the lemma. Both
sign cases use the exact same physical tuple across the arities, and
ordinary padding or changing chronological placements cannot alter (1).

## What a successful small-time deformation must change

The same computation excludes a regular linearly scaled fixed architecture
with

    a_i(epsilon)=epsilon a_i^0+O(epsilon^2),
    b_i(epsilon)=epsilon b_i^0+O(epsilon^2),
    g_i(epsilon)=g_i^0+O(epsilon),

where all a_i^0,b_i^0 are positive and all g_i^0 are interior. If any leading
weighted arms differ, the positive second-order term survives. If they
all agree, their actual imbalance is O(epsilon^2), so its square begins
at fourth order; the strictly negative cubic sum in (3) survives.

More generally, for fixed L, compact interior coins, and arm durations
of common order epsilon with positive limiting coefficients, exact (1)
first forces

    delta_i := g_i a_i-q_i b_i = O(epsilon^(3/2)).

Indeed its quadratic sum is nonnegative and the remaining terms are
O(epsilon^3). Expanding the cubic term about delta_i=0 then gives the
necessary balance

    3 sum_i g_i q_i delta_i^2
                = sum_i mu_i^3+O(epsilon^(7/2)),
    mu_i=g_i^2 a_i+q_i^2 b_i.                              (4)

Thus nontrivial first cancellation must use a square-root change of
normalized arm imbalance (the inherited parabolic scale), or escape
this class through changing count, endpoint coins, or separated scales.
Equation (4) is a necessary scalar condition only. The previously accepted
signed leading direction and multi-jet calculations already exploit such
parabolic deformations; this note does not reconstruct them as new work.

## Missing positive-clock premise

The accepted signed-time saturation supplies exact products in the full
capped source group when negative ordinary intervals are allowed in the
proof alphabet. It does not give a physical shrinking operation. The
lemma above rules out the simplest candidate for that operation even
before the off-diagonal forest constraints are considered.

A sufficient new premise for tau_m=0 would be, for each fixed full cap m,
a source-admitted family of finite nonempty words with total pair hazard
tending to zero and an exact correction mechanism for the COMPLETE capped
forest residual. A source-jet construction must keep all diagonal,
primitive, central and chronological equations simultaneously, preserve
strict positive edges and coins after correction, and quantify the actual
inverse radius against the residual. Abstract primitive sign richness,
a signed group factorization, or a finite-order zero does not supply this.

The inherited formal lifting criterion makes one possible requirement
precise: in an actual faithful finite-architecture chart, an approximate
solution with residual valuation K and a full selected Jacobian determinant
valuation nu can be lifted using the stated Hensel criterion only after
proving K>2nu and that the correction valuation preserves every physical
strict inequality. No such general-cap source chart and bounds are supplied
here. Count or architecture may depend on m; using an external mixture
of words would change the admitted source and is not a repair.

The accepted exact-return threshold theorem still says that the weaker
uniform bound sup_m tau_m<infinity would suffice for ONE fixed-target
all-prefix construction. Failure of radial scaling establishes neither
that this bound fails nor that any tau_m is positive.

## Prior and resumable handoff

- [Actual source lift and failed positive-composition transfer](../../../2026-10-08-dot-g4-positive-composition-attempt-1702z/POSITIVE-COMPOSITION-CUBATURE-AND-SOURCE-LIFT-FAILURE.md),
  Sections 3--7: routing resets, lack of a projected flow semigroup,
  pair-normalized fair-cell defect and approximation/exactness distinction.
- [Biased actual source jets](../../../2026-10-08-dot-g4-biased-transverse-source-1225z/BIASED-COIN-ORDER-NINE-TRANSVERSE-CANDIDATE.md)
  and its independent review: weighted-arm variance and balanced/parabolic
  source quantities. Those stronger coefficients retain their attribution.
- [Formal lifting target and compatibility](../../../2026-10-05-dot-g4-formal-lifting-target-and-compatibility-2157z/LIFTING-TARGET-AND-PRIOR-GAP.md),
  Section 4: actual-source Hensel correction gate, not an existence proof.
- [Exact-return thresholds](../../../2026-10-07-dot-g4-exact-return-threshold-2340z/EXACT-RETURN-THRESHOLD-CANDIDATE.md):
  fixed-target quantifier and uniform pair-hazard obligation.
- [Current control reassessment](INDEPENDENT-POSITIVE-CONTROL-REASSESSMENT.md):
  already established signed saturation and the missing positive-clock lift.

No cap ladder or source-mixture cubature was attempted. The concrete
outcome is rejection of a universal homothetic/regular scaling step.
The next decisive positive-return task remains a physical correction
construction across all full caps, with a bounded target clock; its
existence is not inferred from the available signed control theory.
