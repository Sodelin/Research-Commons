# First-order mode defect of a vanishing equal-arm meeting cell

Contributor: Codex whole-source lane, 14 October 2026.
**Hand-proof candidate for independent audit.** This is a fixed-cap local
source estimate, including endpoint coins. It addresses the sign of a
zero-duration FINAL A meeting cell; it neither treats positive-duration
endpoint activation nor proves the full original local cone theorem.

## Exact setup and assertion

Use an original anchor pair A,B with no jointly ancestral hybrid. In its
opened meeting representation, the last A hybrid has two full A arms of
equal exposure t>=0, meeting at J, with original coin g and p=g(1-g).
There are n selected A roots and one B root. The single B may enter an A
arm before J, may use a mixture of its two original ports, or may meet A
only above J. All its routing choices remain as in the actual source.

Compare two kernels on this SAME parameter tuple and opened meeting:
V_I routes the A roots independently at this one hybrid, and V_C routes
them with one common bit. All other operations are identical. Every B
hybrid carries one root before contact, so no B-mode change is required.
The statement also holds with arbitrary opaque trees on the entering A
roots. No modified source is proposed as an observation.

Let U_0 be the selected continuation after setting every segment of the
two A arms to zero exposure, retaining B's routing law and all other
upper parameters. This is only an auxiliary finite-cap boundary kernel.
Let Q_A be the ordinary pair-merger generator on the entering A roots,
with B held separate. Then, for t in a fixed bounded neighborhood of zero,

    V_I-V_C = -2p t Q_A U_0 + R_n,
    ||R_n||_1 <= C_n p t^2.                         (1)

The bound is uniform in g in [0,1], in the relative positions of B's
attachments inside the two shrinking arms, and in all other stochastic
upper-completion parameters. The two-arm length sum is 2t. The finite
opened shape and cap determine C_n. In particular the normalized defect
at strength w=p(exp(t)-1) tends to -2 Q_A U_0 as t tends to zero,
uniformly also when g tends to an endpoint.

## Source proof

Condition on the finite B-routing configuration. A single B lineage
undergoes no merger on its B-only passages. Any interaction it has below
J lies on a segment of an A arm. Each such segment has nonnegative
exposure at most t. The sum of all relevant shrinking edge exposures
is at most 2t. In the opened ordinary tree all A arm-routing distinctions
have disappeared once its surviving roots reach J.

Expand the finite-edge ordinary transition operators to first order in
these shrinking exposures. The no-event state at J is the same under
both modes. Consider one specified A/A pair. In COMMON its two roots use
arm 0 together with probability g and arm 1 together with probability
1-g, so their total first-order merger coefficient is

    g t+(1-g)t=t.

In INDEPENDENT it is

    g^2 t+(1-g)^2 t=(1-2p)t.

The corresponding off-diagonal merger and compensating diagonal give
exactly -2p t Q_A, before the same collapsed continuation U_0.

For an A/B pair, only one A routing bit is involved. Its marginal arm
law is the same in the two modes. The B routing law is independent of
that site's bit and is retained, including correlations among B's own
path choices. Thus every first-order A/B merger coefficient, and its
diagonal compensation, agrees. There is no B/B pair. Upper continuation
after a merger is the same opaque graft in both modes; the arm of that
single merger leaves no remaining routing state after J.

This proves the linear term in (1), without assuming that B waits above
the A-arm join. In particular the mixed first-order terms have been
checked, rather than removed by a fictitious private-cell replacement.

For the remainder, at a fixed cap every relevant edge generator has norm
bounded by a constant depending only on n+1. The total shrinking exposure
is at most 2t, so the multivariate matrix-exponential expansion has a
uniform quadratic remainder C_n t^2. Composing arbitrary stochastic
lower/upper kernels cannot increase the row l1 bound.

The stronger factor p is also uniform. For each fixed cap the difference
between the two routing rules is a polynomial in g of degree at most n,
with matrix coefficients given by those same ordinary edge products.
It vanishes identically at g=0 and g=1, as does its displayed linear
term. Polynomial division therefore factors the REMAINDER as g(1-g)
times a matrix polynomial. Each coefficient of that remainder is O_n(t^2)
by the preceding edge expansion; division in a fixed degree uses only
fixed finite linear combinations of coefficients. On g in [0,1] its
quotient is bounded by C_n t^2. Average over B configurations and compose
the unchanged stochastic continuation to obtain (1).

## Applicability and remaining gap

Nonnegative full arm lengths are essential: t tending to zero forces
every A-arm segment, including any mixed segment, to shrink. A zero
INITIAL exclusive pad with positive full arm t does not satisfy this
lemma. Nor does a positive-duration cell whose coin alone tends to an
endpoint. Those cases cannot be replaced by (1).

The all-ancestral ratio palette separately ensures that an unequal full
arm difference cannot tend to zero or have an endpoint coin inside the
fixed natural COMMON fibre. Thus the vanishing-full-arm ghosts to which
(1) applies are exactly equal-arm ghosts, as required here. Equation (1)
places even a mixed zero-duration final cell in the same negative ordinary
generator direction as the small private cells. Combining that direction
with observable finite-body secants still requires the original
COMMON-cost cone argument. No completion of that argument is claimed.

Providers: original finite capped forest compiler and stochastic source
composition; the opened anchor meeting reduction in
[ANCHOR-AND-MEETING-INVARIANT.md](../continuation-1900z/ANCHOR-AND-MEETING-INVARIANT.md);
and the separately stated
[all-ancestral unequal palette](ALL-ANCESTRAL-UNEQUAL-PALETTE-FROM-JOINT-COMMON.md).
Verification is the hand expansion above, not a computation or Lean proof.
