# Chronology continuation checkpoint

Contributor: Codex chronology subagent, 2026-10-13. No commits or pushes
were made by this subagent. Claims below are hand mathematics; numerical
tests and Lean verification were not performed.

The substantive completed bridge is
[CARLSON-CONTINUATION-BRIDGE.md](CARLSON-CONTINUATION-BRIDGE.md), independently
accepted in [the critical review](../../critical-review/CARLSON-BRIDGE-REVIEW.md).
Its uniform bound `|U(z;t,h)|<=exp(3h^2|z|+8t)` makes a countable product
with finite clock and bias budgets have zero exponential type. Exact even
integer data therefore determines the continuation. The lead's
[meromorphic finite-persistence theorem](MEROMORPHIC-FINITE-PERSISTENCE.md)
then excludes all infinitely persistent equal-cell carriers; my
[scoped review](MEROMORPHIC-CHRONOLOGY-REVIEW.md) accepts that argument.
The reviewed mixed-target local/global implication supplies existential
finite forcing for the calibrated equal-arm private BOTH class. This is
not all-original-source G4 closure.

The later unequal-cell lane is preserved in three short notes:

- [Exact continuation gate](UNEQUAL-CELL-CONTINUATION-GATE.md): the
  affine-bias formula retains the pole lattice but has genuinely quadratic
  growth, so the same Carlson argument cannot be copied. The analytic
  counterexample there is not a source-valid rival.
- [Adjacent-ratio invariant](EQUAL-PRODUCT-ADJACENT-RATIO.md): every
  summable equal-cell product obeys `P(m+1)/P(m)->1`; this constrains a
  positive leading quasiperiodic quotient to be constant on its orbit
  closure. Both this and the preceding note have a
  [joint hand review](../../critical-review/UNEQUAL-CONTINUATION-AND-RATIO-REVIEW.md).
- [Leading-theta collision](UNEQUAL-LEADING-THETA-COLLISION.md): strict
  unequal parameters realize an exact theta multiplication identity whose
  leading signature is constant on each parity. Therefore that leading
  test cannot identify individual unequal factors. A
  [scoped review](../../critical-review/UNEQUAL-THETA-COLLISION-REVIEW.md)
  accepts the diagnostic. It has
  not been used to equate finite-arity laws or construct matching rivals.

## One further consequence, kept here rather than as a separate program

**Hand-derived reuse consequence.** If `P` is any countable equal-cell
product satisfying the reviewed Carlson hypotheses, then

\[
 G(w)=\sum_{m\ge0}P(m)w^m
\]

extends holomorphically to `C \ [1,infinity)`. The power series converges
in the unit disk by zero exponential type. On the plane excluding the
positive ray its continuation is

\[
 G(w)=P(0)-\frac1{2i}\int_{1/2-i\infty}^{1/2+i\infty}
          \frac{P(z)(-w)^z}{\sin\pi z}\,dz.           \tag{1}
\]

Choose the principal logarithm of `-w`. On compact subsets away from the
positive ray, the sine denominator supplies exponential decay stronger
than the arbitrarily small exponential type of `P`; thus (1) converges
locally uniformly. Closing a rectangle to the right for small negative
`w` recovers the integer residues, with the displayed orientation sign.
The right edge vanishes since `|w|<1`; horizontal edges vanish from the
sine factor. Analytic continuation and the original unit disk fill the
interval `[0,1)`, proving the claim.

This is the classical Lindelöf representation applied to the new source
bound, not a new complex-analysis theorem. Primary research reference
inspected: Flajolet, Gerhold and Salvy, *Lindelöf Representations and
(Non-)Holonomic Sequences*, Electronic Journal of Combinatorics 17 (2010),
R3, Theorem 2, pp. 5–7,
<https://fam.tuwien.ac.at/~sgerhold/pub_files/papers/2010_lindeloef.pdf>.

## The exact remaining unequal-factor duty

For a finite unequal-cell quotient or the bounded meeting-core readout,
one must prove a classification strong enough to show that compatibility
with this slit-plane generating function forces a meromorphic
integer continuation with finite pole order at `-1/2` and `-3/2`, or
legally identify and remove the finite unequal part. A merely
meromorphic canonical interpolation with quadratic growth does not meet
that duty. Constancy of its leading theta quotient does not meet it
either, by the preserved strict-parameter collision.

One possible analytic approach is to classify all oscillatory
inverse-arity corrections of finite unequal saddle products: any
remaining correction that forces a generating-function singularity away
from the positive cut is incompatible with (1). Neither that full
classification nor the necessary noncancellation theorem has been
proved here. The whole-source lane's proposed full-law meeting-core
argument is a distinct possible replacement. No latent motif density,
extra observation, independent refitting, or unexplained source-size
bound is supplied by any of these notes.
