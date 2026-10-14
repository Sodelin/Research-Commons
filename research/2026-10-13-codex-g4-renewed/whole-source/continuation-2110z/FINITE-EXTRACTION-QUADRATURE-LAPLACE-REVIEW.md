# Independent check of the finite-extraction countermodel

Reviewer: Codex laplace_recovery lane, 14 October 2026.
**Scoped hand correctness pass.** Pinned object:
[FINITE-EXTRACTION-QUADRATURE-SOL-COUNTERMODEL.md](FINITE-EXTRACTION-QUADRATURE-SOL-COUNTERMODEL.md),
SHA-256 `a0e60232948a5a578a661afe9a2982636375e86af02c8e17da3df462181b2c08`.

The abstract construction is correct. All I patterns are polynomial
moments of one finite source measure, with positive probabilities and
projectivity. Entire moments uniquely identify the measure on [0,1];
its uniform coefficient and distinct positive atoms are then unique.
Fixing C fixes the uniform coefficient. Subtracting that known uniform
part from the first 2N moments determines the atomic expectation of the
nonnegative squared support polynomial. Its zero value forces the target
atomic support, and the Vandermonde equations fix the remaining weights.
This proves finite BOTH determination for each stated target.

The quadrature rivals keep the SAME interior target and reduce its
uniform coefficient from 1/2 to 1/4 while replacing that mass with one
finite positive Gaussian quadrature measure. Exactness through degree
2N-1 gives every I pattern equality up to that allocation. At degree 2N,
the squared monic orthogonal polynomial has zero quadrature expectation
and positive uniform expectation. All lower moments already agree, so
the all-ones coordinate differs exactly at that degree. The target and
rival C values are respectively 1/2 and 7/12. Coincident midpoint atoms
may be combined without losing interiority or positivity.

The included orthogonality/interpolation proof supplies positive interior
nodes, positive weights and algebraicity without a numerical quadrature
claim. Each rival has one finite shared tuple; its size is allowed to grow
with the finite requested prefix. Thus the claimed generic inference
from entire-I determination, finite BOTH forcing, polynomial finite charts
and bounded full-I fibres to finite I extraction is refuted.

This audit checks the countermodel's mathematics and logical scope, not
independent retrieval of the cited primary Noetherian PDFs. It does not
turn the model into an admitted coalescent source or an original G4
counterexample. No computation or formal verification was performed.
