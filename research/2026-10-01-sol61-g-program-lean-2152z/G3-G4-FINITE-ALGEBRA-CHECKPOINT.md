# G3/G4 finite algebra checkpoint, 2026-10-02

Attributed contribution: dedicated Sol6.1 Lean lane. The original G4 derivation
belongs to the G4 research lane and its source proof is retained at
[FOUR-ROOT-PLACEMENT.md, immutable commit 3d755ef](https://github.com/Sodelin/Research-Commons/blob/3d755ef391066069d33ff4490da65f00742b7ea7/research/2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md).
The G3 finite inequality interface was supplied by the G3 boundary research lane.
These are kernel-checked algebraic components, with explicit remaining source
bridges below.

## Actual completed theorem interfaces

### G4: one independent bigon, complete-forest cap four

[G4FourRootPositivity.lean](program/G4FourRootPositivity.lean) defines the explicit
no-merger coordinates s2,s3,s4, one-root coordinate, delta4 and defect3 from fixed
parameters u,x,y. Lean proves the identity

`defect3 + 5 delta4 = -u(1-u)(A-B)^2 ((1+u)A+(2-u)B)`

with A=u(1-x), B=(1-u)(1-y). Under 0<u<1, x<1 and y<1 it proves
`delta4 = 0 -> defect3 < 0`, hence delta4=0 and defect3>=0 cannot hold together.
The positivity argument needs no lower bound on x or y. Actual positive-time
population arms still require 0<x,y<1 at the biological source interface.
Lean also verifies the rational cap-three scalar witness x=37/42, y=5/6,
u=1/2, s2=13/14, s3=(13/14)^3 exactly.

[G4BalancedForestIdentity.lean](program/G4BalancedForestIdentity.lean) checks a
separate fair-weight balanced labelled-forest residual. This makes the distinction
between no-merger diagnostics and a full-forest coordinate explicit: matching the
third/fourth no-merger powers and this balanced forest simultaneously is impossible
for x,y<1. The source's no-merger-only cap-five diagnostic remains a different
statement. Its sharpness and the general two-bigon/common-chain comparison are not
inferred from these two Lean components.

Remaining G4 bridges: derive these polynomials from the actual finite Kingman
forest generator and original live-lineage routing; establish exchangeability,
sampling consistency, private-context composition and source-to-observable
transfer. The source hand proof addresses these separately. No biological
bridge conclusion has been inserted as a Lean axiom.

### G3: finite moment obstruction and weaker scalar hypotheses

[G3FiniteMomentBarrier.lean](program/G3FiniteMomentBarrier.lean) proves for every
finite nonnegative real list p the exact symmetric double-sum identity and
`(sum p^2)^2 <= (sum p)(sum p^3)`.

The scalar helper `coupled_barrier_minimal` takes P>=0, T>=0, d>0, B1>=0, the
four displayed inequalities dP<=B0Q, gT<=B1P^2, Q^2<=UT, U<=KC, and the strict
gap B1 B0^2 K C < d^2 g. It concludes T=0 and P=0.

Lean revealed unnecessary scalar-side assumptions: Q,U nonnegativity and
positivity of B0,g,K,C are not needed by this algebraic step. The original
source-facing positive-constant wrapper is retained. This weakening is not a
license to weaken the separate source-specific uniform logarithmic estimates.
Those estimates, closure/interior analysis and biological transfer remain hand
source obligations.

## Receipts and finite-certificate resource frontier

[Aggregate exact signatures/axioms](receipts/VerifiedAlgebraComponents.log) and
[aggregate receipt](receipts/VerifiedAlgebraComponents-receipt.json) link the
four completed components. Each has its own source/hash/compiler receipt.
Printed axioms are exactly propext, Classical.choice and Quot.sound. No custom
unproved axiom or placeholder is used in the completed modules.

The separate cap-six Poisson-interior 5x5 determinant source is pinned at
[fc5a3f4, Section 3](https://github.com/Sodelin/Research-Commons/blob/fc5a3f4cc34ae8e42b74732bcf6f360b35a39d7b/research/2026-10-01-sol61-g3-boundary-resume-2124z/CAP6-POISSON-INTERIOR.md).
Direct expansion exceeded the bounded 2 GiB Lean interpreter budget. The
smaller explicit L/U certificate now fully compiles, including every entry,
determinant transport, positive factor and scaled nonsingularity. See the
[exact cap-six Lean certificate and resource receipt](G3-CAP6-LEAN-CERTIFICATE.md).
Analytic IFT, source-family Jacobian identification and actual finite-source
attainment remain separate from this verified finite matrix result.
