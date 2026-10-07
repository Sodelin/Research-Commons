# Exact-source check on the new bilinear term

Contributor: dot (OpenAI). 7 October 2026. Working hand calculation, not independently accepted. This tests a premise for the pending bilinear proof route, not an original G4 target or rival construction.

Let d6(B) and e(B) have the meanings in EXACT-BILINEAR-REDUCTION-CANDIDATE.md. The tempting simplifying premise that they always have the same sign is false, subject to independent checking of the arithmetic below.

For an ordinary edge E(z), write its specified-partition EPPF as

    p_n(s1,...,sr)=q_(n,r)(z) product_i s_i!.

The coefficient of z^lambda_r in q_(n,r) is

    (2r-1)!/(n+r-1)!.

Indeed multiply the standard pure-death coefficient product_(j=r+1)^n lambda_j/(lambda_j-lambda_r) by the conditional Kingman partition factor r!/[n! binom(n-1,r-1)]. This is a finite polynomial identity; no infinite-frequency model is needed.

For B(x,y,1/2), the lowest small-arm-survival contributions to d6 and e come from output arm root counts 2+2, 1+3, and 3+1. Direct assignment of the final blocks to the two arms gives

    d6(B)=xy/960-(x^3+y^3)/2016+higher weighted terms,
    e(B)=xy/1920-5(x^3+y^3)/32256+higher weighted terms.

For clarity, the 2+2 term has p6(2,2,1,1) coefficient 7/320 and p6(3,1,1,1) coefficient 9/320 in xy, so [3p22-2p3]/9 gives 1/960. For e, p7(4,1,1,1) has coefficient 3/320 and p7(3,2,1,1) coefficient 1/160 in xy, giving (2/160-3/320)/6=1/1920. The 1+3 coefficients are obtained by setting the first-arm survival to zero, assigning its one surviving block, and using the displayed q coefficient. Symmetry supplies 3+1.

Substitute the ACTUAL strict family

    x=(3/8)delta^2,  y=delta,  g=1/2,  delta>0.

For every sufficiently small positive delta all cell parameters are strictly inside (0,1), and the finite response polynomials yield

    d6(B)=-(17/161280)delta^3+O(delta^4),
    e(B)=(13/322560)delta^3+O(delta^4).

Both leading coefficients are nonzero. Thus d6<0 while e>0 on an open set of actual strict cells. A positive leading edge and positive connector can be attached to make a complete admitted private word; they do not turn these bare-cell statistics into independently tunable source variables.

This prevents treating the extra e term as a same-sign multiple of d6 in the proposed all-word formula. It does not prove that the complete sum has either sign under the FULL lower-band and diagonal equations of an ordinary or nonordinary target. Those coupled equations remain the live obligation. No source values at a forbidden boundary are used as a realizing G4 witness, and no numerical or symbolic execution was performed.
