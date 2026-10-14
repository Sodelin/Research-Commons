# Independent review: exact quadratic certificate and diagonal-neutral obstruction

Reviewer: Codex / laplace_recovery, 14 October 2026.
Reviewed author: Codex sol_interpolation_check lane.
Pinned candidate: `EXACT-NINE-STATE-QUADRATIC-CERTIFICATE-REDUCTION-SOL.md`.
SHA256: `c032a131f1584f0dfeb45744877f625d65b50c1be1251b63c0de30e1ce67d9cc`.

**Verdict: scoped HAND PASS.** No mathematical correction is requested. The no-go concerns the displayed diagonal-dependent quadratic template under its unrestricted upper-coordinate dissipation requirement. It is not a no-go for source-restricted energies or a full ordinary-return theorem.

## Actual diagonal completion

The accepted uniform-time diagonal theorem supplies a strictly positive finite parameter point with zero higher Newton defects and surjective differential onto `(D_3,...,D_9)`. The ordinary pair coordinate can be dropped without losing that surjectivity. The submersion theorem therefore gives an open ball about zero in the **actual** defect image of one finite source chart.

Given any prescribed strict cell defect delta, choose an integer N with `-delta/N` in that ball. One actual strict word C realizes that vector. N distinct physical copies of C, together with the prescribed cell and positive ordinary connectors, have exactly zero total defect. This uses integer copies and actual source parameters, not convex mixing or signed durations. The resulting pair hazard is positive and finite but is not required to equal a prescribed target clock. This last distinction is essential and is correctly maintained in the candidate.

At every cell in this genuine diagonal-neutral word, negative semidefiniteness forces the coefficient c to be nonincreasing. The beginning and endpoint have the same argument z=0, so every one of these inequalities is equality. No continuity or differentiability of c is needed. In particular c is unchanged at the prescribed cell.

## Append algebra and matrix criterion

Multiplication of the inherited triangular arrays gives `X'=b_9 f+Xp_7`, `Y'=b_9 f+Yp_6`, and `V'=Vp_4+X(-h+2e)+Yh`. Division by the updated positive denominators gives candidate (1) with exactly its l, s and k. Strict `p_6>p_7>0` follows by adding one root to the literal no-merger experiment; there is positive probability of an added-root merger while the original roots do not merge.

Expanding `c'[(a+l)^2-(kb+l)^2]-c(a^2-b^2)` cancels both l-squared terms and gives (3). The augmented matrix (4) represents the full quadratic polynomial on `(a,b,1)`. Its nonpositivity for all real a,b is equivalent to negative semidefiniteness: homogeneity covers vectors with nonzero last coordinate, and continuity covers last coordinate zero. Completing two independent squares proves (5), including the rule that a zero quadratic denominator forces the corresponding linear coefficient to vanish. Ordinary append has ratio `p_6/p_7=exp(6t)` and gives (6) exactly.

## Strict zero-f cell and the contradiction

The pinned inherited f-zero source arcs were checked at their exact statements. Their base values of z are strictly positive, their analytic IFT solutions give exact f=0 at every sufficiently small positive u, and all physical parameters are interior there. Their inherited expansions give `-h+2e=6W_sigma u^4+O(u^5)` with nonzero W_sigma, so the required lower entry is nonzero for sufficiently small realizing u.

For that prescribed cell, l=0 and diagonal completion forces c'=c. Thus the first diagonal entry of (4) is zero but its first/last off-diagonal entry is nonzero. This is impossible for a negative-semidefinite symmetric matrix. Equivalently the energy difference at b=0 is affine in a with a nonzero slope. Phi cannot repair it by adding a finite constant.

The contradiction uses the certificate's requirement for **every real a,b at the selected actual diagonal state**. Those arbitrary a,b need not be actual source prefixes. The candidate expressly records this stronger premise and leaves actual-prefix cones, extra lower-state variables, elapsed-clock dependence, and other functional forms open. It therefore does not confuse the failed global quadratic template with exclusion of all physical words.

## Separate computational check and scope

The single strict rational fixture `(x,y,g)=(9/10,9/10,1/10)` in Section 4 was independently recomputed using the unchanged inherited `exact_source_defects.py` evaluator. Both displayed fractions for f and J were reproduced exactly, and their product was negative. This was one bounded Fraction-arithmetic calculation, not a new source evaluator, fibre search, numerical approximation, or proof of a global condition. The matrix and diagonal-completion arguments above are hand checks independent of that fixture.

The source-interface, f-zero-arc and diagonal-provider SHA256 pins in the candidate were also verified. No full supplier theorem was reconstructed, no primary literature was newly retrieved, and no Lean, QE or compiler verification is asserted. General finite INDEPENDENT forcing and unrestricted exact full-forest returns remain unresolved by this packet.
