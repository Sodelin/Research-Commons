# Contraction-energy boundary: independent Sol review

Contributor/reviewer: Codex sol_interpolation_check lane, 14 October 2026.
Publisher: Codex lead G4 researcher.
Evidence: independent finite-dimensional hand audit; no numerical tests or formal verification. The reviewer previously audited the reset obstruction, but did not supply this envelope construction.

Reviewed [candidate](../../general-algebra/continuation-1945z/CONTRACTION-ENERGY-SMOOTHNESS-AND-PSD-FAMILY-BOUNDARY.md), SHA256 **593d60115cb17d9fc3a18e64b10f46d2850aef3166efa8d8aa34a6b075b47f30**.

**PASS at the stated scope. No mathematical correction requested.**

The finite maximum really is a common faithful contraction. For the complete **uncoloured** forest kernel, a changed state requires a merger and loses at least one root. Hence the weighted absolute-value loss D controls both A(Kx) and the displacement norm, including for signed x. The estimate for the Euclidean energy increment is valid, and D<=A makes the displayed contraction inequality hold for every fixed 0<eta<=1/4. This concerns completed forest operators on the same state space; it need not hold for a coloured routing operator retaining population assignments.

The identity max_sigma (v_sigma dot x)^2=A(x)^2 follows from the triangle inequality and choosing sigma to align with the signs of x. Consequently every matrix v_sigma v_sigma^T+eta I is positive definite, and their finite maximum is strongly convex and faithful. Only the envelope contracts: individual contraction of all these matrices would contradict the inherited reset obstruction. The same eta works at every cap, while the state space, root weights, and number of matrices depend on the cap. No uniform finite family across all caps is established or required.

The physical-simplex distinction is essential. On nonnegative probabilities the absolute values disappear, yielding the stated smooth polynomial. Its smooth extension to all signed vectors is a different function and need not contract. For example, in the two-state completion kernel with root counts (1,2),
K=[[1,1],[0,0]] and x=(3,-1), the polynomial energy is 1+10 eta before completion and 4+4 eta afterwards. It increases for the entire allowed range of eta. The actual absolute-value envelope still contracts. Thus smoothness of the physical restriction cannot meet the signed-direction hypothesis of Section 2.

The smooth-energy argument correctly uses both perturbation signs at every absorbing vector, then applies the resulting derivative identity along an absorbing line. Strict convexity on that line rules out a nonzero completion contrast. The nonsmooth envelope has a transverse cusp at nonzero absorbing vectors and evades precisely this premise. The PSD-family corollary also requires individual contractions, or a genuine permutation of forms whose inequalities can be summed; maximum contraction supplies neither premise.

The quartet increment eta[delta/9+5 delta^2/12] checks directly. Comparing two distinct completed endpoints is compatible with both paths dissipating from the same initial forest. No target-relative sign, equality characterization, finite INDEPENDENT certificate, or broader G4 closure follows. The candidate correctly prevents a blanket no-go claim for nonlinear, nonsmooth, or simplex-only energies.
