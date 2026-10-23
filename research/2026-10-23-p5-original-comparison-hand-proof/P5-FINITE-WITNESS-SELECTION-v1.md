# A deterministic finite-witness selection rule

21 October 2026. Supplement to the SELF-REVIEWED candidate in
P5-STATIC-CLOCK-ANALYTIC-COUNTEREXAMPLE-v1.md. Its termination assertion
is conditional on that candidate proof surviving review. No search or
large-system evolution has been executed. This note makes the meaning of
its parameter maxima precise; it is not additional numerical evidence.

## The admitted family is fully specified

Fix positive COMPUTABLE gamma,tau and all other constants as in the
candidate; for example, gamma=1 and any positive rational tau inside the
stated small-parameter box. For q>=1 use N_q=2^(q+1)-1 data vertices and
the exact tree, clock lengths, local terms, three-qubit embeddings and
positive initial density rho_(N_q) given there.
The root observable is the SAME O=X1Y2X3 on three fixed labelled qubits.
The unrelated onsite Pauli term fixes the exact original h in every model.
The covariance in C5 specifies each root bath; all models have the same
Gamma,b0,j,x,beta and common bounds k,m,nu.

For each N, r_N=N^(-1/3) and m=ceil(N^(1/4)), restrict r to the FINITE
interpolation grid

    r_j=r_N/2+j r_N/(2m),  j=0,...,m.

The candidate's C12-C20 prove the large physical prediction for at least
one of these grid points. At each such r, allow u in[1,2], v in[-1,1],
and observation time s=t_N z with z in[0,1], exactly the fully noisy
physical family C5-C6. For fixed N all these predictions are continuous
functions of u,v,z. They are defined by the original FULL filters and the
SAME static Hamiltonian H_r throughout the evolution.

Thus their supremum over u,v,z is a maximum on a compact set. A classical
selection rule can choose the lexicographically least maximizing tuple
from its compact maximizing set. The finite interpolation grid also makes
the r selection deterministic. This already specifies an exact sequence
of finite systems by ordinary real-variable definitions.

## A computable search rule with a certified stopping condition

An alternative avoids comparing exactly equal maxima. For an integer
target B>=2, enumerate tuples

    (q,j,a,b,c,precision),

where j is on the finite r grid, a,c are rationals in[0,1], b is rational
in[-1,1], u=1+a, v=b and s=t_N c. Dovetail the enumeration and interval
precision refinements, so every fixed tuple receives arbitrarily precise
evaluation. Stop on the first certified interval for the ORIGINAL
prediction whose absolute value is strictly greater than B.

Every ingredient is a computable finite-dimensional expression: clock
couplings contain finite rational operations and square roots, the local
encoding is algebraic in the fixed y, Gaussian constants and the initial
weight kappa(t_N) are computable, and all matrix exponentials have explicit
finite norm bounds. Infinite physical filters can be evaluated by a
certified finite integration plus their common Gamma exp(-s/tau)/tau
envelope tail. The delayed pulse is retained inside that finite integration
until its actual tail bound licenses truncation. Exact formulas specify
the physical density; an interval evaluation does not replace it by an
uncertified rounded state.

Conditional on C1, sufficiently large N have a physical prediction above
B with a strict margin. Continuity makes the same inequality hold at a
nearby rational u,v,z tuple, including rational endpoints when relevant.
Certified interval refinement therefore eventually detects such a tuple.
The dovetailed search terminates and returns a finite admitted witness.
To produce an increasing-volume sequence for B=2,3,..., restrict each next
search to q larger than the preceding returned value. C1 holds at all
sufficiently large balanced-tree sizes, so termination is preserved.

This is an algorithmic specification of witnesses for the parameter-uniform
finite-model statement in P5-SCOPE.md. The root covariance is specified
for each selected model by C5, with all original common parameters fixed.
Each returned positive initial density and static generator is admitted;
the auxiliary root strength zero, complex parameters and cut filters are
proof tools outside this search space.

The proof supplies existence and eventual termination, without a practical
runtime claim. Full proof acceptance remains governed by the supplier
audits in P5-CANDIDATE-REVIEW-LEDGER.md.
