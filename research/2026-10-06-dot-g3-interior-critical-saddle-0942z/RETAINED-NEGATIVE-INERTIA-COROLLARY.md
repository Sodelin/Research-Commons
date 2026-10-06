# Retained negative inertia is at most three on a nonattained rank-five branch

Contributor: GPT-6 Astra research lane, 6 October2026,09:43UTC. The independent Astra review lane also identified and sent the same dimension argument. This is a short consequence of the accepted second-order critical filter, not an additional recognition theorem. Hand review pending.

Assume exactly the hypotheses of SECOND-ORDER-CRITICAL-EXCLUSION.md: a finite fresh COMMON cap-seven closure presentation with positive drift a and positive residue intensity u, paired critical retained factors, the fixed oriented normal c, and a rank-five presentation derivative J. For each retained factor let nu_i be the number of strictly negative eigenvalues, with multiplicity, of the real symmetric2x2 Hessian Hess(c.H)(p_i,q_i).

Then any nonattained presentation must satisfy

    sum_i nu_i <= 3.

Proof. Let E_i be the strictly negative eigenspace of the i-th Hessian and E their direct sum. On E the sum of the retained quadratic forms is negative definite. Set the residue-node variation delta r to zero. Since J has image c-perp, of dimension5, and contains the independent columns Lambda and D(r), the quotient

    image(J)/span{Lambda,D(r)}

has dimension3. The derivative map from E into this quotient has a nonzero kernel if dim(E)>3. Choose such a nonzero retained variation. Its derivative lies in span{Lambda,D(r)}, so it can be cancelled by choices of delta a and delta u. These are legal two-sided infinitesimal variations because a,u>0. The resulting full variation lies in ker J and has strictly negative normal quadratic form: delta r=0 eliminates the residue-node term, while delta a and delta u make no quadratic contribution. The accepted second-order filter then puts the target in actual source interior, contradicting nonattainment. QED.

The conclusion counts negative inertia, not all retained factors. Factors with positive-semidefinite Hessian are not bounded by this argument, and rank below5 is not covered. Three or fewer negative directions do not prove NO. Distinct critical types, multiplicities and an existing algebraic tuple census still require their own source-consistent treatment. This local filter does not decide the residual exponential equations or original joint/all-core G3.

No numerical execution, root census or formal verification is used. Historical novelty of the general linear-algebra principle is not claimed.
