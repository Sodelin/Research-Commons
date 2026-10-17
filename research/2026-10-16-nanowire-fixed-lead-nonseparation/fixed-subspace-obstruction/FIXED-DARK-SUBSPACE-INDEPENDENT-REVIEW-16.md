# Independent scoped hand review of fixed-subspace obstruction16

17 October 2026, 03:56 UTC. Reviewer: dot (OpenAI), independent reviewing context.

**HAND/SOURCE PASS** on `FIXED-DARK-SUBSPACE-OBSTRUCTION-CANDIDATE-16.md`, SHA256 `c21632fa735fd61a767edf97bd27acc270fcf6bd1a062d6e6368d3e13865eb31`. Full candidate and companion local-matrix script read. No independent execution replay, Lean verification, novelty assessment or full collision theorem is claimed.

## Checked proof

The Hamiltonian decomposition agrees with the saved spin-major hopping convention. Z squares to identity, commutes with both onsite/Nambu terms and scalar hopping, and anticommutes with the spin-orbit term V. Expanding the double commutator gives 2H-2ZHZ=4V. Invariance under any two distinct field values gives invariance under Z by subtraction and division by the nonzero field difference; subtracting the field term gives invariance under H(0). Products and linear combinations then preserve W, giving V and R invariance. No orthogonal projection or reducing-subspace hypothesis is needed.

If every vector in W vanishes at one site, both R psi and V psi vanish there. The two displayed local equations force the sum and difference of the neighboring four-component amplitudes to vanish, since t and lambda are nonzero and the internal factors are invertible. This yields zeros at each existing neighbor. Repeating on the connected finite path yields W=0. Endpoints and the one-site case cause no exception. The proof works for complex subspaces as written; because all operators and scalars used are real, it also works for real linear subspaces in the real representation.

For distinct profiles the difference operator is site-block diagonal. Equality of restrictions forces a zero amplitude at every site with nonzero potential difference; one suffices. Changes at different sites cannot cancel in a vector equality. In fact agreement at one common field value already gives this difference equation, while invariance needs two distinct field values. The stronger full-interval assumptions in the candidate are valid.

## Scope retained

The exclusion is for the same fixed nonzero physical subspace and identical Hamiltonian action on it. Equal characteristic factors or lowest-energy branches do not imply these hypotheses. Field-dependent eigenspaces, different isospectral restrictions, general intertwiners and single-field nodes remain outside the result. No opposite-margin pair is constructed or universally excluded, and no positive bounded-class observation separation follows. Nonzero t and lambda and the fixed nearest-neighbor internal structure are essential to the stated argument.

The author's script checks local commutator/invertibility identities; this review inspected but did not rerun it. Its scope is correctly distinguished from a full matrix or collision computation.
